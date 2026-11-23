#!/usr/bin/env bash
# Tier 1: scripts/score measures source metrics (spec_lines, proof_lines, code_lines, trusted_native_lines)
# deterministically against a fixture library of known counts, and catches a miscounted fixture (negative case).
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh
sc=$(pwd)/scripts/score
fail() { echo "tier1: score: $*" >&2; exit 1; }

T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t

# Build a fixture library with known line counts:
#   spec/Spec.lean: 3 lines
#   Demo.lean: 2 lines, Demo/Core.lean: 4 lines (code_lines = 6)
#   DemoProofs.lean: 1 line, DemoProofs/Lemmas.lean: 5 lines (proof_lines = 6)
#   abi/shim.c: 7 lines (trusted_native_lines = 7)
#   Excluded: lakefile.lean (2 lines), vectors/Main.lean (3 lines), tests/test.c (4 lines)
F="$T/lib/vbm-demo"
mkdir -p "$F/spec" "$F/Demo" "$F/DemoProofs" "$F/abi" "$F/vectors" "$F/tests"
printf 'a\nb\nc\n' > "$F/spec/Spec.lean"
printf 'x\ny\n' > "$F/Demo.lean"
printf 'c1\nc2\nc3\nc4\n' > "$F/Demo/Core.lean"
printf 'p0\n' > "$F/DemoProofs.lean"
printf 'p1\np2\np3\np4\np5\n' > "$F/DemoProofs/Lemmas.lean"
printf 'n1\nn2\nn3\nn4\nn5\nn6\nn7\n' > "$F/abi/shim.c"
printf 'l1\nl2\n' > "$F/lakefile.lean"
printf 'v1\nv2\nv3\n' > "$F/vectors/Main.lean"
printf 't1\nt2\nt3\nt4\n' > "$F/tests/test.c"
git -C "$T" init -q
git -C "$T" add -A
git -C "$T" commit -qm "feat(demo): fixture"
sha=$(git -C "$T" rev-parse HEAD)
ver=$(tr -d '[:space:]' < VERSION)

check_counts() {
  python3 -c '
import sys, tomllib
d = tomllib.loads(sys.stdin.read())
s, p = d["scores"], d["scores"]["provenance"]
want = {"spec_lines": int(sys.argv[1]), "proof_lines": int(sys.argv[2]),
        "code_lines": int(sys.argv[3]), "trusted_native_lines": int(sys.argv[4])}
for k, v in want.items():
    assert s[k] == v, f"{k}: got {s[k]}, want {v}"
assert p["commit"] == sys.argv[5], f"commit: {p} != {sys.argv[5]}"
assert p["tool_version"] == sys.argv[6], f"tool_version: {p} != {sys.argv[6]}"
' "$1" "$2" "$3" "$4" "$5" "$6"
}

out1=$("$sc" "$F")
out2=$("$sc" "$F")
[ "$out1" = "$out2" ] && ran_case || fail "output is not deterministic"
printf '%s\n' "$out1" | check_counts 3 6 6 7 "$sha" "$ver" && ran_case || fail "fixture counts mismatch: $out1"

# Negative case: a fixture with altered counts must NOT match the baseline counts (catches hardcoded/miscounted output).
printf 'extra\n' >> "$F/abi/shim.c"
git -C "$T" commit -qam "feat(demo): add native line"
sha2=$(git -C "$T" rev-parse HEAD)
out3=$("$sc" "$F")
must_fail "miscounted fixture caught" bash -c 'printf "%s\n" "$1" | python3 -c "import sys, tomllib; d = tomllib.loads(sys.stdin.read()); n = d.get(\"scores\", {}).get(\"trusted_native_lines\"); assert n == 7, f\"got {n}, expected mismatch with 7\""' _ "$out3"
printf '%s\n' "$out3" | check_counts 3 6 6 8 "$sha2" "$ver" && ran_case || fail "updated fixture counts mismatch"

# Negative case: symlinked source file must not be counted.
ln -s /etc/hosts "$F/Demo/Symlink.lean"
git -C "$T" add -A && git -C "$T" commit -qm "feat(demo): symlink"
out4=$("$sc" "$F")
printf '%s\n' "$out4" | check_counts 3 6 6 8 "$(git -C "$T" rev-parse HEAD)" "$ver" && ran_case || fail "symlinked file was counted"

# Negative case: missing directory exits 2.
must_fail "missing directory rejected" "$sc" "$T/nonexistent"

ran_done test_score
echo "tier1: score: source metrics deterministic and exact on fixture, miscounted fixture and symlinks caught: ok"
