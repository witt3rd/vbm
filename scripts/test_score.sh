#!/usr/bin/env bash
# Tier 1: scripts/score measures source, proof and trust metrics deterministically against fixture libraries,
# omits unmeasurable metrics instead of inventing them, and catches negative cases for each metric.
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

# Negative case: absent trust-ledger, ledger module, and ClosureGate must omit those fields (never invent 0).
python3 -c '
import sys, tomllib
s = tomllib.loads(sys.stdin.read())["scores"]
assert s["unproved_escapes"] == 0, s
for absent in ("generated_share_pct", "proved_claims", "total_claims", "trust_ledger_entries"):
    assert absent not in s, f"invented {absent}: {s}"
' <<< "$out4" && ran_case || fail "invented unmeasurable fields"

# Negative case (unproved_escapes): comments and strings mentioning escape words are NOT counted; planted ones ARE counted.
cat > "$F/Demo/Core.lean" <<'LEAN'
-- sorry admit axiom unsafe implemented_by csimp
/- nested /- sorry -/ axiom -/
def msg : String := "sorry axiom unsafe"
LEAN
git -C "$T" commit -qam "feat(demo): comments and strings"
out_comment=$("$sc" "$F")
python3 -c '
import sys, tomllib
s = tomllib.loads(sys.stdin.read())["scores"]
assert s["unproved_escapes"] == 0, f"comment/string counted as escape: {s}"
' <<< "$out_comment" && ran_case || fail "comment or string counted as unproved_escapes"

printf 'theorem bad : False := by sorry\n' >> "$F/Demo/Core.lean"
git -C "$T" commit -qam "feat(demo): plant sorry"
out_sorry=$("$sc" "$F")
python3 -c '
import sys, tomllib
s = tomllib.loads(sys.stdin.read())["scores"]
assert s["unproved_escapes"] == 1, f"planted sorry not counted: {s}"
' <<< "$out_sorry" && ran_case || fail "planted sorry not counted"

printf 'unsafe def u : Nat := 0\n' >> "$F/Demo/Core.lean"
git -C "$T" commit -qam "feat(demo): plant unsafe"
out_unsafe=$("$sc" "$F")
python3 -c '
import sys, tomllib
s = tomllib.loads(sys.stdin.read())["scores"]
assert s["unproved_escapes"] == 2, f"planted unsafe not counted: {s}"
' <<< "$out_unsafe" && ran_case || fail "planted unsafe not counted"

# Negative case (trust_ledger_entries): uses trust_ledger.py parser; decoys ignored; removing an entry drops count.
mkdir -p "$F/docs"
cat > "$F/docs/trust-ledger.md" <<'MD'
# Trust ledger
## ### T99. Not a level-3 header
### Note. Not a T-entry
### T1. First entry
- **What:** first item
### T2. Second entry
- **What:** second item
MD
git -C "$T" add -A && git -C "$T" commit -qm "feat(demo): trust ledger"
out_tl=$("$sc" "$F")
python3 -c '
import sys, tomllib
s = tomllib.loads(sys.stdin.read())["scores"]
assert s["trust_ledger_entries"] == 2, f"trust_ledger_entries: {s}"
' <<< "$out_tl" && ran_case || fail "trust_ledger_entries mismatch"

cat > "$F/docs/trust-ledger.md" <<'MD'
# Trust ledger
### T1. First entry
- **What:** first item
MD
git -C "$T" commit -qam "feat(demo): drop trust entry"
out_tl2=$("$sc" "$F")
python3 -c '
import sys, tomllib
s = tomllib.loads(sys.stdin.read())["scores"]
assert s["trust_ledger_entries"] == 1, f"trust_ledger_entries after drop: {s}"
' <<< "$out_tl2" && ran_case || fail "trust_ledger_entries did not drop"

# Negative case (proved_claims, total_claims): fake docs/proof-ledger.md without Ledger module must NOT be parsed.
printf '# Obligation ledger\n\n**99 proved, 0 partial, 0 open, 0 limit, of 99.**\n' > "$F/docs/proof-ledger.md"
git -C "$T" add -A && git -C "$T" commit -qm "feat(demo): decoy proof-ledger.md"
out_decoy=$("$sc" "$F")
python3 -c '
import sys, tomllib
s = tomllib.loads(sys.stdin.read())["scores"]
assert "proved_claims" not in s and "total_claims" not in s, f"parsed fake markdown: {s}"
' <<< "$out_decoy" && ran_case || fail "parsed rendered docs/proof-ledger.md instead of typed Ledger"

# Typed obligation ledger + axiom audit on a real Lean fixture (when lake is available):
# ignores contradicting docs/proof-ledger.md and reads typed DemoProofs.Ledger via land-lean ledger.
if command -v lake >/dev/null 2>&1; then
  L="$T/lean-demo"
  mkdir -p "$L/.land" "$L/DemoProofs" "$L/docs"
  cp lib/vbm-rng/lean-toolchain "$L/lean-toolchain"
  cat > "$L/lakefile.lean" <<LAKE
import Lake
open Lake DSL
package "vbm-lean-demo" where
  leanOptions := #[]
require "land-ledger" from "$(pwd)/.land/tool/lean"
lean_lib DemoProofs
LAKE
  printf 'import DemoProofs.Ledger\n' > "$L/DemoProofs.lean"
  cat > "$L/DemoProofs/Ledger.lean" <<'LEAN'
import LandLedger
open Land.Ledger
theorem t1 : True := trivial
def ledger : List Obligation := [
  O "c1" (.proved [`t1]),
  O "c2" (.open_ "todo"),
]
LEAN
  cat > "$L/.land/lean.conf" <<'CONF'
LAND_LEAN_AXIOM_IMPORTS="DemoProofs"
LAND_LEAN_AXIOM_ROOTS="DemoProofs"
LAND_LEAN_LEDGER_MODULE="DemoProofs.Ledger"
CONF
  printf '# Obligation ledger\n\n**99 proved, 0 partial, 0 open, 0 limit, of 99.**\n' > "$L/docs/proof-ledger.md"
  git -C "$L" init -q && git -C "$L" add -A && git -C "$L" commit -qm "feat(lean-demo): typed ledger"
  (cd "$L" && lake build DemoProofs LandLedger >/dev/null 2>&1)
  out_lean=$("$sc" "$L")
  python3 -c '
import sys, tomllib
s = tomllib.loads(sys.stdin.read())["scores"]
assert s["proved_claims"] == 1 and s["total_claims"] == 2, f"typed ledger mismatch: {s}"
assert s["unproved_escapes"] == 0, f"clean lean fixture had escapes: {s}"
' <<< "$out_lean" && ran_case || fail "typed ledger mismatch: $out_lean"

  # Negative case: planting a non-standard axiom is caught by both typed axiom audit and token scan.
  cat > "$L/DemoProofs/Ledger.lean" <<'LEAN'
import LandLedger
open Land.Ledger
axiom badAx : False
theorem t1 : False := badAx
def ledger : List Obligation := [
  O "c1" (.proved [`t1]),
]
LEAN
  git -C "$L" commit -qam "feat(lean-demo): plant axiom"
  (cd "$L" && lake build DemoProofs LandLedger >/dev/null 2>&1)
  out_ax=$("$sc" "$L")
  python3 -c '
import sys, tomllib
s = tomllib.loads(sys.stdin.read())["scores"]
assert s["unproved_escapes"] >= 1, f"planted axiom not caught: {s}"
assert s["proved_claims"] == 1 and s["total_claims"] == 1, f"updated typed ledger mismatch: {s}"
' <<< "$out_ax" && ran_case || fail "planted axiom not caught: $out_ax"
fi

# Negative case: missing directory exits 2.
must_fail "missing directory rejected" "$sc" "$T/nonexistent"

ran_done test_score
echo "tier1: score: source, proof and trust metrics deterministic and exact, negative cases caught: ok"
