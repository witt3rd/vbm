#!/usr/bin/env bash
# Tier 1: the host-side check of vendored libraries (scorecard/scorecard_pins.py, DECISIONS 21) can FAIL. A real scratch git repository is the "remote" and its tag is really signed (a throwaway key; no mock of git or of the
# signature); the expected tree hash is a RECORDED value computed independently of the tool (Python, over the same three files). A subject that vendors the release exactly passes and its provenance is returned; an edited vendored
# file, a self-consistent doctoring (the file AND the lock hash changed), a lock whose commit is not the tag's, an unsigned tag, a tag signed by a key the SCORER does not trust, an unlocked library, a URL outside the allowlist,
# the retired lock, a git package in the manifest and a malformed lock each REFUSE with their reason; a subject that vendors nothing provisions nothing.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh
fail() { echo "tier1: pins: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_TERMINAL_PROMPT=0 GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
HASH=07ef6be10fa40b8a4de202ee52dee89700fbdb0ebef6b9478a424b9583d65c3e   # recorded: the tree hash of the three files below, computed with Python, not with the tool under test
ssh-keygen -q -t ed25519 -N '' -f "$T/maint" -C maint; ssh-keygen -q -t ed25519 -N '' -f "$T/rogue" -C rogue
echo "maint $(cut -d' ' -f1,2 "$T/maint.pub")" > "$T/signers"
mkdir -p "$T/remote/LibA"; ( cd "$T/remote" && git init -q -b main && git config commit.gpgsign false && printf 'def a := 1\n' > LibA/A.lean && printf 'import LibA.A\n' > LibA.lean && printf 'leanprover/lean4:v4.35.0\n' > lean-toolchain && git add -A && git commit -qm one )
REV=$(git -C "$T/remote" rev-parse HEAD)
tag() { local n=$1 k=$2; if [ "$k" = none ]; then git -C "$T/remote" -c tag.gpgsign=false tag -a "$n" -m "libx $n" -m "tree_sha256=$HASH"; else git -C "$T/remote" -c gpg.format=ssh -c "user.signingkey=$T/$k" tag -s "$n" -m "libx $n" -m "tree_sha256=$HASH"; fi; }
tag v1.0.0 maint; tag v1.0.1 none; tag v1.0.2 rogue
mk() {   # mk NAME [tag] [lock rev] [lock hash] [url]: a subject tree that vendors libx exactly as the release has it
  local d=$T/$1; rm -rf "$d"; mkdir -p "$d/.land" "$d/vendor/libx"; git -C "$T/remote" archive "${2:-v1.0.0}" | tar -x -C "$d/vendor/libx"
  printf '{"version":"1.3.0","packagesDir":".lake/packages","packages":[{"type":"path","name":"«libx»","dir":"vendor/libx"}],"name":"x"}\n' > "$d/lake-manifest.json"
  printf 'libx %s %s %s %s\n' "${5:-$T/remote}" "${2:-v1.0.0}" "${3:-$REV}" "${4:-$HASH}" > "$d/.land/pins.lock"
}
run() { python3 - "$1" "${2:-local}" "$T/signers" <<'PY'
import sys
sys.path.insert(0, "scorecard"); import scorecard_pins
env = {"PATH": "/usr/bin:/bin", "HOME": "/tmp", "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_CONFIG_SYSTEM": "/dev/null", "GIT_TERMINAL_PROMPT": "0"}
try: print("OK", scorecard_pins.provision(sys.argv[1], env, allow_local=(sys.argv[2] == "local"), signers=sys.argv[3]))
except ValueError as x: print("REFUSED", x); sys.exit(1)
PY
}
want() { local n=$1 re=$2; if run "$T/$n" ${3:-} > "$T/o" 2>&1; then fail "$n was accepted (a check that cannot fail)"; fi; grep -Eq -- "$re" "$T/o" && ran_case || fail "$n refused for another reason: $(cat "$T/o")"; }
mk ok; run "$T/ok" > "$T/o" 2>&1 && grep -q "'tag': 'v1.0.0'" "$T/o" && grep -q "'tree_sha256': '$HASH'" "$T/o" && grep -q "'rev': '$REV'" "$T/o" && ran_case || fail "a vendored release that is exactly the published one was refused or lost its provenance: $(cat "$T/o")"
mk edited; echo "def a := 2" > "$T/edited/vendor/libx/LibA/A.lean"; want edited "not exactly their lock"
mk doctored; echo "def a := 2" > "$T/doctored/vendor/libx/LibA/A.lean"; NEW=$(.land/tool/bin/land-pin tree "$T/doctored/vendor/libx"); sed -i "s/$HASH/$NEW/" "$T/doctored/.land/pins.lock"; want doctored "does not match the published release"
mk wrongrev v1.0.0 0123456789012345678901234567890123456789; want wrongrev "does not match the published release"
mk unsigned v1.0.1; want unsigned "is not accepted.*(does not verify|not signed)"
mk rogue v1.0.2; want rogue "is not accepted.*(does not verify|not signed)"
mk unlocked; mkdir -p "$T/unlocked/vendor/liby"; echo y > "$T/unlocked/vendor/liby/f"; want unlocked "not exactly their lock"
mk url; want url "allowlisted" nonlocal
mk https v1.0.0 "$REV" "$HASH" https://example.org/evil/libx; want https "allowlisted" nonlocal
mk oldlock; mkdir -p "$T/oldlock/scripts"; echo "libx $REV $HASH LibA LibA/" > "$T/oldlock/scripts/pinned-libs.lock"; want oldlock "retired lock"
mk gitpkg; sed -i 's/"type":"path"/"type":"git"/' "$T/gitpkg/lake-manifest.json"; want gitpkg "a git package"
mk short; echo "libx $T/remote v1.0.0 $REV" > "$T/short/.land/pins.lock"; want short "5 fields"
mkdir -p "$T/none"; run "$T/none" > "$T/o" 2>&1 && grep -q 'OK \[\]' "$T/o" && ran_case || fail "a subject that vendors nothing provisions something: $(cat "$T/o")"
( cd "$T/remote" && printf 'def a := 3\n' > LibA/A.lean && git commit -qam two ); mk later; run "$T/later" > "$T/o" 2>&1 && ran_case || fail "a later commit on the remote broke a pin of an older, tagged release: $(cat "$T/o")"
ran_done test_pins
echo "tier1: pins: a vendored library is checked offline against its lock and against the signed release it names; an edit, a self-consistent doctoring, a wrong commit, an unsigned or untrusted tag, an unlocked library, a URL outside the allowlist, the retired lock, a git package and a loose lock each refuse: ok"
