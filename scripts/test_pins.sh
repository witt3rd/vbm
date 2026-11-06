#!/usr/bin/env bash
# Tier 1: the host-side provisioning of pinned libraries (scorecard/scorecard_pins.py, design note D5) can FAIL. A real scratch git repository is the "remote" (no mock of git); the expected spec_hash is a RECORDED value
# computed by the subject-side tool (scripts/pinned-lib.py of the sibling libraries) over the same three files, not by the code under test. A matching pin is fetched at the LOCK's rev into <tree>/.lake/packages and verified;
# a manifest rev that is not the lock's, a remote that was edited after the pin (hash), a remote that lacks the locked rev, a URL outside the allowlist (the https-only rule is on unless the fixture flag is given),
# an already-present checkout, a malformed lock and a lock path that escapes each REFUSE with their reason; a subject with no lock provisions nothing.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh
. scripts/git-hermetic.sh 2>/dev/null || true
fail() { echo "tier1: pins: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
HASH=07ef6be10fa40b8a4de202ee52dee89700fbdb0ebef6b9478a424b9583d65c3e   # recorded: pinned-lib.py hash over LibA/, LibA.lean, lean-toolchain with the contents below
mkdir -p "$T/remote/LibA"; ( cd "$T/remote" && git init -q -b main && git config user.email t@t && git config user.name t && printf 'def a := 1\n' > LibA/A.lean && printf 'import LibA.A\n' > LibA.lean && printf 'leanprover/lean4:v4.35.0\n' > lean-toolchain && git add -A && git commit -q -m one )
REV=$(git -C "$T/remote" rev-parse HEAD)
mk() {   # mk NAME [manifest rev] [lock rev] [lock hash] [url]: a subject tree with a lock and a manifest
  local d=$T/$1; rm -rf "$d"; mkdir -p "$d/scripts"
  printf '{"version":"1.3.0","packagesDir":".lake/packages","packages":[{"type":"git","name":"«libx»","url":"%s","rev":"%s","inputRev":"main"}],"name":"x"}\n' "${5:-$T/remote}" "${2:-$REV}" > "$d/lake-manifest.json"
  printf 'libx %s %s LibA LibA/,LibA.lean,lean-toolchain\n' "${3:-$REV}" "${4:-$HASH}" > "$d/scripts/pinned-libs.lock"
}
run() { python3 - "$1" "${2:-local}" <<'PY'
import sys, os, subprocess
sys.path.insert(0, "scorecard"); import scorecard_pins
env = {"PATH": "/usr/bin:/bin", "HOME": "/tmp", "GIT_CONFIG_GLOBAL": "/dev/null", "GIT_CONFIG_SYSTEM": "/dev/null", "GIT_TERMINAL_PROMPT": "0"}
try: print("OK", scorecard_pins.provision(sys.argv[1], env, allow_local=(sys.argv[2] == "local")))
except ValueError as x: print("REFUSED", x); sys.exit(1)
PY
}
mk ok; run "$T/ok" > "$T/o" 2>&1 && ran_case || fail "a matching pin is refused: $(cat "$T/o")"
[ "$(git -C "$T/ok/.lake/packages/libx" rev-parse HEAD)" = "$REV" ] && ran_case || fail "the checkout is not at the locked rev"
want() { local n=$1 re=$2; shift 2; mk "$n" "$@"; if run "$T/$n" > "$T/o" 2>&1; then fail "$n was accepted (a check that cannot fail)"; fi; grep -Eq -- "$re" "$T/o" && ran_case || fail "$n refused for another reason: $(cat "$T/o")"; [ ! -e "$T/$n/.lake/packages/libx" ] && ran_case || fail "$n left a checkout behind"; }
want stale 'stale rev' 0123456789012345678901234567890123456789
want hash 'spec_hash' "$REV" "$REV" 0000000000000000000000000000000000000000000000000000000000000000
want norev 'failed' 0123456789012345678901234567890123456789 0123456789012345678901234567890123456789
mk url; if run "$T/url" nonlocal > "$T/o" 2>&1; then fail "a local URL was accepted without the fixture flag"; fi; grep -q 'allowlisted' "$T/o" && ran_case || fail "the https-only rule did not say why: $(cat "$T/o")"
mk https "$REV" "$REV" "$HASH" https://example.org/evil/libx; if run "$T/https" nonlocal > "$T/o" 2>&1; then fail "a non-GitHub URL was accepted"; fi; grep -q 'allowlisted' "$T/o" && ran_case || fail "the allowlist refusal did not say why"
mk twice; mkdir -p "$T/twice/.lake/packages/libx"; if run "$T/twice" > "$T/o" 2>&1; then fail "an already-present checkout was accepted"; fi; grep -q 'already' "$T/o" && ran_case || fail "the present-checkout refusal did not say why"
mk short; sed -i 's/^libx [0-9a-f]* /libx main /' "$T/short/scripts/pinned-libs.lock"; if run "$T/short" > "$T/o" 2>&1; then fail "a branch name in the lock was accepted"; fi; grep -q 'bad name, rev' "$T/o" && ran_case || fail "the lock was not read strictly"
mk esc; sed -i 's#LibA/,LibA.lean#../x,LibA.lean#' "$T/esc/scripts/pinned-libs.lock"; if run "$T/esc" > "$T/o" 2>&1; then fail "a lock path that escapes was accepted"; fi; grep -q 'unsafe' "$T/o" && ran_case || fail "the unsafe path was not refused"
mkdir -p "$T/none"; run "$T/none" > "$T/o" 2>&1 && grep -q 'OK \[\]' "$T/o" && ran_case || fail "a subject with no lock provisions something: $(cat "$T/o")"
# the remote is edited AFTER the pin: a new commit at the same URL with the locked rev still reachable is fine (the lock's rev is fetched, not the head), an edited ROOT of history is not reachable by rev
( cd "$T/remote" && printf 'def a := 2\n' > LibA/A.lean && git commit -qam two ); mk later; run "$T/later" > "$T/o" 2>&1 && ran_case || fail "a moved remote head broke a pin of an older rev: $(cat "$T/o")"
[ "$(git -C "$T/later/.lake/packages/libx" rev-parse HEAD)" = "$REV" ] && ran_case || fail "the later checkout is not at the locked rev"
ran_done test_pins
echo "tier1: pins: a pin is fetched host-side at the lock's rev and verified; stale rev, wrong hash, missing rev, URL outside the allowlist, present checkout, loose lock and escaping path each refuse: ok"
