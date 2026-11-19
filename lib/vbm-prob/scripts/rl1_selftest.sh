#!/usr/bin/env bash
# Tier 1: the RL1 scan (scripts/scan_rl1.sh) passes on the whole library AND is shown able to fail: a file with `Float`, a structure with the fields `num` and `den`
# (also when they are declared on one line each after other fields, and in a nested directory) are each flagged; a clean tree, a structure with only one of the two
# fields and a field named like one (`numer`) pass.
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case counts each executed check, ran_done prints `ran: NAME: N cases`
scan=$(pwd)/scripts/scan_rl1.sh
fail() { echo "tier1: rl1: $*" >&2; exit 1; }
"$scan" >/dev/null 2>&1 && ran_case || fail "the library breaks RL1"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/VbmProb/Sub"
printf 'import VbmProb.Core\nstructure Ok where\n  num : Nat\n  other : Nat\n\ndef f : Nat := 1\n' > "$T/VbmProb/A.lean"
printf 'structure Numer where\n  numer : Int\n  denom : Nat\n' > "$T/VbmProb/B.lean"
printf 'structure P where\n  num : Nat\n\nstructure Q where\n  den : Nat\n' > "$T/VbmProb/C.lean"
: > "$T/VbmProb.lean"
"$scan" "$T" >/dev/null 2>&1 && ran_case || fail "a clean fixture tree was flagged"
chk() { "$scan" "$T" > "$T/out" 2>&1 && fail "negative self-test: $1 was NOT flagged"; grep -q "$2" "$T/out" && ran_case || fail "negative self-test: $1: wrong finding: $(cat "$T/out")"; }
printf 'def x : Float := 1.5\n' > "$T/VbmProb/Sub/F.lean"; chk "a Float" "Sub/F.lean:1: Float"; rm "$T/VbmProb/Sub/F.lean"
printf -- '-- a comment about Float\n' > "$T/VbmProb/Sub/F.lean"; chk "a Float in a comment" "Sub/F.lean:1: Float"; rm "$T/VbmProb/Sub/F.lean"
printf 'structure Ratio where\n  num : Int\n  den : Nat\n' > "$T/VbmProb/Sub/R.lean"; chk "a ratio structure" "Sub/R.lean:1: a structure with fields num and den"; rm "$T/VbmProb/Sub/R.lean"
printf 'structure Ratio where\n  den : Nat\n  pos : 0 < den\n  num : Int\n  deriving Repr\n' > "$T/VbmProb/Sub/R.lean"; chk "a ratio structure with other fields" "Sub/R.lean:1: a structure with fields num and den"; rm "$T/VbmProb/Sub/R.lean"
printf 'def x : Float := 1\n' > "$T/VbmProb.lean"; chk "a Float in the root module" "VbmProb.lean:1: Float"
ran_done rl1_selftest
echo "tier1: rl1: the library has no Float and no second ratio, and the scan flags both: ok"
