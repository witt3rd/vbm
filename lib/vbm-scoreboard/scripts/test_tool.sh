#!/usr/bin/env bash
# Tier 1: a known-answer test of the PRODUCT BINARY `vbm-scoreboard` at its process boundary: a throwaway directory, a fake provider script and files; the six subcommands, their exit codes and exact
# messages; and the refusals (a regression, an unmeasured metric, a failing, malformed, repeating or endless provider, a refused reset, a bad file). The binary is built by tier1.sh (`lake build vbm-scoreboard`).
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. ../../.land/tool/lib/ran.sh
bin=$(pwd)/.lake/build/bin/vbm-scoreboard
[ -x "$bin" ] || { echo "test_tool: $bin is not built (lake build vbm-scoreboard)" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
cd "$T"
fail() { echo "test_tool: $*" >&2; exit 1; }
# run CMD...: sets $rc, $out (stdout), $err (stderr)
run() { rc=0; "$bin" "$@" > "$T/o" 2> "$T/e" || rc=$?; out=$(cat "$T/o"); err=$(cat "$T/e"); }
expect() { # expect NAME RC OUT ERR: exact
  [ "$rc" = "$2" ] || fail "$1: exit $rc, wanted $2 (out: $out; err: $err)"
  [ "$out" = "$3" ] || fail "$1: stdout was [$out], wanted [$3]"
  [ "$err" = "$4" ] || fail "$1: stderr was [$err], wanted [$4]"
  ran_case
}
cat > provider.sh <<'E'
#!/bin/sh
cat readings.txt
E
chmod +x provider.sh
P='sh provider.sh'
reads() { printf '%s\n' "$@" > readings.txt; }
r() { printf '{"v":1,"metric":"%s","value":%s,"unit":"count"}' "$1" "$2"; }
cat > baseline.jsonl <<'E'
{"v":1,"metric":"covered","direction":"higher","floor":80}
{"v":1,"metric":"warnings","direction":"lower","floor":5}
E
: > history.jsonl

# check: equal readings pass; better readings pass
reads "$(r covered 80)" "$(r warnings 5)"
run check --provider "$P" --baseline baseline.jsonl
expect "check equal" 0 "scoreboard: ok: 2 floors held" ""
reads "$(r covered 90)" "$(r warnings 1)"
run check --provider "$P" --baseline baseline.jsonl
expect "check better" 0 "scoreboard: ok: 2 floors held" ""
# check: a regression names the metric, the floor and the reading, and exits 1
reads "$(r covered 79)" "$(r warnings 5)"
run check --provider "$P" --baseline baseline.jsonl
expect "check regression" 1 "" "scoreboard: regressed: covered: reading 79 is worse than floor 80 (higher is better)"
reads "$(r covered 80)" "$(r warnings 6)"
run check --provider "$P" --baseline baseline.jsonl
expect "check regression lower" 1 "" "scoreboard: regressed: warnings: reading 6 is worse than floor 5 (lower is better)"
# check: an omitted baselined metric fails closed
reads "$(r covered 80)"
run check --provider "$P" --baseline baseline.jsonl
expect "check unmeasured" 1 "" "scoreboard: unmeasured: warnings: no reading (a floor with no reading fails)"
# a reading for a metric with no floor is not a refusal
reads "$(r covered 80)" "$(r warnings 5)" "$(r extra 1)"
run check --provider "$P" --baseline baseline.jsonl
expect "check extra reading" 0 "scoreboard: ok: 2 floors held" ""

# the provider's refusals are typed, exit 3
reads "$(r covered 80)" "not json"
run check --provider "$P" --baseline baseline.jsonl
[ "$rc" = 3 ] && [ -z "$out" ] && [[ "$err" == "scoreboard: provider output refused: line 2: not JSON ("* ]] && ran_case || fail "malformed line: $rc $err"
reads "$(r covered 80)" '{"v":1,"metric":"warnings","value":"x"}'
run check --provider "$P" --baseline baseline.jsonl
expect "wrong type" 3 "" "scoreboard: provider output refused: line 2: wrong type for key value"
reads "$(r covered 80)" "$(r covered 81)" "$(r warnings 5)"
run check --provider "$P" --baseline baseline.jsonl
expect "repeated metric" 3 "" "scoreboard: provider output refused: line 2: metric covered repeated"
reads '{"v":2,"metric":"covered","value":1}'
run check --provider "$P" --baseline baseline.jsonl
expect "unknown version" 3 "" "scoreboard: provider output refused: line 1: unknown version 2"
run check --provider "sh -c 'exit 7'" --baseline baseline.jsonl
expect "provider exit" 3 "" "scoreboard: provider failed: exit code 7"
reads "$(r covered 80)" "$(r warnings 5)"
run check --provider "cat readings.txt; exit 2" --baseline baseline.jsonl
expect "provider exit with output" 3 "" "scoreboard: provider failed: exit code 2"
run check --provider "sleep 30" --baseline baseline.jsonl --timeout 1
expect "provider timeout" 3 "" "scoreboard: provider stopped: still running after 1 seconds"
s=$SECONDS
run check --provider "sleep 30 & sleep 30" --baseline baseline.jsonl --timeout 1
expect "provider timeout, grandchild" 3 "" "scoreboard: provider stopped: still running after 1 seconds"
[ $((SECONDS - s)) -lt 10 ] || fail "a stopped provider held the caller"

# show
reads "$(r covered 83)"
run show --provider "$P" --baseline baseline.jsonl
expect "show" 0 "metric    direction  floor     reading
covered   higher     80        83
warnings  lower      5         -" ""

# files
run check --provider "$P" --baseline missing.jsonl
[ "$rc" = 4 ] && grep -q "cannot read missing.jsonl" <<<"$err" && ran_case || fail "a missing baseline: $rc $err"
echo '{"v":1,"metric":"a","direction":"sideways","floor":1}' > bad.jsonl
run check --provider "$P" --baseline bad.jsonl
expect "bad baseline" 4 "" "scoreboard: bad.jsonl: line 1: unknown direction sideways"
run frobnicate
[ "$rc" = 2 ] && grep -q "unknown subcommand frobnicate" <<<"$err" && ran_case || fail "unknown subcommand: $rc $err"
run check --baseline baseline.jsonl
[ "$rc" = 2 ] && grep -q "missing --provider" <<<"$err" && ran_case || fail "missing flag: $rc $err"

# bank: a worse number is never recorded; a regression refuses the whole banking and changes nothing
reads "$(r covered 79)" "$(r warnings 2)"
cp baseline.jsonl b0; cp history.jsonl h0
run bank --provider "$P" --baseline baseline.jsonl --history history.jsonl --author me --reason ratchet --at 100
expect "bank regression" 1 "" "scoreboard: regressed: covered: reading 79 is worse than floor 80 (higher is better)
scoreboard: nothing banked"
cmp -s baseline.jsonl b0 && cmp -s history.jsonl h0 && ran_case || fail "a refused bank changed a file"
# bank: improvements move the floors and append one history line each
reads "$(r covered 85)" "$(r warnings 5)"
run bank --provider "$P" --baseline baseline.jsonl --history history.jsonl --author me --reason ratchet --at 100
expect "bank" 0 "scoreboard: banked: banked covered: 80 -> 85" ""
[ "$(cat baseline.jsonl)" = '{"direction":"higher","floor":85,"metric":"covered","v":1}
{"direction":"lower","floor":5,"metric":"warnings","v":1}' ] && ran_case || fail "bank: baseline is $(cat baseline.jsonl)"
[ "$(cat history.jsonl)" = '{"after":85,"at":100,"author":null,"before":80,"event":"banked","metric":"covered","reason":null,"v":1}' ] && ran_case || fail "bank: history is $(cat history.jsonl)"
# banking again changes nothing (idempotent)
run bank --provider "$P" --baseline baseline.jsonl --history history.jsonl --author me --reason ratchet --at 101
expect "bank again" 0 "scoreboard: nothing to bank: no floor moved" ""
[ "$(wc -l < history.jsonl)" = 1 ] && ran_case || fail "a bank that moved nothing wrote history"
# no temporary file is left
[ "$(ls | grep -c 'tmp\|undo' || true)" = 0 ] && ran_case || fail "a temporary file is left: $(ls)"
# bank with a lower-is-better improvement and two moves: one line each
reads "$(r covered 90)" "$(r warnings 2)"
run bank --provider "$P" --baseline baseline.jsonl --history history.jsonl --author me --reason ratchet --at 102
expect "bank two" 0 "scoreboard: banked: banked covered: 85 -> 90
scoreboard: banked: banked warnings: 5 -> 2" ""
[ "$(wc -l < history.jsonl)" = 3 ] && ran_case || fail "bank two: history is $(cat history.jsonl)"
# a baseline and a history that cannot both be written: nothing changes
cp baseline.jsonl b1; cp history.jsonl h1
reads "$(r covered 95)" "$(r warnings 2)"
mkdir noway; cp baseline.jsonl noway/b; : > noway/h; chmod 555 noway
if [ "$(id -u)" != 0 ]; then
  run bank --provider "$P" --baseline noway/b --history noway/h --at 103
  [ "$rc" = 4 ] && grep -q "cannot write" <<<"$err" && cmp -s noway/b b1 && ran_case || fail "bank into an unwritable directory: $rc $err"
fi
chmod 755 noway

# reset: an explicit, logged lowering
run reset covered --to 70 --reason "provider changed" --author me --baseline baseline.jsonl --history history.jsonl --at 200
expect "reset" 0 "scoreboard: reset covered: 90 -> 70" ""
grep -q '"floor":70' baseline.jsonl && [ "$(tail -n 1 history.jsonl)" = '{"after":70,"at":200,"author":"me","before":90,"event":"reset","metric":"covered","reason":"provider changed","v":1}' ] && ran_case || fail "reset: $(cat baseline.jsonl) $(cat history.jsonl)"
cp baseline.jsonl b2; cp history.jsonl h2
run reset covered --to 99 --reason "x" --author me --baseline baseline.jsonl --history history.jsonl --at 201
expect "reset not looser" 1 "" "scoreboard: reset refused: covered: that is not looser than the floor: use bank"
run reset covered --to 60 --reason "" --author me --baseline baseline.jsonl --history history.jsonl --at 201
expect "reset no reason" 1 "" "scoreboard: reset refused: covered: a reset needs a reason"
run reset nothing --to 1 --reason x --author me --baseline baseline.jsonl --history history.jsonl --at 201
expect "reset no floor" 1 "" "scoreboard: reset refused: nothing: no such metric in the baseline"
cmp -s baseline.jsonl b2 && cmp -s history.jsonl h2 && ran_case || fail "a refused reset changed a file"

# add: a new metric with its first floor and an `added` line
run add speed --direction lower --floor 40 --baseline baseline.jsonl --history history.jsonl --at 300
expect "add" 0 "scoreboard: added speed: - -> 40" ""
grep -q '{"direction":"lower","floor":40,"metric":"speed","v":1}' baseline.jsonl && [ "$(tail -n 1 history.jsonl)" = '{"after":40,"at":300,"author":null,"before":null,"event":"added","metric":"speed","reason":null,"v":1}' ] && ran_case || fail "add: $(cat baseline.jsonl) $(cat history.jsonl)"
run add speed --direction lower --floor 40 --baseline baseline.jsonl --history history.jsonl --at 301
expect "add twice" 1 "" "scoreboard: add refused: speed: the metric already has a floor"
run add other --direction sideways --floor 1 --baseline baseline.jsonl --history history.jsonl
[ "$rc" = 2 ] && ran_case || fail "add with a bad direction: $rc"

# progress: from where a floor started (the history), to its target
run progress --baseline baseline.jsonl --history history.jsonl --target covered=100 --target warnings=0
expect "progress" 0 "metric    direction  start     floor     target    permille
covered   higher     80        70        100       0
speed     lower      40        40        -         -
warnings  lower      5         2         0         600" ""
run progress --baseline baseline.jsonl --history history.jsonl --target covered=x
[ "$rc" = 2 ] && ran_case || fail "a bad target: $rc"

ran_done test_tool
