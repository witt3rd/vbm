#!/usr/bin/env bash
# Run independent test scripts in parallel (Tier 1 wall time = the longest script, not the sum). Usage: scripts/run-tests-parallel.sh SCRIPT...
# Each script runs in its own TMPDIR with its output captured; a passing script prints one line, a failing one its whole log. The run FAILS if any
# script fails, is missing, or leaves no result (killed, or never started): a skipped script is a failure, never a pass; so is a script that exits 0 without a ran-evidence line (`ran: NAME: N cases`, N > 0; scripts/lib-ran.sh) or that reports SKIPPED. TEST_JOBS caps the parallelism.
# A test that passes alone but fails here is a bug in the test: find it, never retry it or raise a timeout. Copied from vbm-json.
set -uo pipefail
cd "$(dirname "$0")/.."
# the environment, not a test: a full temp directory (inodes or blocks) makes git, mktemp and every fixture fail with unrelated symptoms ("unparseable closure output"): say so first
ti=$(df --output=iavail "${TMPDIR:-/tmp}" 2>/dev/null | tail -1 | tr -dc 0-9); tb=$(df --output=avail "${TMPDIR:-/tmp}" 2>/dev/null | tail -1 | tr -dc 0-9)
{ [ -z "$ti" ] || [ "$ti" -gt "${MIN_TMP_INODES:-20000}" ]; } && { [ -z "$tb" ] || [ "$tb" -gt "${MIN_TMP_KIB:-500000}" ]; } || { echo "run-tests-parallel: ${TMPDIR:-/tmp} is nearly full ($ti free inodes, $tb KiB free): the ENVIRONMENT is the failure, not a test; free it or set TMPDIR elsewhere" >&2; exit 1; }
[ $# -gt 0 ] || { echo "run-tests-parallel: no scripts given" >&2; exit 1; }
[ -z "$(printf '%s\n' "$@" | sort | uniq -d)" ] || { echo "run-tests-parallel: a script is listed twice" >&2; exit 1; }
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
export out
name() { echo "${1//\//_}"; }
run_one() {  # run_one SCRIPT: result files rc and secs only when the script ran to its end
  local n; n=$(name "$1"); mkdir "$out/$n.tmp"
  local t0=$SECONDS
  TMPDIR="$out/$n.tmp" bash "$1" > "$out/$n.log" 2>&1 < /dev/null; local rc=$?
  echo $(( SECONDS - t0 )) > "$out/$n.secs"; echo $rc > "$out/$n.rc"
}
export -f name run_one
printf '%s\0' "$@" | xargs -0 -n1 -P "${TEST_JOBS:-$(nproc)}" bash -c 'run_one "$0"'
ev=$(pwd)/scripts/ran-evidence.sh   # a script that exits 0 without `ran: NAME: N cases` (N > 0), or that reports SKIPPED, did not run its checks: a failure (docs/0001-ran-evidence.md)
bad=0
for s in "$@"; do
  n=$(name "$s")
  if [ ! -f "$s" ]; then echo "FAIL $s: no such script" >&2; bad=1
  elif [ ! -f "$out/$n.rc" ]; then echo "FAIL $s: no result (it was skipped, or died before it finished)" >&2; cat "$out/$n.log" 2>/dev/null >&2; bad=1
  elif [ "$(cat "$out/$n.rc")" != 0 ]; then echo "FAIL $s: exit $(cat "$out/$n.rc") after $(cat "$out/$n.secs") s" >&2; cat "$out/$n.log" >&2; bad=1
  elif ! "$ev" check "$s" "$out/$n.log" 2> "$out/$n.ev"; then echo "FAIL $s: exit 0 but no ran-evidence ($(tr '\n' ' ' < "$out/$n.ev"))" >&2; cat "$out/$n.log" >&2; bad=1
  else cat "$out/$n.ev" 2>/dev/null >&2; echo "ok   $s ($(cat "$out/$n.secs") s, $(awk '/^ran: [^:]+: [0-9]+ cases$/ {t += $3} END {print t + 0}' "$out/$n.log") cases)"
  fi
done
if [ $bad = 0 ]; then echo "run-tests-parallel: $# scripts passed"; echo "ran: tests: $(cat "$out"/*.log | awk '/^ran: [^:]+: [0-9]+ cases$/ {t += $3} END {print t + 0}') cases"   # the evidence of the whole batch (tier1's bgwait reads it)
else echo "run-tests-parallel: FAILED" >&2; fi
exit $bad
