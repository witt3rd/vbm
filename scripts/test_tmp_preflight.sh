#!/usr/bin/env bash
# Tier 1: scripts/run-tests-parallel.sh names a FULL temp directory (inodes or blocks) as the environment's failure before any test runs (a full /tmp once made git, mktemp and fixtures fail with unrelated symptoms).
# Negative self-test: with the minimums raised above what any disk has, it refuses and says so; with the defaults and a roomy temp dir it runs.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/0001-ran-evidence.md)
fail() { echo "tier1: tmp-preflight: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT; printf 'echo "ran: ok: 1 cases"\n' > "$T/ok.sh"
MIN_TMP_INODES=999999999999 scripts/run-tests-parallel.sh "$T/ok.sh" > "$T/out" 2>&1 && fail "negative self-test: a nearly full temp dir (inodes) was not refused"; grep -q "ENVIRONMENT is the failure" "$T/out" && ran_case || fail "wrong message: $(cat "$T/out")"
MIN_TMP_KIB=999999999999 scripts/run-tests-parallel.sh "$T/ok.sh" > "$T/out" 2>&1 && fail "negative self-test: a nearly full temp dir (blocks) was not refused"; grep -q "ENVIRONMENT is the failure" "$T/out" && ran_case || fail "wrong message: $(cat "$T/out")"
scripts/run-tests-parallel.sh "$T/ok.sh" > "$T/out" 2>&1 && ran_case || fail "a roomy temp dir was refused: $(cat "$T/out")"
ran_done test_tmp_preflight
echo "tier1: tmp-preflight: a full temp directory is named as the environment's failure before any test runs: ok"
