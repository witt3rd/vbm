#!/usr/bin/env bash
# Tier 1 (pre-landing gate): runs every scripts/test_*.sh (the self-tests of the runner, its metrics and the lander) in parallel. Each gate here has a negative
# self-test inside its test script. Every scripts/test_*.sh must be declared below with `par`: an undeclared test fails Tier 1. Run: mise exec -- scripts/tier1.sh
set -euo pipefail
cd "$(dirname "$0")/.."
# RAN-EVIDENCE (docs/0001-ran-evidence.md): a test script that never ran must not pass. Every test script ends with `ran: NAME: N cases` (N > 0); scripts/run-tests-parallel.sh FAILS a script without it
# (or with zero cases, or that reports SKIPPED): a refused tool, a skipped check or a stop by a guard is a failure, never a pass (scripts/ran-evidence.sh; the shared negative test is scripts/test_ran_evidence.sh).
[ "$(grep -c '^ran_done()' scripts/lib-ran.sh)" = 1 ] && [ "$(grep -c '^must_fail()' scripts/lib-ran.sh)" = 1 ] && [ -x scripts/ran-evidence.sh ] && [ "$(grep -c '^  gate)' scripts/ran-evidence.sh)" = 1 ] || { echo "tier1: scripts/lib-ran.sh or scripts/ran-evidence.sh does not define the ran-evidence mechanism" >&2; exit 1; }
tests=(); par() { tests+=("$@"); }
par scripts/test_scorecard.sh scripts/test_lint_public.sh scripts/test_sandbox_conformance.sh scripts/test_registry.sh scripts/test_card_page.sh scripts/test_plain_meanings.sh scripts/test_cards_one_page.sh scripts/test_sandbox_bwrap.sh scripts/test_readme.sh scripts/test_comparators.sh
par scripts/test_manifest.sh
par scripts/test_pins.sh
par scripts/test_license.sh
par scripts/test_tmp_preflight.sh
par scripts/test_export.sh
par scripts/test_no_crash_record.sh
par scripts/test_run_scoped.sh
par scripts/test_reap.sh
par scripts/test_ran_evidence.sh   # the shared negative test of the ran-evidence mechanism: a refused, missing, skipped, silent or zero-count check FAILS
for f in scripts/test_*.sh; do case " ${tests[*]} " in *" $f "*) ;; *) echo "tier1: $f is not declared with par" >&2; exit 1;; esac; done
for f in "${tests[@]}"; do [ -f "$f" ] || { echo "tier1: declared test $f does not exist" >&2; exit 1; }; done
scripts/land/bin/land-check   # the pinned lander is intact (edit vbm-land, not the copy); negative self-test:
scripts/lint-scoped-runners.sh --selftest   # long runners run under scripts/run-scoped.sh (a bounded transient scope, reaped on exit: an aborted run cannot orphan); a guard against accidents, indirection is its stated limit
# No test may leave a crash record (systemd-coredump, hence a desktop notification): the run is wrapped (scripts/lib-no-crash-record.sh; self-test: scripts/test_no_crash_record.sh).
# Audit: no test here crashes on purpose (the fixtures exit 1, the sandbox probes are denials and a timeout kill); a probe that must crash runs under `quiet`.
scripts/no-crash-record.sh begin
scripts/run-tests-parallel.sh "${tests[@]}"
scripts/no-crash-record.sh end
echo "tier1: ok"
