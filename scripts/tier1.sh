#!/usr/bin/env bash
# Tier 1 (pre-landing gate): runs every scripts/test_*.sh (the self-tests of the runner, its metrics and the lander) in parallel. Each gate here has a negative
# self-test inside its test script. Every scripts/test_*.sh must be declared below with `par`: an undeclared test fails Tier 1. Run: mise exec -- scripts/tier1.sh
set -euo pipefail
cd "$(dirname "$0")/.."
# 0. The vendored libraries are exactly their pins (vbm-land docs/pin.md): the same first step in every repository (this one vendors none today).
.land/tool/bin/land-pin verify
# RAN-EVIDENCE (.land/tool/docs/ran-evidence.md): a test script that never ran must not pass. Every test script ends with `ran: NAME: N cases` (N > 0); .land/tool/bin/run-tests-parallel FAILS a script without it
# (or with zero cases, or that reports SKIPPED): a refused tool, a skipped check or a stop by a guard is a failure, never a pass (.land/tool/bin/ran-evidence; tested in vbm-land).
[ "$(grep -c '^ran_done()' .land/tool/lib/ran.sh)" = 1 ] && [ "$(grep -c '^must_fail()' .land/tool/lib/ran.sh)" = 1 ] && [ -x .land/tool/bin/ran-evidence ] && [ "$(grep -c '^  gate)' .land/tool/bin/ran-evidence)" = 1 ] || { echo "tier1: .land/tool/lib/ran.sh or .land/tool/bin/ran-evidence does not define the ran-evidence mechanism" >&2; exit 1; }
tests=(); par() { tests+=("$@"); }
par scripts/test_scorecard.sh scripts/test_lint_public.sh scripts/test_sandbox_conformance.sh scripts/test_registry.sh scripts/test_card_page.sh scripts/test_plain_meanings.sh scripts/test_cards_one_page.sh scripts/test_sandbox_bwrap.sh scripts/test_readme.sh scripts/test_comparators.sh
par scripts/test_manifest.sh
par scripts/test_pins.sh
par scripts/test_license.sh
par scripts/test_export.sh
par
for f in scripts/test_*.sh; do case " ${tests[*]} " in *" $f "*) ;; *) echo "tier1: $f is not declared with par" >&2; exit 1;; esac; done
for f in "${tests[@]}"; do [ -f "$f" ] || { echo "tier1: declared test $f does not exist" >&2; exit 1; }; done
.land/tool/bin/land-check   # the pinned lander is intact (edit vbm-land, not the copy); negative self-test:
# The heavy-host guard's lint (vbm-land docs/no-build-host.md): declared long runners (scripts/long-runners.txt; none today) run through the vendored .land/tool/bin/run-scoped.sh.
.land/tool/bin/no-build-guard --lint .
# No test may leave a crash record (systemd-coredump, hence a desktop notification): the run is wrapped (.land/tool/lib/no-crash-record.sh; tested in vbm-land).
# Audit: no test here crashes on purpose (the fixtures exit 1, the sandbox probes are denials and a timeout kill); a probe that must crash runs under `quiet`.
. .land/tool/lib/no-crash-record.sh; nocrash_begin
.land/tool/bin/run-tests-parallel "${tests[@]}"
nocrash_end
echo "tier1: ok"
