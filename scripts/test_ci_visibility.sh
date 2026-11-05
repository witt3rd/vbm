#!/usr/bin/env bash
# Tier 1: scripts/check-ci-visibility.py (DECISIONS 16) with a gh shim: public + self-hosted FAILS; private + self-hosted passes; public + hosted passes; unreadable visibility + self-hosted fails closed;
# a runs-on expression that mentions self-hosted counts; the repo's own workflows are judged by the same check in tier1.sh.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/0001-ran-evidence.md)
fail() { echo "tier1: ci-visibility: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT; mkdir -p "$T/w"
printf '#!/bin/sh\n[ -f "$SHIM_DIR/broken" ] && exit 1\ncat "$SHIM_DIR/private"\n' > "$T/gh"; chmod +x "$T/gh"; export SHIM_DIR=$T SCORECARD_GH=$T/gh GITHUB_REPOSITORY=acme/widget
wf() { printf 'name: x\non: push\njobs:\n  a:\n    runs-on: %s\n    steps:\n      - run: true\n' "$2" > "$T/w/$1.yml"; }
chk() { python3 scripts/check-ci-visibility.py "$T/w" > "$T/out" 2>&1 && echo 0 || echo 1; }
rm -f "$T/w"/*; wf a '[self-hosted]'
echo true > "$T/private"; [ "$(chk)" = 0 ] && ran_case || fail "private + self-hosted was refused: $(cat "$T/out")"
echo false > "$T/private"; [ "$(chk)" = 1 ] && grep -q "is PUBLIC" "$T/out" && ran_case || fail "negative self-test: public + self-hosted passed: $(cat "$T/out")"
touch "$T/broken"; [ "$(chk)" = 1 ] && grep -q "failing closed" "$T/out" && ran_case || fail "negative self-test: an unreadable visibility + self-hosted passed: $(cat "$T/out")"
rm "$T/broken"
rm "$T/w"/*; wf b '${{ inputs.fallback_hosted && '"'ubuntu-latest'"' || fromJSON('"'"'["self-hosted"]'"'"') }}'
[ "$(chk)" = 1 ] && ran_case || fail "negative self-test: a runs-on expression that includes self-hosted was not counted (public)"
rm "$T/w"/*; wf c '[my-runner]'; [ "$(chk)" = 1 ] && ran_case || fail "negative self-test: a custom runner label was not counted as self-hosted (public)"
rm "$T/w"/*; wf d ubuntu-latest
[ "$(chk)" = 0 ] && ran_case || fail "public + hosted was refused: $(cat "$T/out")"
touch "$T/broken"; [ "$(chk)" = 0 ] && ran_case || fail "hosted jobs must not need the visibility at all: $(cat "$T/out")"
ran_done test_ci_visibility
echo "tier1: ci-visibility: public + self-hosted fails, private + self-hosted passes, public + hosted passes, unreadable visibility fails closed: ok"
