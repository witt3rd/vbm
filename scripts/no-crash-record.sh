#!/usr/bin/env bash
# Tier 1 wrapper around scripts/lib-no-crash-record.sh: `begin` stamps the start (keyed by the calling Tier 1's pid), `end` FAILS when coredumpctl gained a record for a test
# executable since (skips with a note without coredumpctl). Called from scripts/tier1.sh around the whole test run.
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-no-crash-record.sh
f="$(mktemp -u -p "${XDG_RUNTIME_DIR:-${TMPDIR:-/tmp}}" "no-crash-record.XXXXXX" | sed 's|[^/]*$||')no-crash-record.$PPID"
case "${1:-}" in
  begin) nocrash_begin; echo "$nocrash_t0" > "$f";;
  end) nocrash_t0=$(cat "$f"); rm -f "$f"; nocrash_end;;
  *) echo "usage: no-crash-record.sh begin|end" >&2; exit 2;;
esac
