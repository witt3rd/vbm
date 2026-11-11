#!/usr/bin/env bash
# Tier 1: the License line of README.md and MANIFESTO.md must name the SPDX id the LICENSE file is (Apache-2.0). Negative self-test: a wrong line or a mismatched LICENSE fails.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (.land/tool/docs/ran-evidence.md)
fail() { echo "tier1: license: $*" >&2; exit 1; }
# check <dir>: succeeds when every doc has exactly the line and the LICENSE file is that licence
check() {
  local d=$1 id f
  grep -q '^ *Apache License$' "$d/LICENSE" && grep -q 'Version 2.0, January 2004' "$d/LICENSE" || return 1
  id=Apache-2.0
  for f in README.md MANIFESTO.md; do
    [ "$(grep -c '^License: ' "$d/$f")" = 1 ] && grep -q "^License: $id (see \[LICENSE\](LICENSE))\.\$" "$d/$f" || return 1
  done
}
check . && ran_case || fail "README.md/MANIFESTO.md license line does not equal the LICENSE file"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
fx() { cp LICENSE README.md MANIFESTO.md "$T/"; }
fx; sed -i 's/^License: Apache-2.0/License: MIT/' "$T/README.md"; check "$T" && fail "negative self-test: a wrong README line passed"
fx; sed -i '/^License: /d' "$T/MANIFESTO.md"; check "$T" && fail "negative self-test: a missing MANIFESTO line passed"
fx; echo "MIT License" > "$T/LICENSE"; check "$T" && fail "negative self-test: a non-Apache LICENSE passed"
ran_done test_license
echo "tier1: license: README/MANIFESTO line equals LICENSE (Apache-2.0); wrong line, missing line, wrong file all fail: ok"
