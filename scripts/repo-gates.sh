#!/usr/bin/env bash
# The gates that judge the WHOLE repository. They are one step of EVERY area (docs/areas.md rule 3: a step identical in every area runs once per landing), so a change inside one library cannot skip them:
# the vendored lander is the pinned copy, no build tool runs outside the guard, the tree is public-ready, and no secret is in the history or the tree (vbm-land docs/secrets-gate.md).
set -euo pipefail
cd "$(dirname "$0")/.."
.land/tool/bin/land-check
.land/tool/bin/no-build-guard --lint .
scripts/lint-public
.land/tool/bin/land-secrets --selftest
.land/tool/bin/land-secrets
echo "repo-gates: ok"
