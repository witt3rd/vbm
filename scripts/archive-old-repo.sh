#!/usr/bin/env bash
# archive-old-repo.sh NAME: the old repository gets a last landing (through its own lander) that replaces README.md with a notice, then is archived (read-only; no tag removed, nothing deleted).
set -euo pipefail
export PATH=$HOME/.local/share/mise/shims:$PATH
N=${1:?usage: archive-old-repo.sh NAME}; D=/var/tmp/arch-$N; rm -rf "$D"
export GIT_CONFIG_COUNT=1 GIT_CONFIG_KEY_0=url.git@github.com:witt3rd/.insteadOf GIT_CONFIG_VALUE_0=https://github.com/witt3rd/
git clone -q "https://github.com/witt3rd/$N.git" "$D"; cd "$D"; git config user.name "${ID_NAME:?set ID_NAME to the name the project commits under}"; git config user.email "witt3rd@witt3rd.com"
git checkout -q -B agent/moved-notice origin/main
tags=$(git tag | sed 's/^/`/;s/$/`/' | tr '\n' ' ')
cat > README.md <<MD
# $N has moved

**This repository is archived (read-only).** The library now lives in the VBM family repository:

> **https://github.com/witt3rd/vbm/tree/main/lib/$N**

* **History:** all of this repository's history is in the family repository (\`git log lib/$N\` and \`git blame\` follow it).
* **Releases:** the releases made here (${tags:-none}) stay here with their signatures. Each is released again there as \`$N/<version>\` (signed by the same key; its \`tree_sha256\` is identical). New releases are tagged \`$N/vX.Y.Z\` in the family repository.
* **Issues and changes:** open them in the family repository.
* **Pins:** a pin at a tag of this repository keeps verifying (the files are unchanged); re-point it with \`land-pin vendor $N https://github.com/witt3rd/vbm $N/<version>\` and the vendored files come out byte for byte as they were.

The library is Apache-2.0 licensed (see \`LICENSE\`).
MD
git add README.md
git commit -q -m "docs: $N has moved to lib/$N of the family repository; this repository is archived" -m "Task-ID: $N-archive-notice"
echo "[$(date +%T)] $N: landing the notice (identity $(git log -1 --format=%ae))"
timeout 2700 .land/land-direct 2>&1 | tail -2 | cut -c1-220
[ "$(git ls-remote origin refs/heads/main | cut -f1)" = "$(git rev-parse HEAD)" ] || [ "$(gh api repos/witt3rd/$N/contents/README.md --jq .content | base64 -d | head -1)" = "# $N has moved" ] || { echo "$N: the notice did not land: NOT archiving"; exit 1; }
gh api -X PATCH "repos/witt3rd/$N" -f archived=true --jq '"[archived] \(.name): archived=\(.archived)"'
