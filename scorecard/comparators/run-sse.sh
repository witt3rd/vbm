#!/usr/bin/env bash
# Run the prebuilt SSE comparators (build-sse.sh; mounted read-only) on ONE corpus file at ONE chunk size; runs inside the sandbox, no network, no compiler.
#   $VBM_COMPARATORS/run-sse.sh CORPUS CHUNK    prints, per comparator,  `comparator NAME MB_PER_S`,  `events NAME COUNT`  and  `provenance NAME VERSION SHA256 INPUTS_SHA256`
# Before running anything it recomputes the sha256 of what it runs and compares it with manifest.json (written at build time): a comparator that changed since the build is refused (exit 1).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
[ $# -eq 2 ] && [ -f "$1" ] && [[ "$2" =~ ^[1-9][0-9]*$ ]] || { echo "run-sse.sh: usage: run-sse.sh CORPUS_FILE CHUNK_BYTES" >&2; exit 2; }
[ -f "$here/manifest.json" ] || { echo "run-sse.sh: $here/manifest.json is missing: the comparators were not built" >&2; exit 1; }
python3 - "$here" "$1" "$2" <<'PY'
import hashlib, json, os, subprocess, sys
here, corpus, chunk = sys.argv[1:]
def tree(root):
    x = hashlib.sha256()
    for base, dirs, files in os.walk(root):
        dirs.sort()
        for f in sorted(files):
            p = os.path.join(base, f); x.update(os.path.relpath(p, root).encode() + b"\0" + open(p, "rb").read())
    return x.hexdigest()
for name, c in sorted(json.load(open(here + "/manifest.json"))["comparators"].items()):
    if c["kind"] == "js": got, cmd = tree(here + "/js"), ["node", here + "/js/bench.mjs", corpus, chunk]
    else: got, cmd = hashlib.sha256(open(f"{here}/bin/{c['binary']}", "rb").read()).hexdigest(), [f"{here}/bin/{c['binary']}", corpus, chunk]
    if got != c["sha256"]: sys.exit(f"run-sse.sh: {name}: differs from the manifest (built {c['sha256'][:12]}, found {got[:12]}): refused")
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=600)
    f = r.stdout.split()
    if r.returncode or len(f) != 3 or f[1] != "events": sys.exit(f"run-sse.sh: {name} failed (exit {r.returncode}): {r.stderr[-300:]}")
    print(f"comparator {name} {float(f[0])}"); print(f"events {name} {int(f[2])}"); print(f"provenance {name} {c['version']} {c['sha256']} {c['inputs_sha256']}")
PY
