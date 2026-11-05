#!/usr/bin/env bash
# Run the prebuilt comparators (built by build.sh outside the sandbox, mounted read-only) on ONE corpus file; runs inside the sandbox, no network, no compiler.
#   $VBM_COMPARATORS/run.sh CORPUS      prints, per comparator,  `comparator NAME MB_PER_S`  and  `provenance NAME VERSION BINARY_SHA256 INPUTS_SHA256`
# Before running a binary it recomputes its sha256 and compares it with manifest.json (written at build time): a binary that changed since the build is refused (exit 1).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
[ $# -eq 1 ] && [ -f "$1" ] || { echo "run.sh: usage: run.sh CORPUS_FILE" >&2; exit 2; }
[ -f "$here/manifest.json" ] || { echo "run.sh: $here/manifest.json is missing: the comparators were not built" >&2; exit 1; }
python3 - "$here" "$1" <<'PY'
import hashlib, json, subprocess, sys
here, corpus = sys.argv[1:]
for name, c in sorted(json.load(open(here + "/manifest.json"))["comparators"].items()):
    exe = f"{here}/bin/{c['binary']}"
    h = hashlib.sha256(open(exe, "rb").read()).hexdigest()
    if h != c["sha256"]: sys.exit(f"run.sh: {name}: the binary differs from the manifest (built {c['sha256'][:12]}, found {h[:12]}): refused")
    r = subprocess.run([exe, corpus], capture_output=True, text=True, timeout=300)
    if r.returncode or not r.stdout.split(): sys.exit(f"run.sh: {name} failed (exit {r.returncode})")
    print(f"comparator {name} {float(r.stdout.split()[0])}")
    print(f"provenance {name} {c['version']} {h} {c['inputs_sha256']}")
PY
