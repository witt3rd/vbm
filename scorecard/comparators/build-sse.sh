#!/usr/bin/env bash
# Build the SSE throughput comparators OUTSIDE the sandbox (network allowed here and only here) into DEST, which the sandbox then mounts READ-ONLY with no network.
#   scorecard/comparators/build-sse.sh DEST
# Needs: node and npm (network to the npm registry), cargo (network to crates.io: the crates are vendored here, then built --locked --offline).
#   eventsource-parser  (npm, scalar, JavaScript: the parser of the Vercel AI SDK and many clients)   pins: sse_js/package.json (exact version), sse_js/package-lock.json (integrity hashes; `npm ci`)
#   eventsource-stream  (crates.io, scalar, Rust: the parser under reqwest-eventsource)                 pins: sse_rs/Cargo.toml (exact versions), sse_rs/Cargo.lock (checksums)
# Writes DEST/js (the package, its dependencies and bench.mjs), DEST/bin/sse_rs, DEST/src (the Rust sources and vendored crates as built), DEST/run-sse.sh and DEST/manifest.json: for each comparator its version, a sha256 of what is run
# (the tree hash of DEST/js; the binary) and a sha256 of its inputs (the lock file and sources). run-sse.sh recomputes the hashes inside the sandbox and refuses what changed since the build.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); dest=${1:?usage: build-sse.sh DEST}
[ ! -e "$dest/manifest.json" ] || { echo "build-sse.sh: $dest already holds a build: use a new directory (builds are immutable)" >&2; exit 1; }
mkdir -p "$dest/bin" "$dest/src" "$dest/js"
cp "$here/sse_js/package.json" "$here/sse_js/package-lock.json" "$here/sse_js/bench.mjs" "$dest/js/"
cp -a "$here/sse_rs" "$dest/src/"; cp "$here/run-sse.sh" "$dest/run-sse.sh"; chmod +x "$dest/run-sse.sh"
( cd "$dest/js" && npm ci --ignore-scripts --no-audit --no-fund >/dev/null )
( cd "$dest/src/sse_rs" && cargo vendor vendor >/dev/null && CARGO_TARGET_DIR="$dest/src/target" cargo build --release --locked --offline >/dev/null )
cp "$dest/src/target/release/sse_rs_bench" "$dest/bin/sse_rs"; rm -rf "$dest/src/target"
python3 - "$dest" <<'PY'
import hashlib, json, os, re, subprocess, sys
d = sys.argv[1]
def h(*paths):
    x = hashlib.sha256()
    for p in paths: x.update(open(p, "rb").read())
    return x.hexdigest()
def tree(root):
    x = hashlib.sha256()
    for base, dirs, files in os.walk(root):
        dirs.sort()
        for f in sorted(files):
            p = os.path.join(base, f); x.update(os.path.relpath(p, root).encode() + b"\0" + open(p, "rb").read())
    return x.hexdigest()
jv = json.load(open(d + "/js/node_modules/eventsource-parser/package.json"))["version"]
rv = re.search(r'name = "eventsource-stream"\nversion = "([0-9.]+)"', open(d + "/src/sse_rs/Cargo.lock").read()).group(1)
vend = sorted(os.popen("ls " + d + "/src/sse_rs/vendor/*/.cargo-checksum.json").read().split())
m = {"comparators": {
    "eventsource-parser": {"kind": "js", "version": jv, "sha256": tree(d + "/js"), "inputs_sha256": h(d + "/js/package.json", d + "/js/package-lock.json")},
    "eventsource-stream": {"kind": "bin", "binary": "sse_rs", "version": rv, "sha256": h(d + "/bin/sse_rs"), "inputs_sha256": h(d + "/src/sse_rs/Cargo.toml", d + "/src/sse_rs/Cargo.lock", d + "/src/sse_rs/src/main.rs", *vend)}},
    "toolchain": {"node": subprocess.run(["node", "--version"], capture_output=True, text=True).stdout.strip(), "rustc": subprocess.run(["rustc", "--version"], capture_output=True, text=True).stdout.strip()}}
json.dump(m, open(d + "/manifest.json", "w"), indent=2, sort_keys=True); open(d + "/manifest.json", "a").write("\n")
print("built", d, {k: v["version"] for k, v in m["comparators"].items()})
PY
chmod -R a-w "$dest"
