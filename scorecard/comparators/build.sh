#!/usr/bin/env bash
# Build the throughput comparators OUTSIDE the sandbox (a host or an image-build step: the network is allowed here and only here) into DEST, which the sandbox then mounts READ-ONLY with no network.
#   scorecard/comparators/build.sh DEST
# Needs: g++ with libsimdjson (headers and library), cargo with network access to crates.io (the crates are vendored here, then built --locked --offline).
# Writes DEST/bin/{simd,serde_bench}, DEST/src (the sources and vendored crates as built), DEST/run.sh and DEST/manifest.json: for each comparator its version, the sha256 of the binary and the sha256 of its inputs
# (sources, lock file, vendored crate checksums; the simdjson library). run.sh recomputes the binary hashes inside the sandbox and refuses a binary that no longer matches. Pins: serde_bench/Cargo.lock (serde_json =1.0.150).
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); dest=${1:?usage: build.sh DEST}
[ ! -e "$dest/manifest.json" ] || { echo "build.sh: $dest already holds a build: use a new directory (builds are immutable)" >&2; exit 1; }
mkdir -p "$dest/bin" "$dest/src"; cp -a "$here/simd.cpp" "$here/serde_bench" "$dest/src/"; cp "$here/run.sh" "$dest/run.sh"; chmod +x "$dest/run.sh"
g++ -O3 -o "$dest/bin/simd" "$dest/src/simd.cpp" -lsimdjson
( cd "$dest/src/serde_bench" && cargo vendor vendor >/dev/null && CARGO_TARGET_DIR="$dest/src/target" cargo build --release --locked --offline >/dev/null )
cp "$dest/src/target/release/serde_bench" "$dest/bin/serde_bench"; rm -rf "$dest/src/target"
python3 - "$dest" <<'PY'
import glob, hashlib, json, os, re, subprocess, sys
d = sys.argv[1]
def h(*paths):
    x = hashlib.sha256()
    for p in paths: x.update(open(p, "rb").read())
    return x.hexdigest()
lib = os.path.realpath(subprocess.run(["bash", "-c", "ldd " + d + "/bin/simd | awk '/libsimdjson/{print $3}'"], capture_output=True, text=True).stdout.strip())
hdr = open("/usr/include/simdjson.h").read() if os.path.exists("/usr/include/simdjson.h") else ""
sv = re.search(r"#define SIMDJSON_VERSION \"([0-9.]+)\"", open(next(iter(glob.glob("/usr/include/simdjson/simdjson_version.h")), "/dev/null")).read() + hdr)
lock = open(d + "/src/serde_bench/Cargo.lock").read()
jv = re.search(r'name = "serde_json"\nversion = "([0-9.]+)"', lock).group(1)
vend = sorted(glob.glob(d + "/src/serde_bench/vendor/*/.cargo-checksum.json"))
m = {"comparators": {
    "simdjson": {"binary": "simd", "version": sv.group(1) if sv else "unknown", "sha256": h(d + "/bin/simd"), "inputs_sha256": h(d + "/src/simd.cpp", lib)},
    "serde_json": {"binary": "serde_bench", "version": jv, "sha256": h(d + "/bin/serde_bench"), "inputs_sha256": h(d + "/src/serde_bench/Cargo.toml", d + "/src/serde_bench/Cargo.lock", d + "/src/serde_bench/src/main.rs", *vend)}},
    "toolchain": {"gxx": subprocess.run(["g++", "--version"], capture_output=True, text=True).stdout.splitlines()[0], "rustc": subprocess.run(["rustc", "--version"], capture_output=True, text=True).stdout.strip()}}
json.dump(m, open(d + "/manifest.json", "w"), indent=2, sort_keys=True); open(d + "/manifest.json", "a").write("\n")
print("built", d, {k: v["version"] for k, v in m["comparators"].items()})
PY
chmod -R a-w "$dest"
