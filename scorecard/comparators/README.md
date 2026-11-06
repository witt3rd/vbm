# Comparator builders

The throughput comparators are built outside the sandbox, once, into a directory the sandbox mounts read-only. Builds are immutable: use a new directory each time. Put the output outside `/tmp` (the sandbox mounts its own `/tmp` over it); the build directory is read-only afterwards (`chmod -R u+w` before removing it).

- `build.sh DEST` builds the JSON comparators (simdjson, serde_json); `run.sh` runs them.
- `build-sse.sh DEST` builds the SSE comparators (eventsource-parser from npm, eventsource-stream from crates.io); `run-sse.sh` runs them.

Each build writes `manifest.json`: per comparator its version, the sha256 of what is run and the sha256 of its inputs (sources, lock files, vendored checksums). Inputs and the npm tree and the simdjson binary rebuild byte for byte; a Rust binary does not (the build path is embedded), so the card pins the binary of the build it used and the inputs hash shows the sources are the same. `VBM_COMPARATORS` points the sandbox at the build.
