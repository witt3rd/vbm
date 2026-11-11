#!/usr/bin/env bash
# Tier 1: the comparator tooling (scorecard/comparators): run.sh, which runs INSIDE the sandbox, prints a number and a pinned provenance line per comparator and REFUSES a binary whose sha256 no longer matches the manifest
# written at build time (tampered, swapped or rebuilt in place); a missing manifest or a bad call fails. build.sh (network, outside the sandbox) is checked statically: it refuses an existing build directory, builds the crates
# --locked --offline from vendored sources, and the lock file pins the version Cargo.toml names. The real build is a host step (it needs network and a toolchain), not a Tier 1 step.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (.land/tool/docs/ran-evidence.md)
c=$(pwd)/scorecard/comparators
fail() { echo "tier1: comparators: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
D=$T/build; mkdir -p "$D/bin"; cp "$c/run.sh" "$D/run.sh"
printf '#!/bin/sh\necho 111.5\n' > "$D/bin/a"; printf '#!/bin/sh\necho 222.25\n' > "$D/bin/b"; chmod +x "$D/bin/a" "$D/bin/b"; echo corpus > "$T/corpus"
python3 - "$D" <<'PY'
import hashlib, json, sys
d = sys.argv[1]; h = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()
json.dump({"comparators": {"alpha": {"binary": "a", "version": "1.0.0", "sha256": h(d + "/bin/a"), "inputs_sha256": "i" * 64}, "beta": {"binary": "b", "version": "2.5", "sha256": h(d + "/bin/b"), "inputs_sha256": "j" * 64}}}, open(d + "/manifest.json", "w"))
PY
out=$("$D/run.sh" "$T/corpus") && ran_case || fail "run.sh failed on an intact build"
ha=$(sha256sum "$D/bin/a" | cut -d' ' -f1)
[ "$out" = "$(printf 'comparator alpha 111.5\nprovenance alpha 1.0.0 %s %s\ncomparator beta 222.25\nprovenance beta 2.5 %s %s' "$ha" "$(printf 'i%.0s' $(seq 64))" "$(sha256sum "$D/bin/b" | cut -d' ' -f1)" "$(printf 'j%.0s' $(seq 64))")" ] && ran_case || fail "run.sh output is not the number and the pinned provenance of each comparator: $out"
printf '#!/bin/sh\necho 999\n' > "$D/bin/a"; "$D/run.sh" "$T/corpus" > "$T/o" 2> "$T/e" && fail "negative self-test: a binary changed after the build was run"; grep -q "differs from the manifest" "$T/e" && ran_case || fail "wrong message for a tampered binary: $(cat "$T/e")"
! grep -q "^comparator" "$T/o" && ran_case || fail "a tampered binary's number was printed before it was refused"
rm "$D/manifest.json"; "$D/run.sh" "$T/corpus" >/dev/null 2>"$T/e" && fail "negative self-test: a missing manifest was accepted"; grep -q "manifest.json is missing" "$T/e" && ran_case || fail "wrong message for a missing manifest"
"$D/run.sh" >/dev/null 2>&1 && fail "run.sh without a corpus succeeded"
bash -n "$c/build.sh" && bash -n "$c/run.sh" && ran_case || fail "a comparator script does not parse"
grep -q -- '--release --locked --offline' "$c/build.sh" && ran_case || fail "build.sh does not build the crates --locked --offline from vendored sources"
mkdir -p "$T/old" && echo '{}' > "$T/old/manifest.json"; "$c/build.sh" "$T/old" >/dev/null 2>"$T/e" && fail "build.sh overwrote an existing build"; grep -q "already holds a build" "$T/e" && ran_case || fail "wrong message for an existing build"
"$c/build.sh" >/dev/null 2>&1 && fail "build.sh ran without a destination"
pin=$(sed -n 's/^serde_json = "=\(.*\)"/\1/p' "$c/serde_bench/Cargo.toml"); lock=$(grep -A1 '^name = "serde_json"' "$c/serde_bench/Cargo.lock" | sed -n 's/^version = "\(.*\)"/\1/p')
[ -n "$pin" ] && [ "$pin" = "$lock" ] && ran_case || fail "Cargo.toml pins serde_json '$pin' but Cargo.lock has '$lock'"
[ -f "$c/simd.cpp" ] && [ -f "$c/serde_bench/src/main.rs" ] && [ -f "$c/serde_bench/.cargo/config.toml" ] && ran_case || fail "a comparator source is missing"
ran_done test_comparators
echo "tier1: comparators: run.sh prints numbers with pinned provenance and refuses a changed binary; build.sh is immutable, locked and offline: ok"
