#!/usr/bin/env bash
# Tier 1: the sandbox conformance probes (scripts/sandbox-conformance.sh) can FAIL. A deliberately leaky launcher (it runs the command straight on the host and lies in its attestation) must fail the
# network, undeclared-file, environment and subject-read-only probes, yet pass the time-limit and attestation-parse probes (so each probe is shown to discriminate); a launcher that writes no attestation
# fails that probe. The first conforming launcher is a later slice: it must pass this script, and is added here as a positive case when it lands.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/0001-ran-evidence.md)
fail() { echo "tier1: sandbox-conformance: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
cat > "$T/leaky" <<'SH'
#!/bin/bash
while [ "$1" != -- ]; do case $1 in --subject) s=$2;; --out) o=$2;; --timeout) t=$2;; esac; shift; done; shift
[ "${LEAKY_NO_ATT:-}" = 1 ] || echo '{"image_digest":"sha256:lie","network":"none","subject_mount":"ro","limits":{}}' > "$o/attestation.json"
cd "$s" && exec timeout "$t" bash -c "$1"
SH
chmod +x "$T/leaky"
scripts/sandbox-conformance.sh "$T/leaky" > "$T/out" 2>&1 && fail "a launcher that leaks everything passed the conformance probes"
for p in network undeclared-file environment subject-read-only; do grep -q "^FAIL $p:" "$T/out" && ran_case || fail "the leaky launcher was not caught by the $p probe: $(cat "$T/out")"; done
for p in time-limit attestation; do grep -q "^PASS $p" "$T/out" && ran_case || fail "the $p probe did not pass on a launcher that does that right: $(cat "$T/out")"; done
LEAKY_NO_ATT=1 scripts/sandbox-conformance.sh "$T/leaky" > "$T/out2" 2>&1 && fail "a launcher with no attestation passed"; grep -q "^FAIL attestation" "$T/out2" && ran_case || fail "a missing attestation was not caught"
ran_done test_sandbox_conformance
echo "tier1: sandbox-conformance: the probes fail a leaky launcher (network, file, environment, read-only, attestation) and pass what is done right: ok"
