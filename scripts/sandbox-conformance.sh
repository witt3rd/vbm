#!/usr/bin/env bash
# Conformance probes for a sandbox launcher (scorecard/SPEC.md, "Untrusted subject code"). A launcher lands only if every probe passes.
#   scripts/sandbox-conformance.sh <launcher>      exit 0: all probes pass; exit 1: prints FAIL <probe>: why for each failing probe
# The launcher is called exactly as the runner calls it: <launcher> --subject DIR --out DIR --timeout S --cpus N --memory-mb N --disk-mb N --pids N --net none -- <command>; the command runs with the subject at
# the working directory and its output on stdout. Probes: a TCP connect to a loopback listener started here must fail; a host file outside the mounts must be unreadable; a planted environment variable must not appear;
# a write into the subject must fail; a runaway must be killed at its time limit; the attestation must parse and say network none, subject read-only.
export LC_ALL=C
set -uo pipefail
L=${1:?usage: sandbox-conformance.sh <launcher>}; L=$(realpath "$L")
T=$(mktemp -d); lp=; trap '[ -z "$lp" ] || kill "$lp" 2>/dev/null; rm -rf "$T"' EXIT
mkdir "$T/subject"; echo SUBJECTFILE > "$T/subject/f"; echo TOPSECRET > "$T/host-secret"; export CONF_SECRET=leak-4711
port=$(python3 -c 'import socket;s=socket.socket();s.bind(("127.0.0.1",0));print(s.getsockname()[1])')
timeout 120 python3 -c 'import socket,sys;s=socket.socket();s.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1);s.bind(("127.0.0.1",int(sys.argv[1])));s.listen(1);open(sys.argv[2]+".ready","w").write("1");c,_=s.accept();open(sys.argv[2],"w").write("hit")' "$port" "$T/hit" & lp=$!
for _ in $(seq 100); do [ -e "$T/hit.ready" ] && break; sleep 0.05; done; [ -e "$T/hit.ready" ] || { echo "FAIL harness: the loopback listener did not start" >&2; exit 1; }
bad=0; n=0
probe() {   # probe TIMEOUT COMMAND -> $out, $rc, $secs, the out dir in $od
  n=$((n + 1)); od=$T/out$n; mkdir "$od"; local t0=$SECONDS
  out=$(timeout 60 "$L" --subject "$T/subject" --out "$od" --timeout "$1" --cpus 1 --memory-mb 256 --disk-mb 64 --pids 64 --net none -- "echo RAN; $2" 2>&1) && rc=0 || rc=$?; secs=$((SECONDS - t0))
}
# a probe only counts if its command demonstrably RAN inside the launcher (marker RAN): a launcher that cannot run anything must not pass "denied" probes
result() { if [ "$2" = ok ] && ! grep -q '^RAN' <<<"$out"; then echo "FAIL $1: the probe command never ran (a launcher that runs nothing proves nothing): $out"; bad=1; elif [ "$2" = ok ]; then echo "PASS $1"; else echo "FAIL $1: $2"; bad=1; fi; }
probe 20 "(exec 3<>/dev/tcp/127.0.0.1/$port) 2>/dev/null && echo CONNECTED || echo denied"; sleep 0.3
if grep -q CONNECTED <<<"$out" || [ -e "$T/hit" ]; then result network "the command reached a loopback listener on the host"; else result network ok; fi
probe 20 "cat $T/host-secret 2>&1; true"; if grep -q TOPSECRET <<<"$out"; then result undeclared-file "a host file outside the mounts was readable"; else result undeclared-file ok; fi
probe 20 'echo "v=${CONF_SECRET-unset}"'; if grep -q leak-4711 <<<"$out"; then result environment "a caller environment variable reached the command"; else result environment ok; fi
probe 20 'touch ./conf-written 2>/dev/null && echo WROTE || echo denied'; if grep -q WROTE <<<"$out" || [ -e "$T/subject/conf-written" ]; then result subject-read-only "the command wrote into the subject"; else result subject-read-only ok; fi
probe 2 "sleep 30"; if [ "$rc" = 0 ] || [ "$secs" -gt 15 ]; then result time-limit "a runaway was not killed at its limit (exit $rc after ${secs}s)"; else result time-limit ok; fi
if python3 -c 'import json,sys;d=json.load(open(sys.argv[1]));assert d["network"]=="none" and d["subject_mount"]=="ro" and d["image_digest"]' "$od/attestation.json" 2>/dev/null; then result attestation ok; else result attestation "no attestation.json that says network none, subject_mount ro and carries an image_digest"; fi
exit $bad
