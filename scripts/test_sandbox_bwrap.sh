#!/usr/bin/env bash
# Tier 1: the bubblewrap launcher (scorecard/sandbox-bwrap) passes the conformance probes (each with a positive control: the probe command demonstrably ran), and the runner, given it, measures a fixture subject
# while that subject's commands are DENIED what the sandbox denies: a symlink to a host secret, a connect to a host loopback listener, the host environment. Negative controls: the same commands succeed when run
# directly on the host, so each denial is the sandbox's doing. Needs bwrap with unprivileged user namespaces; without them this test FAILS (a skipped sandbox test would be a green lie).
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (.land/tool/docs/ran-evidence.md)
sb=$(pwd)/scorecard/sandbox-bwrap; sc=$(pwd)/scorecard/scorecard
fail() { echo "tier1: sandbox-bwrap: $*" >&2; exit 1; }
command -v bwrap >/dev/null && ran_case || fail "bwrap is not installed (apt install bubblewrap)"
bwrap --unshare-all --ro-bind / / true 2> "${TMPDIR:-/tmp}/bwrap.err" && ran_case || fail "bwrap cannot create namespaces here (unprivileged user namespaces disabled?): $(cat "${TMPDIR:-/tmp}/bwrap.err"); userns sysctls: $(sysctl -a 2>/dev/null | grep -E 'userns|unprivileged' | tr '\n' ' ')"
rm -f "${TMPDIR:-/tmp}/bwrap.err"
scripts/sandbox-conformance.sh "$sb" > /dev/null 2>&1 || { scripts/sandbox-conformance.sh "$sb" >&2 || true; fail "the bwrap launcher fails the conformance probes"; }
T=$(mktemp -d); trap '[ -z "${lp:-}" ] || kill "$lp" 2>/dev/null; rm -rf "$T"' EXIT; export TMPDIR=$T/tmp; mkdir -p "$TMPDIR"
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
echo TOPSECRET > "$T/host-secret"
port=$(python3 -c 'import socket;s=socket.socket();s.bind(("127.0.0.1",0));print(s.getsockname()[1])')
timeout 120 python3 -c 'import socket,sys;s=socket.socket();s.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1);s.bind(("127.0.0.1",int(sys.argv[1])));s.listen(5);open(sys.argv[2]+".ready","w").write("1")
while True:
    c,_=s.accept();open(sys.argv[2],"a").write("hit\n")' "$port" "$T/hit" & lp=$!
for _ in $(seq 100); do [ -e "$T/hit.ready" ] && break; sleep 0.05; done; [ -e "$T/hit.ready" ] && ran_case || fail "the loopback listener did not start"
# the escape attempts, as one subject command each; EXIT 0 means the attempt SUCCEEDED
read_link() { echo 'grep -q TOPSECRET secretlink'; }
net() { echo "(exec 3<>/dev/tcp/127.0.0.1/$port)"; }
envleak() { echo '[ -z "${HOST_SECRET_VAR-}" ]'; }
mk() {   # mk DIR TIER1-COMMAND: a subject repo whose fast gate is that command and whose closure gate prints a share
  mkdir -p "$1"; git init -q -b main "$1"; ( cd "$1"; mkdir src; echo 'def x := 1' > src/A.lean; ln -s "$T/host-secret" secretlink; echo '### T1' > ledger.md
    cat > scorecard.toml <<TOML
[subject]
name = "fixture"
kind = "library"
[source]
globs = ["src/**/*.lean"]
[trust]
c_files = []
ledger = "ledger.md"
entry_regex = "^### T"
[tests]
generated = []
extra = []
gate_selftests = []
entry_points = []
scenario_files = []
[proof]
sorry_pattern = "sorry"
allow_marker = ""
closure_cmd = "echo specified share 100.0%"
closure_regex = "specified share ([0-9.]+)%"
closure_timeout_seconds = 60
axiom_cmd = ""
axiom_regex = "x"
axiom_timeout_seconds = 60
[bare_metal]
build_cmd = ""
symbols_cmd = ""
allowed_symbols = []
wasm_cmd = ""
wasm_bytes_regex = ""
timeout_seconds = 60
[mutation]
comment = "//"
files = []
setup_cmd = ""
kill_cmd = ""
mutants = 1
seed = 1
kill_timeout_seconds = 10
timeout_seconds = 10
[bench]
cmd = ""
comparators = []
timeout_seconds = 10
[nonvacuity]
comment = "//"
files = []
setup_cmd = ""
kill_cmd = ""
mutants = 1
seed = 1
kill_timeout_seconds = 10
timeout_seconds = 10
[tier1]
command = '$2'
timeout_seconds = 60
script = "scripts/tier1.sh"
[velocity]
window_hours = 168
[floors]
specified_share = 100
TOML
    git add -A; git commit -qm "feat(fix): fixture" ); }
card() { python3 -c 'import json,sys;c=json.load(open(sys.argv[1]));m={x["id"]:x for x in c["metrics"]};print(m[sys.argv[2]][sys.argv[3]])' "$T/card.json" "$1" "$2"; }
run() { HOST_SECRET_VAR=leaked "$sc" run --repo "$1" --commit HEAD --sandbox "$sb" > "$T/card.json" 2> "$T/err" && ran_case || fail "the runner failed: $(cat "$T/err")"; }
# 0. the runner measures through the launcher: the closure gate ran inside it, the attestation is in the card
mk "$T/ok" 'true'; run "$T/ok"; [ "$(card verified.specified_share value)" = 100.0 ] && [ "$(card velocity.tier1_seconds_cold status)" = pass ] && ran_case || fail "the runner did not measure through the launcher: $(cat "$T/card.json")"
python3 -c 'import json,sys;a=json.load(open(sys.argv[1]))["sandbox"]["attestations"];assert len(a)==2 and all(x["kind"]=="bwrap" and x["network"]=="none" for x in a)' "$T/card.json" && ran_case || fail "the card does not record both attestations"
# 1. each escape attempt SUCCEEDS on the host (negative control) and is DENIED in the sandbox (tier-1 command fails)
for name in read_link net envleak; do
  cmd=$($name)
  if [ "$name" = envleak ]; then ( export HOST_SECRET_VAR=leaked; ! bash -c "$cmd" ) && ran_case || fail "control: the host environment variable was not set"; else ( cd "$T" && ln -sf "$T/host-secret" secretlink && bash -c "$cmd" ) 2>/dev/null && ran_case || fail "control: the $name attempt does not succeed on the host, so it proves nothing"; fi
done
: > "$T/hit"
mk "$T/denied1" "$(read_link)";  run "$T/denied1";  [ "$(card velocity.tier1_seconds_cold status)" = fail ] && ran_case || fail "a symlink to a host secret was readable in the sandbox"
mk "$T/denied2" "$(net)";        run "$T/denied2";  [ "$(card velocity.tier1_seconds_cold status)" = fail ] && ! grep -q hit "$T/hit" && ran_case || fail "the sandbox reached a host loopback listener"
mk "$T/ok2" "$(envleak)";        run "$T/ok2";      [ "$(card velocity.tier1_seconds_cold status)" = pass ] && ran_case || fail "the host environment reached the sandbox"
ran_done test_sandbox_bwrap
echo "tier1: sandbox-bwrap: the launcher passes the conformance probes; the runner measures through it; a symlinked host secret, the host network and the host environment are denied (each succeeds on the host): ok"
