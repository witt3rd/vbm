#!/usr/bin/env bash
# Tier 1: the runner (scorecard/scorecard) and every metric, against fixture subjects built here. Each gate is shown able to fail in the same run:
#  schema: every required adapter key, removed one at a time, is rejected (exit 2); an unknown key/section, a bad kind, a library floor under 100, a bad commit, a missing adapter are rejected;
#  the subject is only read (a byte-level snapshot of the repo is identical after a run) and the scratch clone is removed; the card is pinned (the named commit, not the working tree) and deterministic.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/0001-ran-evidence.md)
sc=$(pwd)/scorecard/scorecard
fail() { echo "tier1: scorecard: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT; export TMPDIR=$T/tmp; mkdir -p "$TMPDIR"
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
# jq-free JSON access: field PATH (dotted; a list index is a number; a metric by id: metric:ID.field) from the card in $T/card.json
card() { python3 - "$1" <<'PY'
import json, sys
import os
c = json.load(open(os.environ["T"] + "/card.json"))
p = sys.argv[1]
if p.startswith("metric:"):
    mid, _, f = p[7:].rpartition("."); v = next(m for m in c["metrics"] if m["id"] == mid)[f]
else:
    v = c
    for k in p.split("."): v = v[int(k)] if isinstance(v, list) else v[k]
print(json.dumps(v) if isinstance(v, (dict, list)) else ("null" if v is None else str(v).lower() if isinstance(v, bool) else v))
PY
}
export T
cat > "$T/fake" <<'SH'
#!/bin/bash
# a TEST launcher: runs the fixture's command on the host (our own fixtures only, never a real subject) and writes an attestation per $T/mode: ok | noatt | net (claims network host) | limits (wrong limits) | hang (ignores its timeout)
d=$(dirname "$0"); mode=$(cat "$d/mode" 2>/dev/null || echo ok); echo "$@" >> "$d/launch.args"; env > "$d/launch.env"
while [ "$1" != -- ]; do case $1 in --subject) s=$2;; --out) o=$2;; --timeout) t=$2;; --cpus) c=$2;; --memory-mb) m=$2;; --disk-mb) k=$2;; --pids) p=$2;; esac; shift; done; shift
net=none; [ "$mode" != net ] || net=host; [ "$mode" != limits ] || k=1
[ "$mode" = noatt ] || echo "{\"image_digest\":\"sha256:fake\",\"network\":\"$net\",\"subject_mount\":\"ro\",\"limits\":{\"cpus\":$c,\"memory_mb\":$m,\"disk_mb\":$k,\"pids\":$p,\"timeout_seconds\":$t}}" > "$o/attestation.json"
[ "$mode" != hang ] || exec sleep 100
cd "$s" && exec timeout "$t" bash -c "$1"
SH
chmod +x "$T/fake"; sbargs=(--sandbox "$T/fake"); export SCORECARD_GRACE_SECONDS=2
printf 'repos = ["example/fixture"]\nmeasured_per_month = 1\n' > "$T/allow.toml"   # the fixtures' origin is on this allowlist (SPEC rule 10; the refusal itself is tested in test_manifest.sh)
run() { "$sc" run "$@" --allowlist "$T/allow.toml" "${sbargs[@]}" >"$T/card.json" 2>"$T/err" && rc=0 || rc=$?; }
adapter() {   # adapter KIND FLOOR CLOSURE_CMD  -> scorecard.toml text (the full valid schema)
local mf=${MUT_FILES-'["mut/*.c"]'} mk=${MUT_KILL-'grep -q "a < b" mut/ops.c'} nk=${NV_KILL-'grep -q "p < q" spec/ops.c'} H64=$(printf 'a%.0s' $(seq 64)); bc=${BENCH_CMD-"echo corpus $H64 100; echo subject 900; echo comparator py 1000; echo provenance py 1.0 $H64 -"} br=${BENCH_COMP-'{ name = "py", scalar = true }'} ep=${ENTRY_POINTS-} sf=${SCENARIO_FILES-}
cat <<TOML
[subject]
name = "fixture"
kind = "${1:-library}"
[source]
globs = ["src/**/*.lean"]
[trust]
c_files = ["c/*.c"]
ledger = "docs/trust-ledger.md"
entry_regex = "^### T[0-9]"
[tests]
generated = ["vectors/**"]
extra = []
gate_selftests = ["scripts/test_*.sh"]
entry_points = [$ep]
scenario_files = [$sf]
[proof]
sorry_pattern = "\\\\b(sorry|admit|axiom|unsafe|implemented_by|csimp)\\\\b"
allow_marker = "tier1-allow"
closure_cmd = "${3-sh scripts/closure.sh}"
closure_regex = "specified share ([0-9.]+)%"
closure_timeout_seconds = 60
${PROOF_EXTRA-}
axiom_cmd = '${AXIOM_CMD-echo axiom gate: 3 constants checked, 0 offending}'
axiom_regex = "axiom gate: [0-9]+ constants checked, ([0-9]+) offending"
axiom_timeout_seconds = 60
[bare_metal]
build_cmd = '${BUILD_CMD-true}'
symbols_cmd = '${SYMBOLS_CMD-echo --end-of-symbols--}'
allowed_symbols = [${ALLOWED_SYMBOLS-}]
wasm_cmd = '${WASM_CMD-}'
wasm_bytes_regex = 'wasm bytes: ([0-9]+)'
timeout_seconds = 60
[mutation]
comment = '//'
${MUT_EQ:+equivalent = '$MUT_EQ'}
files = $mf
setup_cmd = ''
kill_cmd = '$mk'
mutants = ${MUT_N-50}
seed = ${MUT_SEED-7}
kill_timeout_seconds = 20
timeout_seconds = 60
[bench]
cmd = '$bc'
comparators = [$br]
timeout_seconds = 60
[nonvacuity]
comment = '${NV_COMMENT-//}'
files = ["spec/*.c"]
setup_cmd = ''
kill_cmd = '$nk'
mutants = 50
seed = 3
kill_timeout_seconds = 20
timeout_seconds = 60
[tier1]
command = "echo selftest alpha ok; echo ran: alpha: 3 cases"
timeout_seconds = 60
warm_change_cmd = "true"
warm_command = "echo selftest alpha ok; echo ran: alpha: 3 cases"
warm_timeout_seconds = 60
script = "scripts/tier1.sh"
gates = [{ name = "alpha", selftest = "selftest alpha ok" }]
ran_names = ["alpha"]
attack_cmd = 'echo PASS relabel-attacks: 3 of 3'
attack_sabotage_cmd = 'echo FAIL relabel-attacks: 0 of 3; exit 1'
[velocity]
window_hours = 168
[floors]
specified_share = ${2:-100}
TOML
}
mkfixture() {   # mkfixture DIR [ADAPTER_TEXT]: a clean subject, one commit
  mkdir -p "$1"; git init -q -b main "$1"; ( cd "$1"; mkdir -p src c docs vectors scripts mut spec
    printf 'def f : Nat := 1\n' > src/Core.lean; printf 'int x;\nint y;\nint z;\n' > c/rt.c; printf 'int lt(int a, int b) { return a < b; }\n' > mut/ops.c; printf 'int lt(int p, int q) { return p < q; }\n' > spec/ops.c; printf '### T1. a\n### T2. b\n' > docs/trust-ledger.md; printf '{}\n' > vectors/v.json
    printf 'echo "closure gate: spec 10 of 10 | specified share 100.00%% (floor 100.00%%)"\n' > scripts/closure.sh; printf 'par scripts/test_x.sh\n' > scripts/tier1.sh; echo 'echo watched fail' > scripts/test_x.sh
    printf '%s\n' "${2:-$(adapter)}" > scorecard.toml; git remote add origin git@github.com:example/fixture.git; git add -A; git commit -qm "feat(fix): fixture" ); }
printf '#!/bin/sh\ncat "$T/prs"\n' > "$T/gh"; chmod +x "$T/gh"; echo '[]' > "$T/prs"; export SCORECARD_GH="$T/gh"   # the gh shim: `gh pr list` prints $T/prs
snap() { find "$1" -xdev -printf '%p %y %s %T@\n' | sort | sha256sum; }
G=$T/good; mkfixture "$G"; sha=$(git -C "$G" rev-parse HEAD)
# 1. a card for the good fixture: pinned, valid, every unimplemented floored metric not-measurable with a reason, strict result fail
before=$(snap "$G"); run --repo "$G" --commit "$sha"; [ "$rc" = 0 ] && ran_case || fail "good fixture: exit $rc: $(cat "$T/err")"
[ "$(snap "$G")" = "$before" ] && ran_case || fail "the subject was mutated by a run (snapshot differs)"
[ -z "$(ls "$TMPDIR")" ] && ran_case || fail "the scratch clone was not removed: $(ls "$TMPDIR")"
[ "$(card subject.commit)" = "$sha" ] && [ "$(card schema)" = scorecard-3 ] && [ "$(card subject.name)" = fixture ] && ran_case || fail "the card does not name the pinned commit"
[ "$(python3 -c 'import json,os; print(all(m["implemented"] for m in json.load(open(os.environ["T"] + "/card.json"))["metrics"]))')" = True ] && ran_case || fail "a metric of the table is not implemented in this runner version (the not-implemented path is stale: add its negative self-test back with the next such metric)"
[ "$(card metric:honesty.attack_suite.status)" = pass ] && [ "$(card honesty_unused 2>/dev/null || echo x)" = x ] && ran_case || fail "the good fixture's declared attack suite did not pass"
# determinism (SPEC rule 1): two runs of the same commits are byte-identical once the wall-clock values a metric MEASURES (marked "measured": true: they vary with load) are masked. Root cause of a flake seen under load: the tier-1 seconds
# were compared raw and read 0.0 on one run and 0.1 on the next. The masking is itself shown able to fail: a planted timestamp, or a changed unmarked number, is NOT masked.
mask() { python3 - "$1" <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
for m in c["metrics"]:
    if m.get("measured"): m["value"] = "<measured>"
print(json.dumps(c, indent=2, sort_keys=True))
PY
}
cp "$T/card.json" "$T/card1.json"
for n in 2 3 4; do run --repo "$G" --commit "$sha"; cp "$T/card.json" "$T/card$n.json"; done
for n in 2 3 4; do [ "$(mask "$T/card1.json")" = "$(mask "$T/card$n.json")" ] && ran_case || fail "same commits, different bytes (run $n; measured values masked): $(diff <(mask "$T/card1.json") <(mask "$T/card$n.json") | head -20)"; done
python3 - "$T/card1.json" "$T/card_planted.json" <<'PY'
import json, sys
c = json.load(open(sys.argv[1])); c["scorecard"]["ran_at"] = "2026-11-04T12:00:00"; json.dump(c, open(sys.argv[2], "w"))
PY
[ "$(mask "$T/card1.json")" != "$(mask "$T/card_planted.json")" ] && ran_case || fail "negative self-test: a planted timestamp was masked away: the determinism check cannot fail"
python3 - "$T/card1.json" "$T/card_planted.json" <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
m = next(m for m in c["metrics"] if m["id"] == "verified.trusted_c_lines"); m["value"] += 1; json.dump(c, open(sys.argv[2], "w"))
PY
[ "$(mask "$T/card1.json")" != "$(mask "$T/card_planted.json")" ] && ran_case || fail "negative self-test: a changed unmarked number was masked away"
[ "$(python3 -c 'import json,sys; c=json.load(open(sys.argv[1])); print([m["id"] for m in c["metrics"] if m.get("measured")])' "$T/card1.json")" = "['velocity.tier1_seconds_warm', 'velocity.tier1_seconds_cold']" ] && ran_case || fail "exactly the tier-1 seconds (warm and cold) should be marked measured"
# 2. pinned: a later commit changes the adapter; the card for the first commit still reads the first
echo 'x' >> "$G/c/rt.c"; sed -i 's/name = "fixture"/name = "later"/' "$G/scorecard.toml"; git -C "$G" commit -qam "feat(fix): later"
run --repo "$G" --commit "$sha"; [ "$(card subject.name)" = fixture ] && ran_case || fail "the card read the working tree, not the pinned commit"
run --repo "$G" --commit HEAD; [ "$(card subject.name)" = later ] && [ "$(card subject.commit)" = "$(git -C "$G" rev-parse HEAD)" ] && ran_case || fail "HEAD was not resolved to its SHA"
# 3. schema: each required key removed in turn is rejected naming the key; so are unknown keys, a bad kind, a library floor under 100
keys=$(python3 - <<PY
import importlib.machinery, importlib.util
l = importlib.machinery.SourceFileLoader("sc", "$sc"); s = importlib.util.spec_from_loader("sc", l); m = importlib.util.module_from_spec(s); l.exec_module(m)
print("\n".join(f"{sec} {k}" for sec, ks in m.ADAPTER.items() for k in ks))
PY
)
[ "$(wc -l <<<"$keys")" -ge 15 ] && ran_case || fail "the schema read from the runner is suspiciously small"
while read -r sec key; do
  awk -v s="[$sec]" -v k="$key" '/^\[/{cur=$0} !(cur==s && $1==k)' <<<"$(adapter)" > "$T/bad.toml"
  run --repo "$G" --commit "$sha" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "missing key \[$sec\] $key" "$T/err" && ran_case || fail "a missing adapter key [$sec] $key was not rejected (exit $rc): $(cat "$T/err")"
done <<<"$keys"
{ adapter; echo 'extra = 1'; } > "$T/bad.toml"; run --repo "$G" --commit "$sha" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "unknown key" "$T/err" && ran_case || fail "an unknown key was accepted"
{ adapter; printf '[surprise]\na = 1\n'; } > "$T/bad.toml"; run --repo "$G" --commit "$sha" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "unknown section" "$T/err" && ran_case || fail "an unknown section was accepted"
adapter weird > "$T/bad.toml"; run --repo "$G" --commit "$sha" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "kind must be" "$T/err" && ran_case || fail "a bad kind was accepted"
adapter library 90 > "$T/bad.toml"; run --repo "$G" --commit "$sha" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "library's" "$T/err" && ran_case || fail "a library floor under 100 was accepted"
adapter runtime 45.8 > "$T/ok.toml"; run --repo "$G" --commit "$sha" --adapter "$T/ok.toml"; [ "$rc" = 0 ] && [ "$(card metric:verified.specified_share.floor)" = '{"op": ">=", "value": 45.8}' ] && ran_case || fail "a runtime's own floor was not honoured: $(cat "$T/err")"
# 4. bad input: unknown commit, not a repo, no adapter at the commit
run --repo "$G" --commit deadbeef; [ "$rc" = 2 ] && ran_case || fail "an unknown commit was accepted"
run --repo "$T/nowhere" --commit HEAD; [ "$rc" = 2 ] && ran_case || fail "a missing repo was accepted"
mkdir "$T/bare" && git init -q -b main "$T/bare" && git -C "$T/bare" commit -q --allow-empty -m "feat(fix): empty"; run --repo "$T/bare" --commit HEAD; [ "$rc" = 2 ] && grep -q "no adapter" "$T/err" && ran_case || fail "a subject without an adapter was accepted"
echo "tier1: scorecard: runner: schema, pinning, read-only subject, determinism: ok"

# ---- the metrics, each with a fixture shown to trip it ----
m() { card "metric:$1"; }   # m ID.field
mp() { python3 - "$1" "$2" <<'PY'   # mp ID DOTTED.PATH.INTO.THE.METRIC (a list index is a number)
import json, os, sys
v = next(m for m in json.load(open(os.environ["T"] + "/card.json"))["metrics"] if m["id"] == sys.argv[1])
for k in sys.argv[2].split("."): v = v[int(k)] if isinstance(v, list) else v[k]
print(v)
PY
}
# 5. the good fixture: every metric passes: both verdicts pass; there is no blended result
G2=$T/good2; mkfixture "$G2"; s2=$(git -C "$G2" rev-parse HEAD); run --repo "$G2" --commit "$s2"; [ "$rc" = 0 ] && ran_case || fail "good2: $(cat "$T/err")"
[ "$(card verdicts.correctness.status)" = pass ] && [ "$(card verdicts.landedness.status)" = pass ] && [ "$(card verdicts.profile.dimensions)" = '{"bare_metal": "pass", "efficiency": "pass"}' ] && ran_case || fail "good fixture: a verdict is not pass (every metric of the table is implemented now): $(card verdicts)"
[ "$(card verdicts.correctness.not_defined_yet)" = '["generation"]' ] && [ "$(card verdicts.correctness.measured)" = 3 ] && [ "$(card verdicts.correctness.of)" = 4 ] && ran_case || fail "the Correctness verdict does not state its coverage (3 of 4, Trusted generation undefined): $(card verdicts.correctness)"
[ -z "$(card result 2>/dev/null)" ] && [ -z "$(card implemented_result 2>/dev/null)" ] && ran_case || fail "the card carries a blended result: there are two verdicts and a profile, never one score"
[ "$(m verified.unproved_escapes.value)" = 0 ] && [ "$(m verified.specified_share.value)" = 100.0 ] && [ "$(m verified.trusted_c_lines.value)" = 3 ] && [ "$(m verified.trust_ledger_entries.value)" = 2 ] \
  && [ "$(m construction.hand_written_tests.value)" = 0 ] && [ "$(m velocity.open_prs.value)" = 0 ] && [ "$(m velocity.tier1_seconds_cold.status)" = pass ] && ran_case || fail "good fixture: a measured value is wrong: $(cat "$T/card.json")"
[ "$(card dimensions.verified.below_floor)" = "[]" ] && [ "$(card dimensions.honesty.below_floor)" = "[]" ] && [ "$(card dimensions.velocity.status)" = pass ] && ran_case || fail "good fixture: the dimensions are wrong"
# 6. a planted sorry is counted and fails the card; tier1-allow skips a comment; a file outside source.globs is not scanned
S=$T/sorry; mkfixture "$S"; ( cd "$S"; printf 'theorem t : True := by sorry\n-- says sorry (tier1-allow)\ndef ok := 1\n' > src/Core.lean; printf 'axiom a : True\n' > docs/outside.lean; git commit -qam "feat(fix): plant a sorry" )
run --repo "$S" --commit HEAD; [ "$(m verified.unproved_escapes.value)" = 1 ] && [ "$(m verified.unproved_escapes.status)" = fail ] && [ "$(m verified.unproved_escapes.findings)" = '["src/Core.lean:1"]' ] && ran_case || fail "a planted sorry was not counted exactly once: $(m verified.unproved_escapes.findings)"
[ "$(card verdicts.correctness.status)" = fail ] && [ "$(card verdicts.landedness.status)" = pass ] && [ "$(card dimensions.verified.status)" = fail ] && grep -q verified.unproved_escapes <<<"$(card dimensions.verified.below_floor_implemented)" && ran_case || fail "a planted sorry did not fail the card"
for w in admit axiom unsafe implemented_by csimp; do printf 'x := %s\n' $w > "$S/src/Core.lean"; git -C "$S" commit -qam "feat(fix): $w"; run --repo "$S" --commit HEAD; [ "$(m verified.unproved_escapes.value)" = 1 ] && ran_case || fail "the forbidden word $w was not counted"; done
# 7. below its floor FAILS the card, and no other dimension rescues it (no averaging): specified share 90 vs the library floor 100, everything else clean
B=$T/below; mkfixture "$B" "$(adapter library 100 'echo specified share 90.00%')"; run --repo "$B" --commit HEAD
[ "$(m verified.specified_share.value)" = 90.0 ] && [ "$(m verified.specified_share.status)" = fail ] && [ "$(card dimensions.verified.status)" = fail ] && [ "$(card dimensions.velocity.status)" = pass ] && [ "$(card verdicts.correctness.status)" = fail ] && [ "$(card verdicts.landedness.status)" = pass ] && ran_case || fail "a fixture below its floor did not fail the card: $(card dimensions)"
mkfixture "$T/runtime" "$(adapter runtime 45.8 'echo specified share 45.8%')"; run --repo "$T/runtime" --commit HEAD; [ "$(m verified.specified_share.status)" = pass ] && ran_case || fail "a runtime at its own floor failed"
mkfixture "$T/runtime2" "$(adapter runtime 45.8 'echo specified share 45.7%')"; run --repo "$T/runtime2" --commit HEAD; [ "$(m verified.specified_share.status)" = fail ] && ran_case || fail "a runtime below its own floor passed"
# 7b. DECISIONS 20: the floor stays 100; a boundary that cannot be specified is a documented, protected carve-out whose mass may only shrink, and the card shows it
PX='carveouts = "scripts/carveouts.txt"'$'\n''carveouts_protected = "scripts/protected-paths.txt"'$'\n''carveouts_regex = "carve-outs: ([0-9]+) nodes"'$'\n''carveouts_baseline = "scripts/closure-baseline.txt"'
mkco() {   # mkco DIR LIST-LINE PROTECTED-LIST BASELINE-LINE: a subject whose ledger has T13, with the given carve-out list, protected list and baseline
  ( cd "$1"; printf '### T13. The pinned library (a documented reason)\n- **What:** four shims.\n- **Plan:** verify; the kernel is proved in its own repository and the shim is tested there.\n- **Covers:** x\n' > docs/trust-ledger.md; printf '%s\n' "$2" > scripts/carveouts.txt; printf '%s\n' "$3" > scripts/protected-paths.txt; printf '%s\n' "$4" > scripts/closure-baseline.txt; git add -A; git commit -qm carveouts --amend ); }
CL='echo specified share 100.00%; echo closure gate: carve-outs: 36 nodes'
C1=$T/co1; PROOF_EXTRA="$PX" mkfixture "$C1" "$(PROOF_EXTRA="$PX" adapter library 100 "$CL")"; mkco "$C1" 'findAvx2 | T13 | scripts/pinned-libs.lock' 'scripts/pinned-libs.lock' 'carveout_mass 36'; run --repo "$C1" --commit HEAD
[ "$(m verified.specified_share.status)" = pass ] && [ "$(m verified.specified_share.carveout_nodes)" = 36 ] && grep -q "T13" <<<"$(m verified.specified_share.carveouts)" && grep -q "kernel is proved" <<<"$(m verified.specified_share.carveouts)" && ran_case || fail "a documented, protected carve-out within its baseline did not pass and show itself: $(m verified.specified_share.reason)"
C2=$T/co2; PROOF_EXTRA="$PX" mkfixture "$C2" "$(PROOF_EXTRA="$PX" adapter library 100 "$CL")"; mkco "$C2" 'findAvx2 | T99 | scripts/pinned-libs.lock' 'scripts/pinned-libs.lock' 'carveout_mass 36'; run --repo "$C2" --commit HEAD
[ "$(m verified.specified_share.status)" = fail ] && grep -q "undocumented" <<<"$(m verified.specified_share.reason)" && ran_case || fail "a carve-out with no ledger entry was accepted: $(m verified.specified_share.reason)"
C3=$T/co3; PROOF_EXTRA="$PX" mkfixture "$C3" "$(PROOF_EXTRA="$PX" adapter library 100 "$CL")"; mkco "$C3" 'findAvx2 | T13 | scripts/pinned-libs.lock' 'AGENTS.md' 'carveout_mass 36'; run --repo "$C3" --commit HEAD
[ "$(m verified.specified_share.status)" = fail ] && grep -q "protected" <<<"$(m verified.specified_share.reason)" && ran_case || fail "an unprotected carve-out was accepted: $(m verified.specified_share.reason)"
C4=$T/co4; PROOF_EXTRA="$PX" mkfixture "$C4" "$(PROOF_EXTRA="$PX" adapter library 100 'echo specified share 100.00%; echo closure gate: carve-outs: 40 nodes')"; mkco "$C4" 'findAvx2 | T13 | scripts/pinned-libs.lock' 'scripts/pinned-libs.lock' 'carveout_mass 36'; run --repo "$C4" --commit HEAD
[ "$(m verified.specified_share.status)" = fail ] && grep -q "grew" <<<"$(m verified.specified_share.reason)" && ran_case || fail "a widened carve-out (40 nodes over a baseline of 36) was accepted: $(m verified.specified_share.reason)"
C5=$T/co5; PROOF_EXTRA="$PX" mkfixture "$C5" "$(PROOF_EXTRA="$PX" adapter library 100 'echo specified share 99.77%; echo closure gate: carve-outs: 36 nodes')"; mkco "$C5" 'findAvx2 | T13 | scripts/pinned-libs.lock' 'scripts/pinned-libs.lock' 'carveout_mass 36'; run --repo "$C5" --commit HEAD
[ "$(m verified.specified_share.status)" = fail ] && [ "$(m verified.specified_share.value)" = 99.77 ] && ran_case || fail "a share below 100 outside the carve-outs passed"
C6=$T/co6; PROOF_EXTRA="$PX" mkfixture "$C6" "$(PROOF_EXTRA="$PX" adapter library 99.5 "$CL")"; run --repo "$C6" --commit HEAD
[ "$rc" != 0 ] && grep -q "carve-out" "$T/err" && ran_case || fail "a library floor below 100 was accepted (rc=$rc)"
C7=$T/co7; PROOF_EXTRA='carveouts_regex = "x"' mkfixture "$C7" "$(PROOF_EXTRA='carveouts_regex = "x"' adapter library 100 "$CL")"; run --repo "$C7" --commit HEAD
[ "$rc" != 0 ] && grep -q "carveouts" "$T/err" && ran_case || fail "carveouts_* keys without the list were accepted (rc=$rc)"
# 8. not-measurable fails the floor with a NAMED reason: no closure gate; unparseable closure output; a closure gate that fails; --no-exec; unmatched source globs
N=$T/nogate; mkfixture "$N" "$(adapter library 100 '')"; run --repo "$N" --commit HEAD
[ "$(m verified.specified_share.status)" = not-measurable ] && grep -q "no closure gate" <<<"$(m verified.specified_share.reason)" && [ "$(card dimensions.verified.status)" = fail ] && [ "$(card verdicts.correctness.status)" = fail ] && ran_case || fail "a subject without a closure gate was not not-measurable/failed: $(m verified.specified_share.reason)"
mkfixture "$N/../junk" "$(adapter library 100 'echo hello')"; run --repo "$T/junk" --commit HEAD; [ "$(m verified.specified_share.status)" = not-measurable ] && grep -q "did not match" <<<"$(m verified.specified_share.reason)" && ran_case || fail "unparseable closure output was not not-measurable"
mkfixture "$T/gatefail" "$(adapter library 100 'echo specified share 100%; exit 3')"; run --repo "$T/gatefail" --commit HEAD; [ "$(m verified.specified_share.status)" = fail ] && grep -q "exited 3" <<<"$(m verified.specified_share.reason)" && ran_case || fail "a failing closure gate did not fail"
# 8b. the subject is untrusted: with NO launcher nothing of it executes (a marker the subject's commands would create is absent); with the launcher it is created (positive control), and the launcher is called as the contract says
MK=$T/marker; mkfixture "$T/untrusted" "$(adapter library 100 "touch $MK; echo specified share 100%" | sed "s#^command = \"echo selftest alpha ok; echo ran: alpha: 3 cases\"#command = \"touch $MK.t1\"#")"
sbargs=(); run --repo "$T/untrusted" --commit HEAD; sbargs=(--sandbox "$T/fake")
[ ! -e "$MK" ] && [ ! -e "$MK.t1" ] && [ "$(m verified.specified_share.status)" = not-measurable ] && [ "$(m velocity.tier1_seconds_cold.status)" = not-measurable ] && grep -q "no launcher is configured" <<<"$(m velocity.tier1_seconds_cold.reason)" && [ "$(card sandbox)" = null ] && ran_case || fail "subject code executed (or was not refused) without a sandbox launcher"
rm -f "$T/launch.args"; SECRET_TOKEN=hunter2 run --repo "$T/untrusted" --commit HEAD; [ -e "$MK" ] && [ -e "$MK.t1" ] && ran_case || fail "positive control: the launcher did not run the subject's commands"
grep -q -- "--net none" "$T/launch.args" && grep -q -- "--subject $TMPDIR" "$T/launch.args" && ! grep -q -- "--subject $T/untrusted" "$T/launch.args" && ran_case || fail "the launcher was not given the scratch clone, read-only contract and --net none: $(cat "$T/launch.args")"
! grep -q hunter2 "$T/launch.env" && [ "$(grep -c '^' "$T/launch.env")" -le 6 ] && ran_case || fail "the launcher inherited the caller's environment: $(cat "$T/launch.env")"
[ "$(card sandbox.attestations.0.network)" = none ] && [ "$(card sandbox.limits.memory_mb)" = 4096 ] && [ "${#sha}" = 40 ] && [ "$(card sandbox.launcher_sha256 | wc -c)" = 65 ] && ran_case || fail "the card does not record the attestation, limits and launcher hash"
# 8c. an attestation that is missing, claims the network, or carries other limits than asked: the result is not trusted (not-measurable)
for mode in noatt net limits; do echo $mode > "$T/mode"; run --repo "$T/untrusted" --commit HEAD; [ "$(m verified.specified_share.status)" = not-measurable ] && grep -q "attestation" <<<"$(m verified.specified_share.reason)" && ran_case || fail "a $mode attestation was trusted: $(m verified.specified_share.reason)"; done
mkfixture "$T/hangfix" "$(adapter | sed 's/timeout_seconds = 60/timeout_seconds = 1/')"; echo hang > "$T/mode"; s0=$SECONDS; SCORECARD_GRACE_SECONDS=1 run --repo "$T/hangfix" --commit HEAD; [ "$(m velocity.tier1_seconds_cold.status)" = fail ] && grep -q "timed out" <<<"$(m velocity.tier1_seconds_cold.reason)" && [ $((SECONDS - s0)) -lt 30 ] && ran_case || fail "a launcher that ignores its timeout was not killed by the runner (took $((SECONDS - s0)) s)"
rm -f "$T/mode"
mkfixture "$T/flood" "$(adapter | sed 's/^command = "echo selftest alpha ok; echo ran: alpha: 3 cases"/command = "yes"/')"; s0=$SECONDS; run --repo "$T/flood" --commit HEAD; [ "$(m velocity.tier1_seconds_cold.status)" = fail ] && [ $((SECONDS - s0)) -lt 20 ] && ran_case || fail "an endless output was not cut off (took $((SECONDS - s0)) s)"
sed 's#src/\*\*/\*.lean#nowhere/*.lean#' "$G2/scorecard.toml" > "$T/nw.toml"; run --repo "$G2" --commit "$s2" --adapter "$T/nw.toml"; [ "$(m verified.unproved_escapes.status)" = not-measurable ] && ran_case || fail "an empty source scan passed (zero findings of nothing is not zero sorry)"
# 9. tier 1: a failing command fails; a timeout fails fast; the warm floor is strictly under 60 s, the cold ceiling is 600 s
mkfixture "$T/t1bad" "$(adapter | sed 's/^command = "echo selftest alpha ok; echo ran: alpha: 3 cases"/command = "exit 7"/')"; run --repo "$T/t1bad" --commit HEAD; [ "$(m velocity.tier1_seconds_cold.status)" = fail ] && grep -q "exited 7" <<<"$(m velocity.tier1_seconds_cold.reason)" && [ "$(card dimensions.velocity.status)" = fail ] && ran_case || fail "a failing tier1 did not fail"
mkfixture "$T/t1slow" "$(adapter | sed 's/^command = "echo selftest alpha ok; echo ran: alpha: 3 cases"/command = "sleep 30"/; /^\[tier1\]/,/^\[velocity\]/ s/timeout_seconds = 60/timeout_seconds = 1/')"; s0=$SECONDS; run --repo "$T/t1slow" --commit HEAD
[ "$(m velocity.tier1_seconds_cold.status)" = fail ] && grep -q "timed out" <<<"$(m velocity.tier1_seconds_cold.reason)" && [ $((SECONDS - s0)) -lt 15 ] && ran_case || fail "a tier1 timeout was not a fast fail (took $((SECONDS - s0)) s)"
python3 - "$sc" <<'PY' && ran_case || fail "the tier-1 floors are wrong (warm strictly under 60 s, cold at most 600 s)"
import importlib.machinery, importlib.util, sys
l = importlib.machinery.SourceFileLoader("sc", sys.argv[1]); s = importlib.util.spec_from_loader("sc", l); m = importlib.util.module_from_spec(s); l.exec_module(m)
w = next(x for x in m.METRICS if x["id"] == "velocity.tier1_seconds_warm"); c = next(x for x in m.METRICS if x["id"] == "velocity.tier1_seconds_cold")
assert [m.judge(w, v, {})[0] for v in (0, 59.9, 60, 61)] == ["pass", "pass", "fail", "fail"]
assert [m.judge(c, v, {})[0] for v in (0, 494.5, 600, 600.1, 700)] == ["pass", "pass", "pass", "fail", "fail"]   # a CEILING: 600 itself passes
assert w["dim"] == c["dim"] == "velocity" and "velocity.tier1_seconds" not in [x["id"] for x in m.METRICS]   # the one metric is retired, not kept beside the two
PY
# 9b. the warm/cold split (DECISIONS 17): the card prints BOTH, each timed by the runner on its own phase; neither is hidden or averaged
WS=$T/warmslow; mkfixture "$WS" "$(adapter | sed 's/^warm_command = .*/warm_command = "sleep 2; echo selftest alpha ok; echo ran: alpha: 3 cases"/')"; run --repo "$WS" --commit HEAD
python3 -c 'import os,json; c=json.load(open(os.environ["T"]+"/card.json")); d={m["id"]:m for m in c["metrics"]}; w,k=d["velocity.tier1_seconds_warm"],d["velocity.tier1_seconds_cold"]; assert 2 <= w["value"] < 15 and k["value"] < 2 and w["status"]==k["status"]=="pass" and w["measured"] and k["measured"], (w,k); assert w["gates_shown"]==["alpha"] and w["gates_skipped"]==[]' && ran_case || fail "the warm and cold seconds are not timed apart (a 2 s warm gate must read about 2 s warm and under 2 s cold)"
# a forged phase line (no nonce) is only output: it cannot move a timing
WF=$T/warmforge; mkfixture "$WF" "$(adapter | sed "s/^warm_command = .*/warm_command = \"sleep 2; printf '\\\\\\\\n@@scorecard abcdef warm-end 0\\\\\\\\n'; echo selftest alpha ok; echo ran: alpha: 3 cases\"/")"; run --repo "$WF" --commit HEAD
[ "$(python3 -c 'import os,json; c=json.load(open(os.environ["T"]+"/card.json")); print(next(m for m in c["metrics"] if m["id"]=="velocity.tier1_seconds_warm")["value"] >= 2)')" = True ] && ran_case || fail "negative self-test: a forged phase line without the run's nonce moved the warm time"
# ... and one that KNOWS the nonce (read from its parent's command line) and prints a late start and an early end line still cannot shorten the phase: the first start and the last end of a phase count
WN=$T/warmnonce; mkfixture "$WN" "$(adapter | sed 's|^warm_command = .*|warm_command = "bash scripts/forge.sh"|')"
cat > "$WN/scripts/forge.sh" <<'SH'
p=$$; N=
while [ -z "$N" ] && [ "$p" -gt 1 ]; do N=$(tr '\0' ' ' < /proc/$p/cmdline 2>/dev/null | grep -o '@@scorecard [0-9a-f]\{16\}' | head -1 || true); p=$(ps -o ppid= -p "$p" | tr -d ' '); done
[ -n "$N" ] || { echo "forge: no nonce found" >&2; exit 9; }
printf '\n%s warm-end 0\n' "$N"; sleep 2; printf '\n%s warm-start 0\n' "$N"; echo selftest alpha ok; echo ran: alpha: 3 cases
SH
git -C "$WN" add -A; git -C "$WN" commit -qm "feat(fix): forger"; run --repo "$WN" --commit HEAD
[ "$(python3 -c 'import os,json; c=json.load(open(os.environ["T"]+"/card.json")); print(next(m for m in c["metrics"] if m["id"]=="velocity.tier1_seconds_warm")["value"] >= 2)')" = True ] && ran_case || fail "negative self-test: a subject that knows the nonce and prints a late start and an early end line shortened the warm time"
# the SABOTAGE tests: a regression in warm time fails the card (landedness only); a cold run past the ceiling fails it too (landedness only); the good run, unshifted, passes (fixture 5)
sab() {   # sab LABEL SECONDS REPO: run the real runner and the real launcher fixture, then move the arrival time of the phase-end line LABEL later by SECONDS (a slow gate), as the clock would have
  python3 - "$sc" "$1" "$2" "$3" "$T" <<'PY'
import importlib.machinery, importlib.util, sys, os
l = importlib.machinery.SourceFileLoader("sc", sys.argv[1]); s = importlib.util.spec_from_loader("sc", l); m = importlib.util.module_from_spec(s); l.exec_module(m)
label, shift, repo, T = sys.argv[2], float(sys.argv[3]), sys.argv[4], sys.argv[5]; real = m.sh
def slow(argv, timeout, env, cwd=None, nonce=None, marks=None):
    rc, out, secs = real(argv, timeout, env, cwd, nonce, marks)
    for i, (lb, r, t) in enumerate(marks or []):
        if lb == label: marks[i] = (lb, r, t + shift)
    return rc, out, secs
m.sh = slow; os.environ["SCORECARD_GRACE_SECONDS"] = "2"
sys.exit(m.main(["run", "--repo", repo, "--commit", "HEAD", "--allowlist", T + "/allow.toml", "--sandbox", T + "/fake", "--out", T + "/card.json"]))
PY
}
SB=$T/sabotage; mkfixture "$SB"
sab warm-end 61 "$SB" && ran_case || fail "sabotage: the runner failed"
[ "$(m velocity.tier1_seconds_warm.status)" = fail ] && [ "$(m velocity.tier1_seconds_cold.status)" = pass ] && [ "$(card dimensions.velocity.status)" = fail ] && [ "$(card verdicts.landedness.status)" = fail ] && [ "$(card verdicts.correctness.status)" = pass ] && ran_case || fail "SABOTAGE: a warm gate 61 s slower did not fail Landedness alone: $(card verdicts)"
sab warm-end 59 "$SB" && ran_case || fail "sabotage: the runner failed"
[ "$(m velocity.tier1_seconds_warm.status)" = pass ] && [ "$(card verdicts.landedness.status)" = pass ] && ran_case || fail "a warm gate 59 s slower (under the floor) failed"
sab cold-end 601 "$SB" && ran_case || fail "sabotage: the runner failed"
[ "$(m velocity.tier1_seconds_cold.status)" = fail ] && [ "$(m velocity.tier1_seconds_warm.status)" = pass ] && [ "$(card verdicts.landedness.status)" = fail ] && [ "$(card verdicts.correctness.status)" = pass ] && ran_case || fail "SABOTAGE: a cold run past the 600 s ceiling did not fail Landedness alone: $(card verdicts)"
sab cold-end 599 "$SB" && ran_case || fail "sabotage: the runner failed"
[ "$(m velocity.tier1_seconds_cold.status)" = pass ] && [ "$(card verdicts.landedness.status)" = pass ] && ran_case || fail "a cold run of 599 s (under the ceiling) failed"
# negative self-tests: no warm run declared is not-measurable (fails the floor); a warm gate that exits 0 WITHOUT showing the gates ran fails; naming the skip makes it pass and is on the card; a failing warm gate, a failing typical change and a failing cold run each fail the warm metric
NW=$T/nowarm; mkfixture "$NW" "$(adapter | sed '/^warm_/d')"; run --repo "$NW" --commit HEAD
[ "$(m velocity.tier1_seconds_warm.status)" = not-measurable ] && grep -q "no warm run" <<<"$(m velocity.tier1_seconds_warm.reason)" && [ "$(card verdicts.landedness.status)" = fail ] && [ "$(m velocity.tier1_seconds_cold.status)" = pass ] && ran_case || fail "a subject with no warm run was not not-measurable (and so failing Landedness)"
EW=$T/emptywarm; mkfixture "$EW" "$(adapter | sed 's/^warm_command = .*/warm_command = "true"/')"; run --repo "$EW" --commit HEAD
[ "$(m velocity.tier1_seconds_warm.status)" = fail ] && grep -q "without the self-test evidence of: alpha" <<<"$(m velocity.tier1_seconds_warm.reason)" && ran_case || fail "negative self-test: a warm gate that ran nothing (true) passed"
SK=$T/skipwarm; mkfixture "$SK" "$(adapter | sed 's/^warm_command = .*/warm_command = "true"/; s/^gates = \[{ name = "alpha", selftest = "selftest alpha ok" }\]/gates = [{ name = "alpha", selftest = "selftest alpha ok" }, { name = "beta", selftest = "selftest beta ok" }]\nwarm_skips = ["beta"]/')"; run --repo "$SK" --commit HEAD
[ "$(m velocity.tier1_seconds_warm.status)" = fail ] && grep -q "evidence of: alpha" <<<"$(m velocity.tier1_seconds_warm.reason)" && ran_case || fail "a skipped gate hid the evidence of a gate that was not skipped"
rm -rf "$SK"; mkfixture "$SK" "$(adapter | sed 's/^warm_command = .*/warm_command = "echo selftest alpha ok; echo ran: alpha: 3 cases"/; s/^gates = \[{ name = "alpha", selftest = "selftest alpha ok" }\]/gates = [{ name = "alpha", selftest = "selftest alpha ok" }, { name = "beta", selftest = "selftest beta ok" }]\nwarm_skips = ["beta"]/')"; run --repo "$SK" --commit HEAD
[ "$(m velocity.tier1_seconds_warm.status)" = pass ] && [ "$(m velocity.tier1_seconds_warm.gates_skipped)" = '["beta"]' ] && [ "$(m velocity.tier1_seconds_warm.gates_shown)" = '["alpha"]' ] && ran_case || fail "a named warm skip was not honoured and reported on the card"
for k in 's/^warm_command = .*/warm_command = "echo selftest alpha ok; echo ran: alpha: 3 cases; exit 3"/|exited 3' 's/^warm_change_cmd = .*/warm_change_cmd = "exit 5"/|typical change'; do
  F=$T/warmbad; rm -rf "$F"; mkfixture "$F" "$(adapter | sed "${k%%|*}")"; run --repo "$F" --commit HEAD
  [ "$(m velocity.tier1_seconds_warm.status)" = fail ] && grep -q "${k##*|}" <<<"$(m velocity.tier1_seconds_warm.reason)" && [ "$(card verdicts.landedness.status)" = fail ] && ran_case || fail "a warm failure (${k##*|}) did not fail the warm metric: $(m velocity.tier1_seconds_warm.reason)"; done
CB=$T/coldbad; mkfixture "$CB" "$(adapter | sed 's/^command = "echo selftest alpha ok; echo ran: alpha: 3 cases"/command = "exit 7"/')"; run --repo "$CB" --commit HEAD
[ "$(m velocity.tier1_seconds_warm.status)" = fail ] && grep -q "cold run" <<<"$(m velocity.tier1_seconds_warm.reason)" && [ "$(m velocity.tier1_seconds_cold.status)" = fail ] && ran_case || fail "a failing cold run left a warm number (the cache was never primed)"
# the adapter: a warm run is declared whole, with gates, and cannot skip every gate
for bad in '/^warm_change_cmd/d|declared together' '/^warm_command/d|declared together' 's/^warm_timeout_seconds = 60/warm_timeout_seconds = 0/|warm_timeout_seconds must be' 's/^warm_timeout_seconds = 60/warm_timeout_seconds = 5000/|warm_timeout_seconds must be' 's/^gates = .*/gates = []/|needs .tier1. gates' 's/^gates = .*/&\nwarm_skips = ["nope"]/|warm_skips names declared gates only' 's/^gates = .*/&\nwarm_skips = ["alpha"]/|cannot name every gate'; do
  adapter | sed "${bad%%|*}" > "$T/bad.toml"; run --repo "$G" --commit "$sha" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "${bad##*|}" "$T/err" && ran_case || fail "a bad warm declaration (${bad%%|*}) was not rejected (exit $rc): $(cat "$T/err")"; done
# 10. hand-written tests by the DECISIONS 5 definition: listed by file; generated vectors and unmatched files excluded; tests.extra adds; the generated list cannot be used on a test outside it
H=$T/tests; mkfixture "$H" "$(adapter | sed 's#^extra = \[\]#extra = ["extras/*.check"]#')"
( cd "$H"; mkdir -p tests extras vectors/jts scripts/sub; echo x > tests/abi_test.c; echo x > scripts/test_thing.sh; echo x > src/FooTest.lean; echo x > cli.golden; echo x > extras/a.check; echo x > extras/b.txt; echo x > vectors/jts/y_test.json; echo x > scripts/sub/not_a_t.sh; git add -A; git commit -qm "feat(fix): tests" )
run --repo "$H" --commit HEAD; [ "$(m construction.hand_written_tests.files)" = '["cli.golden", "extras/a.check", "src/FooTest.lean", "tests/abi_test.c"]' ] && [ "$(m construction.hand_written_tests.value)" = 4 ] && [ "$(m construction.hand_written_tests.gate_selftests_excluded)" = 2 ] && [ "$(m construction.hand_written_tests.status)" = fail ] && ran_case || fail "hand-written tests miscounted: $(m construction.hand_written_tests.files)"
[ "$(card dimensions.construction.status)" = fail ] && ran_case || fail "hand-written tests did not fail the construction dimension"
# 10a. CASE LITERALS: with entry_points declared, a test file counts the calls to them that carry a string/bytes literal; a DRIVER that only loads generated vectors (variables in its arguments) has 0 cases and is listed as a driver;
# a definition of the entry point is not a call; nested literals count once per call; with no entry_points every candidate file is one case (nothing is waved through)
CL=$T/cases; mkfixture "$CL" "$(ENTRY_POINTS='"parse", "lib_parse"' adapter)"
( cd "$CL"; mkdir -p tests; cat > tests/driver.py <<'PY'
import sys, json
for line in open(sys.argv[1]):
    r = json.loads(line); data = bytes.fromhex(r["input"]); v = parse(data)
    assert verdict(v) == r["verdict"], "message with a [literal] in it"
PY
cat > tests/cases.py <<'PY'
def parse(x): return x
assert parse(b"[1]") == 1
assert vbm.parse(enc.encode('{"a":'.repeat(3)), strict=True) == 2
assert parse(variable_only) == 3
PY
git add -A; git commit -qm "feat(fix): a driver and a case file" ); run --repo "$CL" --commit HEAD
[ "$(m construction.hand_written_tests.value)" = 2 ] && [ "$(m construction.hand_written_tests.cases_by_file)" = '{"tests/cases.py": 2}' ] && [ "$(m construction.hand_written_tests.drivers)" = '["tests/driver.py"]' ] && [ "$(m construction.hand_written_tests.status)" = fail ] && ran_case || fail "case literals were not counted per file (driver 0, definition and variable-only calls not counted): $(m construction.hand_written_tests.cases_by_file) / $(m construction.hand_written_tests.drivers)"
( cd "$CL"; git rm -q tests/cases.py; git commit -qm "feat(fix): drivers only" ); run --repo "$CL" --commit HEAD; [ "$(m construction.hand_written_tests.value)" = 0 ] && [ "$(m construction.hand_written_tests.status)" = pass ] && ran_case || fail "a repo with drivers only did not score 0 hand-written cases"
( cd "$CL"; printf 'import x\nr = run_all()\n' > tests/scenario.py; git add -A; git commit -qm "feat(fix): a scenario file" ); mkfixture "$T/sc" "$(ENTRY_POINTS='"parse"' SCENARIO_FILES='"tests/scenario.py"' adapter)"; ( cd "$T/sc"; mkdir -p tests; cp "$CL/tests/scenario.py" tests/; git add -A; git commit -qm "feat(fix): scenario" ); run --repo "$T/sc" --commit HEAD
[ "$(m construction.hand_written_tests.value)" = 1 ] && [ "$(m construction.hand_written_tests.cases_by_file)" = '{"tests/scenario.py": 1}' ] && ran_case || fail "a declared scenario file (inputs built in code) was not counted as a case"
mkfixture "$T/nep" "$(adapter)"; ( cd "$T/nep"; mkdir -p tests; cp "$CL/tests/driver.py" tests/driver.py; git add -A; git commit -qm "feat(fix): a driver" ); run --repo "$T/nep" --commit HEAD; [ "$(m construction.hand_written_tests.value)" = 1 ] && ran_case || fail "without entry_points a test file was not counted as one case"
# 10b. gate self-tests (process honesty): the good fixture's one self-test is named by its fast gate (100%); one the gate does not name is under 100 and FAILS the dimension; none at all is not-measurable and fails;
# a self-test glob outside scripts/ is rejected (a subject cannot declare its own test directory "gate self-tests"); an unreadable fast-gate script is not-measurable
run --repo "$G2" --commit "$s2"; [ "$(m honesty.gate_selftests.value)" = 100.0 ] && [ "$(m honesty.gate_selftests.status)" = pass ] && ran_case || fail "a named gate self-test did not count: $(m honesty.gate_selftests.value)"
U=$T/unnamed; mkfixture "$U"; ( cd "$U"; echo 'echo y' > scripts/test_y.sh; git add -A; git commit -qm "feat(fix): a self-test the gate does not run" ); run --repo "$U" --commit HEAD
[ "$(m honesty.gate_selftests.value)" = 50.0 ] && [ "$(m honesty.gate_selftests.status)" = fail ] && [ "$(m honesty.gate_selftests.not_named_by_the_fast_gate)" = '["scripts/test_y.sh"]' ] && [ "$(card dimensions.honesty.status)" = fail ] && ran_case || fail "a self-test the fast gate does not name was not penalised: $(m honesty.gate_selftests.value)"
NS=$T/noselftest; mkfixture "$NS"; ( cd "$NS"; git rm -q scripts/test_x.sh; git commit -qm "feat(fix): no self-tests" ); run --repo "$NS" --commit HEAD; [ "$(m honesty.gate_selftests.status)" = not-measurable ] && [ "$(card dimensions.honesty.status)" = fail ] && ran_case || fail "a subject with no gate self-tests passed process honesty"
adapter | sed 's#gate_selftests = \["scripts/test_\*.sh"\]#gate_selftests = ["tests/**"]#' > "$T/bad.toml"; run --repo "$G2" --commit "$s2" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "must be under scripts/" "$T/err" && ran_case || fail "a gate_selftests glob outside scripts/ was accepted"
NG=$T/nogate2; mkfixture "$NG"; ( cd "$NG"; git rm -q scripts/tier1.sh; git commit -qm "feat(fix): no fast gate" ); run --repo "$NG" --commit HEAD; [ "$(m honesty.gate_selftests.status)" = not-measurable ] && grep -q "not readable" <<<"$(m honesty.gate_selftests.reason)" && ran_case || fail "an unreadable fast-gate script was accepted"
# 11. trusted C and the ledger: counted; a missing ledger is not-measurable
rm "$G2/docs/trust-ledger.md"; git -C "$G2" commit -qam "feat(fix): no ledger"; run --repo "$G2" --commit HEAD; [ "$(m verified.trust_ledger_entries.status)" = not-measurable ] && ran_case || fail "a missing trust ledger was counted"
# 12. open PRs: 2 open fails the floor; a gh failure and a subject without a GitHub origin are not-measurable
OP=$T/prs; echo '[{"number":1},{"number":2}]' > "$T/prs"; run --repo "$G" --commit "$sha"; [ "$(m velocity.open_prs.value)" = 2 ] && [ "$(m velocity.open_prs.status)" = fail ] && ran_case || fail "two open PRs did not fail the floor"
printf '#!/bin/sh\necho boom >&2; exit 1\n' > "$T/gh"; run --repo "$G" --commit "$sha"; [ "$(m velocity.open_prs.status)" = not-measurable ] && grep -q boom <<<"$(m velocity.open_prs.reason)" && ran_case || fail "a gh failure was not not-measurable"
run --repo "$T/bare" --commit HEAD --adapter "$G/scorecard.toml"; [ "$(m velocity.open_prs.status)" = not-measurable ] && grep -q "no GitHub origin" <<<"$(m velocity.open_prs.reason)" && ran_case || fail "a subject without an origin was measured"
printf '#!/bin/sh\ncat "$T/prs"\n' > "$T/gh"; echo '[]' > "$T/prs"
# 13. commits per hour and p90 commit-to-main, from git: three commits (author dates 0/0/600 s before committer), one old commit outside the 168 h window
V=$T/vel; base=1700000000; GIT_AUTHOR_DATE="$(( base - 40 * 86400 )) +0000" GIT_COMMITTER_DATE="$(( base - 40 * 86400 )) +0000" mkfixture "$V"; ( cd "$V"
  c() { echo "$1" > "f$1"; git add -A; GIT_AUTHOR_DATE="$(( $2 - $3 )) +0000" GIT_COMMITTER_DATE="$2 +0000" git commit -qm "feat(fix): c$1"; }
  c 0 $(( base - 30 * 86400 )) 99999; c 1 $base 0; c 2 $(( base + 1800 )) 0; c 3 $(( base + 3600 )) 600 )
run --repo "$V" --commit HEAD; [ "$(m velocity.commits_per_hour.value)" = 3.0 ] && [ "$(m velocity.commits_per_hour.commits)" = 3 ] && ran_case || fail "commits per hour from git: $(m velocity.commits_per_hour.value) (c0 and the fixture commit are outside the window)"
[ "$(m velocity.p90_commit_to_main_seconds.value)" = 600 ] && [ "$(m velocity.p90_commit_to_main_seconds.changes)" = 3 ] && ran_case || fail "p90 from author to landing date: $(m velocity.p90_commit_to_main_seconds.value) over $(m velocity.p90_commit_to_main_seconds.changes) changes"
# a change of two commits landed 5 s apart is ONE change, measured from its FIRST authored commit (900 s before the first landing) to its last landing; a change authored and landed at once reads 0
B=$T/batch; GIT_AUTHOR_DATE="$(( base - 40 * 86400 )) +0000" GIT_COMMITTER_DATE="$(( base - 40 * 86400 )) +0000" mkfixture "$B"; ( cd "$B"
  c() { echo "$1" > "f$1"; git add -A; GIT_AUTHOR_DATE="$2 +0000" GIT_COMMITTER_DATE="$3 +0000" git commit -qm "feat(fix): c$1"; }
  c y $base $base; c x1 $(( base + 4000 - 900 )) $(( base + 4000 )); c x2 $(( base + 4000 - 30 )) $(( base + 4005 )) )
run --repo "$B" --commit HEAD; [ "$(m velocity.p90_commit_to_main_seconds.value)" = 905 ] && [ "$(m velocity.p90_commit_to_main_seconds.changes)" = 2 ] && ran_case || fail "a two-commit change was not measured from its first authored commit: $(m velocity.p90_commit_to_main_seconds.value)"
# every change reading 0 (a squash-merge or commit-on-main history) is not-measurable with its reason, never a silent zero
Z=$T/zero; mkfixture "$Z"; run --repo "$Z" --commit HEAD; [ "$(m velocity.p90_commit_to_main_seconds.status)" = not-measurable ] && [ "$(m velocity.p90_commit_to_main_seconds.value)" = null ] && grep -q "no authoring start" <<<"$(m velocity.p90_commit_to_main_seconds.reason)" && ran_case || fail "an all-zero history was not not-measurable: $(m velocity.p90_commit_to_main_seconds.value)"
# 14. static metrics read only declared files, through one guard: a symlink (to a file outside the subject, with a placeholder in it) is not followed, an oversized file is skipped, both are reported
echo 'theorem t : True := by sorry' > "$T/outside.lean"; SY=$T/symlinks; mkfixture "$SY"; ( cd "$SY"; ln -s "$T/outside.lean" src/Link.lean; truncate -s 6M src/Big.lean; git add -A; git commit -qm "feat(fix): symlink and big file" )
run --repo "$SY" --commit HEAD; [ "$(m verified.unproved_escapes.value)" = 0 ] && [ "$(m verified.unproved_escapes.files_scanned)" = 1 ] && ran_case || fail "a symlinked or oversized file was read: $(m verified.unproved_escapes.findings)"
grep -q 'src/Link.lean: a symlink' <<<"$(card skipped_files)" && grep -q 'src/Big.lean: over' <<<"$(card skipped_files)" && ran_case || fail "skipped files are not reported: $(card skipped_files)"
( cd "$SY"; git rm -q --cached docs/trust-ledger.md; rm docs/trust-ledger.md; ln -s "$T/outside.lean" docs/trust-ledger.md; git add -A; git commit -qm "feat(fix): symlinked ledger" ); run --repo "$SY" --commit HEAD; [ "$(m verified.trust_ledger_entries.status)" = not-measurable ] && ran_case || fail "a symlinked ledger was read"
# 15. declared paths that escape are rejected with the adapter: absolute, `..`, in every path key
for sub in 's#"src/\*\*/\*.lean"#"../x/*.lean"#' 's#"c/\*.c"#"/etc/*"#' 's#"docs/trust-ledger.md"#"../../etc/passwd"#' 's#generated = \["vectors/\*\*"\]#generated = ["a/../b"]#'; do
  adapter | sed "$sub" > "$T/bad.toml"; cmp -s "$T/bad.toml" <(adapter) && fail "the escape fixture did not change the adapter: $sub"; run --repo "$G" --commit "$sha" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "not allowed" "$T/err" && ran_case || fail "an escaping declared path was accepted ($sub): $(cat "$T/err")"; done
# 16. a hostile adapter regex (catastrophic backtracking on a crafted ledger line) is stopped by the alarm: not-measurable, quickly, the rest of the card still produced
RX=$T/redos; mkfixture "$RX" "$(adapter | sed 's/entry_regex = .*/entry_regex = "(a+)+$"/')"; ( cd "$RX"; python3 -c 'print("a" * 60 + "!")' > docs/trust-ledger.md; git commit -qam "feat(fix): hostile ledger" )
s0=$SECONDS; SCORECARD_METRIC_SECONDS=2 run --repo "$RX" --commit HEAD; [ "$rc" = 0 ] && [ "$(m verified.trust_ledger_entries.status)" = not-measurable ] && grep -q "ran over" <<<"$(m verified.trust_ledger_entries.reason)" && [ $((SECONDS - s0)) -lt 20 ] && [ "$(m verified.unproved_escapes.status)" = pass ] && ran_case || fail "a catastrophic regex was not stopped (took $((SECONDS - s0)) s)"
# 17. executing metrics through the launcher: non-standard axioms (read from the subject's axiom gate), the freestanding build, libc symbols. Each fails on its planted violation, and each silent or garbled
# output is not-measurable, never zero. (The fake launcher runs our own fixtures on the host; real subjects only ever go through scorecard/sandbox-bwrap.)
ax() { local d=$T/ax$1; mkfixture "$d" "$(AXIOM_CMD="$2" BUILD_CMD="${3-true}" SYMBOLS_CMD="${4-echo --end-of-symbols--}" ALLOWED_SYMBOLS="${5-}" adapter)"; run --repo "$d" --commit HEAD; }
ax 1 'echo axiom gate: 9 constants checked, 2 offending'; [ "$(m verified.nonstandard_axioms.value)" = 2 ] && [ "$(m verified.nonstandard_axioms.status)" = fail ] && [ "$(card dimensions.verified.status)" = fail ] && ran_case || fail "a non-standard axiom was not counted and failed"
ax 2 'echo axiom gate: 9 constants checked, 0 offending'; [ "$(m verified.nonstandard_axioms.value)" = 0 ] && [ "$(m verified.nonstandard_axioms.status)" = pass ] && ran_case || fail "a clean axiom gate did not pass"
ax 3 'echo axiom gate: 4 constants checked, 1 offending; exit 1'; [ "$(m verified.nonstandard_axioms.value)" = 1 ] && ran_case || fail "a failing axiom gate that prints its count was not read"
ax 4 'exit 1'; [ "$(m verified.nonstandard_axioms.status)" = fail ] && grep -q "printed no count" <<<"$(m verified.nonstandard_axioms.reason)" && ran_case || fail "an axiom gate that dies silently was not a fail"
ax 5 'echo garbage'; [ "$(m verified.nonstandard_axioms.status)" = not-measurable ] && ran_case || fail "unparseable axiom output was not not-measurable"
ax 6 ''; [ "$(m verified.nonstandard_axioms.status)" = not-measurable ] && grep -q "no axiom gate" <<<"$(m verified.nonstandard_axioms.reason)" && ran_case || fail "no axiom gate was not not-measurable"
ax 7 'echo axiom gate: 1 constants checked, 0 offending' true; [ "$(m bare_metal.freestanding_build.value)" = 1 ] && [ "$(m bare_metal.freestanding_build.status)" = pass ] && ran_case || fail "a passing freestanding build did not pass"
ax 8 'echo axiom gate: 1 constants checked, 0 offending' 'echo no libc headers >&2; exit 1'; [ "$(m bare_metal.freestanding_build.value)" = 0 ] && [ "$(m bare_metal.freestanding_build.status)" = fail ] && [ "$(card dimensions.bare_metal.status)" = fail ] && ran_case || fail "a failing freestanding build did not fail"
ax 9 'echo axiom gate: 1 constants checked, 0 offending' true 'printf "malloc\nmemcpy@GLIBC_2.14\nmemcpy\n--end-of-symbols--\n"'; [ "$(m bare_metal.libc_symbols.value)" = 2 ] && [ "$(m bare_metal.libc_symbols.symbols)" = '["malloc", "memcpy"]' ] && [ "$(m bare_metal.libc_symbols.status)" = fail ] && ran_case || fail "libc symbols were not counted (distinct, version stripped): $(m bare_metal.libc_symbols.value)"
ax 10 'echo axiom gate: 1 constants checked, 0 offending' true 'printf "malloc\nmemcpy\n--end-of-symbols--\n"' '"malloc", "memcpy"'; [ "$(m bare_metal.libc_symbols.value)" = 0 ] && [ "$(m bare_metal.libc_symbols.status)" = pass ] && ran_case || fail "the named allowed symbols were not subtracted"
ax 11 'echo axiom gate: 1 constants checked, 0 offending' true 'echo malloc'; [ "$(m bare_metal.libc_symbols.status)" = not-measurable ] && grep -q "silent failure" <<<"$(m bare_metal.libc_symbols.reason)" && ran_case || fail "a symbols command with no end marker read as a number"
wa() { local d=$T/wa$1; mkfixture "$d" "$(WASM_CMD="$2" adapter)"; run --repo "$d" --commit HEAD; }
wa 1 ''; ! grep -q wasm_freestanding_build "$T/card.json" && ran_case || fail "a wasm metric was listed for an adapter that declares no wasm target"
wa 2 'echo wasm bytes: 60740'; [ "$(m bare_metal.wasm_freestanding_build.value)" = 1 ] && [ "$(m bare_metal.wasm_freestanding_build.bytes)" = 60740 ] && [ "$(m bare_metal.wasm_freestanding_build.status)" = pass ] && ran_case || fail "a passing wasm build was not read with its size"
wa 3 'echo no clang >&2; exit 1'; [ "$(m bare_metal.wasm_freestanding_build.value)" = 0 ] && [ "$(m bare_metal.wasm_freestanding_build.status)" = fail ] && [ "$(card dimensions.bare_metal.status)" = fail ] && ran_case || fail "a failing wasm build did not fail the bare-metal dimension"
python3 -c 'import json,sys;c=json.load(open(sys.argv[1]));assert c["subject"]["commit_date"][:4].isdigit() and "T" in c["subject"]["commit_date"]' "$T/card.json" && ran_case || fail "the card does not carry the subject commit date"
ax 12 'echo axiom gate: 1 constants checked, 0 offending' true 'exit 3'; [ "$(m bare_metal.libc_symbols.status)" = not-measurable ] && ran_case || fail "a dead symbols command read as zero"
sbargs=(); run --repo "$T/ax1" --commit HEAD; sbargs=(--sandbox "$T/fake"); [ "$(m verified.nonstandard_axioms.status)" = not-measurable ] && grep -q "no launcher" <<<"$(m verified.nonstandard_axioms.reason)" && [ "$(m bare_metal.libc_symbols.status)" = not-measurable ] && ran_case || fail "the new executing metrics ran without a sandbox launcher"
# 18. code mutation: the scorecard's operator swaps at seeded sites of the declared files, run against the adapter's harness (in the sandbox). The good fixture's harness kills its only mutant; a weak harness lets one
# survive (50%) and FAILS the floor; a harness that fails on the unmutated subject, no harness, no sites, only non-viable mutants are not-measurable; comments and strings are not mutated; the budget and seed are honoured
mu() { local d=$T/mu$1; mkfixture "$d" "$(MUT_KILL="${3-grep -q \"a < b\" mut/ops.c}" MUT_N="${4-50}" MUT_SEED="${5-7}" adapter)"; ( cd "$d"; printf '%b' "$2" > mut/ops.c; git add -A; git commit -q --allow-empty -m "feat(fix): ops" ); run --repo "$d" --commit HEAD; }
mu 1 'int lt(int a, int b) { return a < b; }\n'; [ "$(m construction.mutation_score.value)" = 100.0 ] && [ "$(m construction.mutation_score.status)" = pass ] && [ "$(m construction.mutation_score.killed)" = 1 ] && ran_case || fail "a harness that kills the only mutant did not score 100: $(m construction.mutation_score.value)"
mu 2 'int lt(int a, int b) { return a < b; }\nint eq(int x) { return x == 1; }\n'; [ "$(m construction.mutation_score.value)" = 50.0 ] && [ "$(m construction.mutation_score.status)" = fail ] && [ "$(m construction.mutation_score.survivors)" = '["mut/ops.c:2 == -> !="]' ] && [ "$(card dimensions.construction.status)" = fail ] && ran_case || fail "a surviving mutant was not counted, listed and failed: $(m construction.mutation_score.value) $(m construction.mutation_score.survivors)"
mu 3 'int lt(int a, int b) { return a < b; }\n' 'exit 1'; [ "$(m construction.mutation_score.status)" = not-measurable ] && grep -q "UNMUTATED" <<<"$(m construction.mutation_score.reason)" && ran_case || fail "a harness failing on the unmutated subject was trusted"
mu 4 'int lt(int a, int b) { return a < b; }\n' ''; [ "$(m construction.mutation_score.status)" = not-measurable ] && grep -q "no mutation harness" <<<"$(m construction.mutation_score.reason)" && ran_case || fail "no harness was not not-measurable"
mu 5 '// a < b and a == b in a comment\nconst char *s = "x == y";\n#if A < B\n'; [ "$(m construction.mutation_score.status)" = not-measurable ] && grep -q "no mutable operator site" <<<"$(m construction.mutation_score.reason)" && ran_case || fail "a comment, a string or a preprocessor line was mutated"
mu 6 'int lt(int a, int b) { return a < b; }\n' 'grep -q "a < b" mut/ops.c || exit 99'; [ "$(m construction.mutation_score.status)" = not-measurable ] && grep -q "no viable" <<<"$(m construction.mutation_score.reason)" && ran_case || fail "only non-viable mutants did not read as not-measurable"
mu 7 'int f(int a,int b){ if (a < b) return a + b; if (a >= b) return a - b; return a != b; }\n' 'grep -q "a < b" mut/ops.c' 2 7; [ "$(m construction.mutation_score.mutants)" = 2 ] && [ "$(m construction.mutation_score.sites_total)" = 5 ] && ran_case || fail "the mutant budget or the site count is wrong: $(m construction.mutation_score.mutants) of $(m construction.mutation_score.sites_total)"
v1=$(m construction.mutation_score.survivors); run --repo "$T/mu7" --commit HEAD; [ "$(m construction.mutation_score.survivors)" = "$v1" ] && ran_case || fail "the seeded sample is not deterministic"
# 18b. equivalent mutants: the subject lists mutants no test can kill (adapter [mutation] equivalent: `id TAB reason TAB expiry`); only a reasoned, unexpired entry for a mutant that SURVIVED counts, and the score is over the rest.
# The survivor of fixture 2 is mut/ops.c:2:25:==:!=. A valid entry scores 100 and lists it; no reason, an expired date, a stale id and an entry for a mutant the tests KILL (mut/ops.c:1:32:<:<=) each leave the score at 50 and are reported rejected.
SRC2='int lt(int a, int b) { return a < b; }\nint eq(int x) { return x == 1; }\n'; R='the comparison is against a constant the type cannot hold'
mue() { local d=$T/mue$1; mkfixture "$d" "$(MUT_EQ=mut/equiv.txt adapter)"; ( cd "$d"; printf '%b' "$SRC2" > mut/ops.c; printf '# list\n%b\n' "$2" > mut/equiv.txt; git add -A; git commit -q --allow-empty -m "feat(fix): ops" ); run --repo "$d" --commit HEAD; }
mue 1 "mut/ops.c:2:25:==:!=\t$R\t2999-01-01"; [ "$(m construction.mutation_score.value)" = 100.0 ] && [ "$(m construction.mutation_score.status)" = pass ] && [ "$(m construction.mutation_score.survivors)" = '[]' ] && [ "$(m construction.mutation_score.equivalent)" = '["mut/ops.c:2:25:==:!="]' ] && [ "$(m construction.mutation_score.survived)" = 1 ] && ran_case || fail "a reasoned equivalent mutant was not excluded from the score: $(m construction.mutation_score.value) $(m construction.mutation_score.survivors)"
mue 2 "mut/ops.c:2:25:==:!=\t\t2999-01-01"; [ "$(m construction.mutation_score.value)" = 50.0 ] && [ "$(m construction.mutation_score.equivalent)" = '[]' ] && grep -q "needs" <<<"$(m construction.mutation_score.rejected_equivalents)" && ran_case || fail "an equivalent entry with no reason counted: $(m construction.mutation_score.value)"
mue 3 "mut/ops.c:2:25:==:!=\t$R\t2000-01-01"; [ "$(m construction.mutation_score.value)" = 50.0 ] && grep -q "expired" <<<"$(m construction.mutation_score.rejected_equivalents)" && ran_case || fail "an expired equivalent entry counted: $(m construction.mutation_score.value)"
mue 4 "mut/ops.c:9:25:==:!=\t$R\t2999-01-01"; [ "$(m construction.mutation_score.value)" = 50.0 ] && grep -q "not a surviving mutant" <<<"$(m construction.mutation_score.rejected_equivalents)" && ran_case || fail "a stale equivalent id counted: $(m construction.mutation_score.value)"
mue 5 "mut/ops.c:1:32:<:<=\t$R\t2999-01-01"; [ "$(m construction.mutation_score.value)" = 50.0 ] && grep -q "not a surviving mutant" <<<"$(m construction.mutation_score.rejected_equivalents)" && ran_case || fail "an entry for a KILLED mutant was accepted or changed the score: $(m construction.mutation_score.value)"
adapter | sed 's/^mutants = .*/mutants = 201/' > "$T/bad.toml"; run --repo "$G2" --commit "$s2" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "mutants must be 1..200" "$T/err" && ran_case || fail "a mutant budget over 200 was accepted"
# 19. non-vacuity: the same engine over the SPECIFICATION files, killed when a proof breaks (harness non-zero); the adapter's comment prefix is honoured
nv() { local d=$T/nv$1; mkfixture "$d" "$(NV_KILL="${3-grep -q \"p < q\" spec/ops.c}" NV_COMMENT="${4-//}" adapter)"; ( cd "$d"; printf '%b' "$2" > spec/ops.c; git add -A; git commit -q --allow-empty -m "feat(fix): spec" ); run --repo "$d" --commit HEAD; }
nv 1 'int lt(int p, int q) { return p < q; }\n'; [ "$(m verified.non_vacuity.value)" = 100.0 ] && [ "$(m verified.non_vacuity.status)" = pass ] && ran_case || fail "a spec mutant that breaks a proof did not score 100: $(m verified.non_vacuity.value)"
nv 2 'int lt(int p, int q) { return p < q; }\nint ge(int p) { return p >= 0; }\n'; [ "$(m verified.non_vacuity.value)" = 50.0 ] && [ "$(m verified.non_vacuity.status)" = fail ] && [ "$(card dimensions.verified.status)" = fail ] && [ "$(m verified.non_vacuity.survivors)" = '["spec/ops.c:2 >= -> >"]' ] && ran_case || fail "a spec mutant that no proof notices (a vacuous spec clause) was not counted and failed: $(m verified.non_vacuity.value) $(m verified.non_vacuity.survivors)"
nv 3 'int lt(int p, int q) { return p < q; }\n' 'exit 1'; [ "$(m verified.non_vacuity.status)" = not-measurable ] && grep -q "UNMUTATED" <<<"$(m verified.non_vacuity.reason)" && ran_case || fail "a proof harness failing on the unmutated spec was trusted"
nv 4 'x = a < b -- c == d\n' 'grep -q "a < b" spec/ops.c' '--'; [ "$(m verified.non_vacuity.sites_total)" = 1 ] && ran_case || fail "the adapter's comment prefix was not honoured: $(m verified.non_vacuity.sites_total) sites"
# 20. throughput against the comparators: percent of the best SCALAR comparator (the floor 50 = "within 2x"); non-scalar ones (SIMD) are reported as a gap, never floored; every declared comparator must report a number AND a pinned
# version with binary and input hashes, on a named corpus, or the metric is not-measurable and names the gap. 1.9x slower than the best scalar passes, 3x slower FAILS.
H=$(printf 'b%.0s' $(seq 64)); P() { echo "echo provenance $1 1.2.3 $H $H;"; }
bn() { local d=$T/bn$1; mkfixture "$d" "$(BENCH_CMD="$2" BENCH_COMP='{ name = "serde", scalar = true }, { name = "py", scalar = true }, { name = "simd", scalar = false }' adapter)"; run --repo "$d" --commit HEAD; }
all() { echo "echo corpus $H 100; echo subject $1; echo comparator serde 1000; echo comparator py 400; echo comparator simd 20000; $(P serde) $(P py) $(P simd)"; }
bn 1 "$(all 900)"; [ "$(m efficiency.throughput_vs_best.value)" = 90.0 ] && [ "$(m efficiency.throughput_vs_best.status)" = pass ] && [ "$(m efficiency.throughput_vs_best.best_scalar)" = serde ] && ran_case || fail "90% of the best scalar comparator did not pass: $(m efficiency.throughput_vs_best.value)"
[ "$(m efficiency.throughput_vs_best.gap_to_non_scalar_x)" = '{"simd": 22.2}' ] && [ "$(m efficiency.throughput_vs_best.corpus)" = '{"sha256": "'$H'", "bytes": 100}' ] && [ "$(m efficiency.throughput_vs_best.comparator_provenance)" != null ] && ran_case || fail "the gap to the SIMD comparator, the corpus or the provenance is not on the card"
bn 2 "$(all 526)"; [ "$(m efficiency.throughput_vs_best.value)" = 52.6 ] && [ "$(m efficiency.throughput_vs_best.status)" = pass ] && ran_case || fail "a subject 1.9x slower than the best scalar comparator did not pass: $(m efficiency.throughput_vs_best.value)"
bn 3 "$(all 333)"; [ "$(m efficiency.throughput_vs_best.value)" = 33.3 ] && [ "$(m efficiency.throughput_vs_best.status)" = fail ] && [ "$(card dimensions.efficiency.status)" = fail ] && ran_case || fail "a subject 3x slower than the best scalar comparator did not FAIL the efficiency floor: $(m efficiency.throughput_vs_best.value)"
bn 4 "$(all 900 | sed 's/echo comparator simd 20000;//')"; [ "$(m efficiency.throughput_vs_best.status)" = not-measurable ] && grep -q "without a number and a pinned version and hash: simd" <<<"$(m efficiency.throughput_vs_best.reason)" && ran_case || fail "a comparator that did not report was skipped instead of named"
bn 5 "$(all 900 | sed "s/$(P simd)//")"; [ "$(m efficiency.throughput_vs_best.status)" = not-measurable ] && grep -q "simd" <<<"$(m efficiency.throughput_vs_best.reason)" && ran_case || fail "a comparator with a number but no pinned version and hash was accepted"
bn 6 "$(all 900 | sed 's/echo corpus [0-9a-f]* 100;//')"; [ "$(m efficiency.throughput_vs_best.status)" = not-measurable ] && grep -q "name its corpus" <<<"$(m efficiency.throughput_vs_best.reason)" && ran_case || fail "a bench that does not name its corpus was accepted"
bn 7 'echo corpus x; exit 3'; [ "$(m efficiency.throughput_vs_best.status)" = fail ] && ran_case || fail "a dying bench was not a fail"
bn 8 ''; [ "$(m efficiency.throughput_vs_best.status)" = not-measurable ] && grep -q "no bench" <<<"$(m efficiency.throughput_vs_best.reason)" && ran_case || fail "no bench was not not-measurable"
adapter | sed 's/scalar = true/scalar = false/' > "$T/bad.toml"; run --repo "$G2" --commit "$s2" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "at least one scalar" "$T/err" && ran_case || fail "a comparator set with no scalar comparator was accepted"
adapter | sed 's/comparators = .*/comparators = ["py"]/' > "$T/bad.toml"; run --repo "$G2" --commit "$s2" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "comparators must be a list of" "$T/err" && ran_case || fail "a malformed comparator entry was accepted"
# 20b. the same measurement on more corpora (`corpusrow NAME SHA BYTES key=MB/s ...`): reported per corpus with its percent of the best scalar comparator, never floored; a row that lacks the subject or a declared comparator is not-measurable
cr() { echo "echo corpusrow $1 $H $2 subject=$3 serde=1000 py=400 simd=20000;"; }
bn 9 "$(all 900) $(cr small 50 600) $(cr big 200 300)"; [ "$(m efficiency.throughput_vs_best.status)" = pass ] && [ "$(m efficiency.throughput_vs_best.corpora_at_or_above_floor)" = 1 ] && [ "$(mp efficiency.throughput_vs_best corpora.0.percent_of_best_scalar)" = 60.0 ] && [ "$(mp efficiency.throughput_vs_best corpora.1.percent_of_best_scalar)" = 30.0 ] && [ "$(mp efficiency.throughput_vs_best corpora.1.best_scalar)" = serde ] && ran_case || fail "the per-corpus rows are not on the card with their percent of the best scalar comparator: $(m efficiency.throughput_vs_best.corpora)"
bn 10 "$(all 333) $(cr small 50 900)"; [ "$(m efficiency.throughput_vs_best.status)" = fail ] && ran_case || fail "a good second corpus lifted a subject below the floor on the primary corpus (the extra rows are reported, never averaged in)"
bn 11 "$(all 900) echo corpusrow bad $H 5 subject=9 serde=1000;"; [ "$(m efficiency.throughput_vs_best.status)" = not-measurable ] && grep -q "corpus row bad lacks: py, simd" <<<"$(m efficiency.throughput_vs_best.reason)" && ran_case || fail "a corpus row without every declared comparator was accepted: $(m efficiency.throughput_vs_best.reason)"
# 21. honesty.gates_self_tested: the adapter declares the gates and a pattern that only their negative self-test prints; the fast gate runs in the sandbox and the percent of gates with evidence is the value
gt() { local d=$T/gt$1; mkfixture "$d" "$(adapter | sed "s|^command = \"echo selftest alpha ok; echo ran: alpha: 3 cases\"|command = \"$2\"|; s|^gates = .*|gates = [{ name = \"alpha\", selftest = \"selftest alpha ok\" }, { name = \"beta\", selftest = \"selftest beta ok\" }]|")"; run --repo "$d" --commit HEAD; }
gt 1 "echo selftest alpha ok; echo ran: alpha: 3 cases; echo selftest beta ok" ""; [ "$(m honesty.gates_self_tested.value)" = 100.0 ] && [ "$(m honesty.gates_self_tested.status)" = pass ] && [ "$(m honesty.gates_self_tested.no_evidence)" = "[]" ] && ran_case || fail "every gate with evidence did not count 100: $(m honesty.gates_self_tested.value)"
gt 2 "echo selftest alpha ok; echo ran: alpha: 3 cases" ""; [ "$(m honesty.gates_self_tested.value)" = 50.0 ] && [ "$(m honesty.gates_self_tested.status)" = fail ] && [ "$(m honesty.gates_self_tested.no_evidence)" = '["beta"]' ] && [ "$(card dimensions.honesty.status)" = fail ] && ran_case || fail "a gate whose negative self-test left no evidence was not counted and named: $(m honesty.gates_self_tested.value)"
gt 3 "echo selftest alpha ok; echo ran: alpha: 3 cases; echo selftest beta ok; exit 1" ""; [ "$(m honesty.gates_self_tested.status)" = fail ] && grep -q "exited 1" <<<"$(m honesty.gates_self_tested.reason)" && ran_case || fail "evidence from a FAILING fast gate counted"
mkfixture "$T/gt4" "$(adapter | sed '/^gates = /d; /^warm_/d')"; run --repo "$T/gt4" --commit HEAD; [ "$(m honesty.gates_self_tested.status)" = not-measurable ] && grep -q "declares no gates" <<<"$(m honesty.gates_self_tested.reason)" && ran_case || fail "no declared gate was not not-measurable"
adapter | sed 's|^gates = .*|gates = [{ name = "a", selftest = "x" }]|' > "$T/bad.toml"; run --repo "$G2" --commit "$s2" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "shorter than 12" "$T/err" && ran_case || fail "a gate pattern that matches almost any output was accepted"
adapter | sed 's|^gates = .*|gates = [{ name = "a", selftest = "((unclosed pattern" }]|' > "$T/bad.toml"; run --repo "$G2" --commit "$s2" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "not a valid regex" "$T/err" && ran_case || fail "an invalid gate pattern was accepted"
adapter | sed 's|^gates = .*|gates = [{ name = "a", selftest = "selftest one ok" }, { name = "a", selftest = "selftest two ok" }]|' > "$T/bad.toml"; run --repo "$G2" --commit "$s2" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "named once" "$T/err" && ran_case || fail "a gate named twice was accepted"
# 22. honesty.attack_suite: the suite passes AND its sabotage run fails; a suite that passes with its gates stubbed, one that fails, and none declared are never a pass
at() { local d=$T/at$1; mkfixture "$d" "$(adapter | sed "s|^attack_cmd = .*|attack_cmd = '$2'|; s|^attack_sabotage_cmd = .*|attack_sabotage_cmd = '$3'|")"; run --repo "$d" --commit HEAD; }
at 1 'echo PASS relabel-attacks: 3 of 3' 'echo FAIL relabel-attacks: 0 of 3; exit 1'; [ "$(m honesty.attack_suite.value)" = 1 ] && [ "$(m honesty.attack_suite.status)" = pass ] && grep -q "^PASS" <<<"$(m honesty.attack_suite.pass_line)" && ran_case || fail "a suite that passes and fails under sabotage did not pass: $(m honesty.attack_suite.reason)"
at 2 'echo PASS relabel-attacks: 3 of 3' 'echo PASS relabel-attacks: 3 of 3'; [ "$(m honesty.attack_suite.status)" = fail ] && grep -q "cannot fail" <<<"$(m honesty.attack_suite.reason)" && ran_case || fail "a suite that still passes with its gates stubbed was accepted"
at 3 'echo FAIL relabel-attacks: 1 of 3; exit 1' 'echo FAIL relabel-attacks: 0 of 3; exit 1'; [ "$(m honesty.attack_suite.status)" = fail ] && grep -q "does not pass" <<<"$(m honesty.attack_suite.reason)" && ran_case || fail "a failing suite was accepted"
at 4 'exit 0' 'exit 1'; [ "$(m honesty.attack_suite.status)" = fail ] && ran_case || fail "a suite that prints no verdict line was accepted"
mkfixture "$T/at5" "$(adapter | sed '/^attack_/d')"; run --repo "$T/at5" --commit HEAD; [ "$(m honesty.attack_suite.status)" = not-measurable ] && grep -q "no attack suite" <<<"$(m honesty.attack_suite.reason)" && ran_case || fail "no declared suite was not not-measurable"
adapter | sed "s|^attack_cmd = .*|attack_cmd = 'true'|; /^attack_sabotage_cmd/d" > "$T/bad.toml"; run --repo "$G2" --commit "$s2" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && grep -q "declared together" "$T/err" && ran_case || fail "an attack suite declared without its sabotage run was accepted"
# 23. honesty.selftests_ran_cases (DECISIONS 19): the fast-gate log must carry `ran: NAME: N cases` evidence, N > 0 summed, no SKIPPED line. Zero cases, SKIPPED and no evidence EACH fail Process honesty alone (the dimension's only
# below-floor metric; velocity and verified stay green); a gate with cases passes; the evidence is read by the runner itself (never the subject's reader); malformed lines count nothing.
RAN='ran: alpha: 3 cases'; GA='echo selftest alpha ok'
rt() { local d=$T/rt$1; rm -rf "$d"; mkfixture "$d" "$(adapter | sed "s|^command = .*|command = \"$2\"|; $3")"; run --repo "$d" --commit HEAD; }
only_honesty() { [ "$(m honesty.selftests_ran_cases.status)" = fail ] && [ "$(card dimensions.honesty.below_floor)" = '["honesty.selftests_ran_cases"]' ] && [ "$(card dimensions.honesty.status)" = fail ] && [ "$(card dimensions.velocity.status)" = pass ] && [ "$(card dimensions.verified.below_floor)" = "[]" ] && [ "$(m honesty.gates_self_tested.status)" = pass ] && [ "$(card verdicts.landedness.status)" = pass ] && [ "$(card verdicts.correctness.status)" = fail ]; }
rt 1 "$GA; echo $RAN" ""; [ "$(m honesty.selftests_ran_cases.status)" = pass ] && [ "$(m honesty.selftests_ran_cases.value)" = 3 ] && [ "$(m honesty.selftests_ran_cases.evidence_names)" = 1 ] && [ "$(m honesty.selftests_ran_cases.cases_by_name)" = '{"alpha": 3}' ] && grep -q "not that every case was meaningful" <<<"$(m honesty.selftests_ran_cases.weakness)" && [ "$(card dimensions.honesty.status)" = pass ] && ran_case || fail "a gate with cases did not pass: $(m honesty.selftests_ran_cases.reason)"
rt 2 "$GA; echo ran: alpha: 0 cases" ""; only_honesty && [ "$(m honesty.selftests_ran_cases.value)" = 0 ] && grep -q "zero cases" <<<"$(m honesty.selftests_ran_cases.reason)" && [ "$(m honesty.selftests_ran_cases.zero_case_names)" = '["alpha"]' ] && ran_case || fail "ZERO executed cases did not fail Process honesty alone: $(m honesty.selftests_ran_cases.reason)"
rt 3 "$GA; echo $RAN; echo SKIPPED scripts/test_beta.sh: no tool" ""; only_honesty && grep -q "SKIPPED" <<<"$(m honesty.selftests_ran_cases.reason)" && [ "$(m honesty.selftests_ran_cases.cases)" = 3 ] && ran_case || fail "a SKIPPED line did not fail Process honesty alone (cases were counted too): $(m honesty.selftests_ran_cases.reason)"
rt 4 "$GA" ""; only_honesty && grep -q "no evidence" <<<"$(m honesty.selftests_ran_cases.reason)" && [ "$(m honesty.selftests_ran_cases.value)" = 0 ] && ran_case || fail "a log with no ran-evidence did not fail Process honesty alone: $(m honesty.selftests_ran_cases.reason)"
rt 5 "$GA; echo ran: alpha: 0 cases; echo ran: beta: 2 cases; echo ran: alpha: 1 cases" 's/^ran_names = .*/ran_names = ["alpha", "beta"]/'; [ "$(m honesty.selftests_ran_cases.value)" = 3 ] && [ "$(m honesty.selftests_ran_cases.status)" = pass ] && [ "$(m honesty.selftests_ran_cases.cases_by_name)" = '{"alpha": 1, "beta": 2}' ] && ran_case || fail "the evidence is not summed over lines: $(m honesty.selftests_ran_cases.value)"
rt 6 "$GA; echo ran: alpha: -1 cases; echo 'ran: alpha: 3 cases extra'; echo ' ran: alpha: 3 cases'; echo ran: alpha: 99999999999999999999 cases; echo ran: a/b: 3 cases; echo ran: alpha: 3 test" ""; only_honesty && grep -q "no evidence" <<<"$(m honesty.selftests_ran_cases.reason)" && ran_case || fail "a malformed or padded evidence line counted: $(m honesty.selftests_ran_cases.value)"
rt 7 "$GA; echo $RAN; exit 1" ""; [ "$(m honesty.selftests_ran_cases.status)" = fail ] && grep -q "exited 1" <<<"$(m honesty.selftests_ran_cases.reason)" && ran_case || fail "evidence from a FAILING fast gate counted"
rt 8 "$GA; echo ran: alpha: 3 cases" 's/^ran_names = .*/ran_names = ["alpha", "beta"]/'; [ "$(m honesty.selftests_ran_cases.status)" = fail ] && grep -q "declared name(s): beta" <<<"$(m honesty.selftests_ran_cases.reason)" && ran_case || fail "a declared evidence name with no line was not named: $(m honesty.selftests_ran_cases.reason)"
rt 9 "$GA; echo ran: alpha: 3 cases; echo ran: beta: 0 cases" 's/^ran_names = .*/ran_names = ["alpha", "beta"]/'; [ "$(m honesty.selftests_ran_cases.status)" = fail ] && grep -q "declared name(s): beta" <<<"$(m honesty.selftests_ran_cases.reason)" && ran_case || fail "a declared evidence name with zero cases passed on the others' sum"
rt 10 "$GA; echo ran: alpha: 3 cases; echo ran: beta: 1 cases" 's/^ran_names = .*/ran_names = ["alpha", "beta"]/'; [ "$(m honesty.selftests_ran_cases.status)" = pass ] && [ "$(m honesty.selftests_ran_cases.ran_names_declared)" = '["alpha", "beta"]' ] && ran_case || fail "every declared evidence name with cases did not pass"
rt 12 "$GA; echo ran: alpha: 3 cases; echo ran: gamma: 5 cases" ""; only_honesty && grep -q "cannot invent a gate.*gamma" <<<"$(m honesty.selftests_ran_cases.reason)" && ran_case || fail "a gate the adapter does not declare (an invented evidence name) was accepted: $(m honesty.selftests_ran_cases.reason)"
rt 13 "$GA; echo $RAN" '/^ran_names = /d'; [ "$(m honesty.selftests_ran_cases.status)" = not-measurable ] && grep -q "no .tier1. ran_names" <<<"$(m honesty.selftests_ran_cases.reason)" && [ "$(card dimensions.honesty.status)" = fail ] && ran_case || fail "a subject with no declared ran_names was measured (it must be not-measurable and fail the floor)"
for bad in 's/^ran_names = .*/ran_names = ["a b"]/' 's/^ran_names = .*/ran_names = ["a", "a"]/' 's/^ran_names = .*/ran_names = "a"/'; do adapter | sed "$bad" > "$T/bad.toml"; run --repo "$G2" --commit "$s2" --adapter "$T/bad.toml"; [ "$rc" = 2 ] && ran_case || fail "a bad ran_names ($bad) was accepted"; done
mkfixture "$T/rt11" "$(adapter)"; sbargs=(); run --repo "$T/rt11" --commit HEAD; sbargs=(--sandbox "$T/fake"); [ "$(m honesty.selftests_ran_cases.status)" = not-measurable ] && grep -q "no launcher" <<<"$(m honesty.selftests_ran_cases.reason)" && ran_case || fail "without a sandbox the evidence was read (nothing may execute)"
ran_done test_scorecard
echo "tier1: scorecard: metrics: forbidden constructs, specified share, trusted C, ledger, hand-written tests, tier 1, open PRs, velocity; floors, no averaging, not-measurable fails: ok"
