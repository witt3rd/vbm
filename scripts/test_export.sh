#!/usr/bin/env bash
# Tier 1: Level 1 slice 2: export INTAKE (scorecard/scorecard_export.py). A REAL export (scorecard/fixtures/nat_add_succ.ndjson, made by the toolchain's lean4export 3.1.0) is accepted; every hostile or malformed variant is
# REJECTED with a reason: over the byte/line/line-length caps, not UTF-8, empty, no meta line, a format version outside 3.1.x, a duplicate key, NaN, a non-dense id, a forward reference, an unknown or doubled tag, a declaration with no value or
# a missing type, a duplicated declaration, a nesting bomb (an expression chain over the depth cap, and a JSON line nested 100000 deep), an over-long natVal; the wall-clock and memory bounds stop a runaway; and `scorecard certify`
# turns a hash mismatch, a missing export and a hostile export into a FAILED metric (never a pass, never a crash) and reads a good one.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (.land/tool/docs/ran-evidence.md)
fail() { echo "tier1: export: $*" >&2; exit 1; }
python3 - <<'PY' || exit 1
import json, sys, time
sys.path.insert(0, "scorecard"); import scorecard_export as E
raw = open("scorecard/fixtures/nat_add_succ.ndjson", "rb").read(); L = raw.decode().split("\n")[:-1]
X = E.intake(raw)
assert X.counts["lines"] == 577 and "Nat.add_succ" in X.decls and X.decls["Nat.add_succ"]["kind"] == "thm" and X.decls["Nat.rec"]["kind"] == "rec" and X.meta["lean"]["version"], X.counts
def rej(what, data, why, **kw):
    try: E.intake(data if isinstance(data, bytes) else ("\n".join(data) + "\n").encode(), **kw)
    except E.ExportError as e:
        assert why in str(e), f"{what}: wrong reason: {e}"; return
    raise SystemExit(f"negative self-test: {what} was ACCEPTED")
meta = L[0]; ne = sum(1 for l in L if '"ie"' in l)
rej("an oversize export", raw, "byte cap", max_bytes=1000)
rej("too many lines", raw, "-line cap", max_lines=10)
rej("an over-long line", raw, "-character cap", max_line=50)
rej("a non-UTF-8 export", b"\xff\xfe" + raw, "not UTF-8")
rej("an empty export", b"", "empty")
rej("no meta line", L[1:], "first line")
rej("an old format", [meta.replace("3.1.0", "3.0.0")] + L[1:], "format version 3.1.x")
rej("a newer format", [meta.replace("3.1.0", "3.2.0")] + L[1:], "format version 3.1.x")
rej("a duplicate key", [meta, '{"in":1,"in":2,"str":{"pre":0,"str":"x"}}'], "duplicate key")
rej("NaN", [meta, '{"in":NaN,"str":{"pre":0,"str":"x"}}'], "NaN")
rej("a non-dense name id", [meta, '{"in":5,"str":{"pre":0,"str":"x"}}'], "dense")
rej("a forward reference", [meta, '{"ie":0,"app":{"fn":3,"arg":4}}'], "earlier expressions")
rej("a name whose prefix is later", [meta, '{"in":1,"str":{"pre":7,"str":"x"}}'], "earlier name")
rej("an unknown tag", [meta, '{"ie":0,"evil":1}'], "exactly one known tag")
rej("two tags", [meta, '{"ie":0,"bvar":1,"sort":0}'], "exactly one known tag")
rej("an unknown declaration kind", [meta, '{"macro":{}}'], "exactly one of")
rej("an extra key in an app", [meta, '{"ie":0,"bvar":0}', '{"ie":1,"app":{"fn":0,"arg":0,"x":1}}'], "exactly the keys")
rej("a non-object line", [meta, "[1,2]"], "not a JSON object")
rej("a blank interior line", [meta, "", '{"ie":0,"bvar":0}'], "not a JSON object")
d = next(l for l in L if l.startswith('{"thm"'))
rej("a theorem with no value", L[:L.index(d)] + [d.replace(',"value":436', "")], "needs a value")
rej("a declaration with no type", L[:L.index(d)] + [d.replace('"type":431,', "")], "needs a type")
rej("a declaration pointing past the expressions", L[:L.index(d)] + [d.replace('"value":436', '"value":99999')], "not an earlier expression")
rej("a duplicated declaration", L + [d], "appears twice")
bomb = [meta, '{"ie":0,"bvar":0}'] + [json.dumps({"ie": i, "app": {"fn": i - 1, "arg": 0}}) for i in range(1, E.MAX_DEPTH + 3)]
rej("an expression chain over the depth cap", bomb, "nested deeper")
rej("a JSON line nested 100000 deep", [meta, "[" * 100000], "not a JSON object")
rej("a natVal of 10001 digits", [meta, json.dumps({"ie": 0, "natVal": "1" * 10001})], "10000 digits")
rej("a natVal with a leading zero", [meta, json.dumps({"ie": 0, "natVal": "01"})], "decimal string")
# the bounds: a runaway is stopped, not waited for
try:
    with E.bounded(seconds=1):
        while True: pass
    raise SystemExit("negative self-test: the wall-clock bound did not stop a busy loop")
except E.ExportError as e: assert "took over" in str(e)
try:
    with E.bounded(seconds=30, memory=300 << 20): bytearray(1 << 30)
    raise SystemExit("negative self-test: the memory bound did not stop a 1 GiB allocation")
except E.ExportError as e: assert "needed over" in str(e)
PY
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT; export TMPDIR=$T/tmp; mkdir -p "$TMPDIR"
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
sc=$(pwd)/scorecard/scorecard; fx=$(pwd)/scorecard/fixtures/nat_add_succ.ndjson
printf 'repos = ["example/fixture"]\nmeasured_per_month = 1\n' > "$T/allow.toml"
mk() {   # mk EXPORT_FILE DECLARED_SHA: a subject repo with the export and a manifest (reuses test_manifest.sh's manifest text)
  rm -rf "$T/s"; mkdir -p "$T/s/proof"; git init -q -b main "$T/s"; cp "$1" "$T/s/proof/export.ndjson"
  sed '/^manifest() {/,/^TOML$/!d' scripts/test_manifest.sh | sed '1d;$d' | sed "s/[$]H/$2/" > "$T/s/vbm-proof.toml"
  ( cd "$T/s"; git remote add origin git@github.com:example/fixture.git; git add -A; git commit -qm "feat(fix): fixture" ); }
certify() { "$sc" certify --repo "$T/s" --commit HEAD --allowlist "$T/allow.toml" > "$T/card.json" 2> "$T/err" && ran_case || fail "certify crashed or refused: $(cat "$T/err")"; }
metric() { python3 -c 'import json,sys; c=json.load(open(sys.argv[1])); m=[m for m in c["metrics"] if m["id"]==sys.argv[2]][0]; print(m["status"], m.get("reason",""))' "$T/card.json" "$1"; }
good=$(sha256sum "$fx" | cut -d' ' -f1)
mk "$fx" "$good"; head -3 "$T/s/vbm-proof.toml" | grep -q '^\[export\]' && ran_case || fail "the test manifest was not extracted"
certify; [ "$(metric verified.export_intake)" = "pass " ] && ran_case || fail "a good export did not pass intake: $(metric verified.export_intake)"
python3 - "$T/card.json" "$good" <<'PY' && ran_case || fail "the card's export block is wrong"
import json, sys; c = json.load(open(sys.argv[1])); e = c["export"]; assert e["sha256"] == sys.argv[2] and e["declarations"] == 33 and e["declaration_kinds"]["thm"] == 1 and e["lines"] == 577, e
m = [m for m in c["metrics"] if m["id"] == "verified.export_meta"][0]; assert m["source"] == "self-reported" and m["status"] == "info", m
PY
mk "$fx" "$(printf 'b%.0s' $(seq 64))"; certify; metric verified.export_intake | grep -q "^fail the export's sha256" && ran_case || fail "negative self-test: a stale manifest hash passed: $(metric verified.export_intake)"
sed 's/"Nat"/"Nat\\u0000"/; 3s/.*/{"il":1,"succ":9}/' "$fx" > "$T/bad.ndjson"; mk "$T/bad.ndjson" "$(sha256sum "$T/bad.ndjson" | cut -d' ' -f1)"; certify; metric verified.export_intake | grep -q "^fail line 3" && ran_case || fail "negative self-test: a hostile export did not FAIL intake: $(metric verified.export_intake)"
mk "$fx" "$good"; git -C "$T/s" rm -q proof/export.ndjson; git -C "$T/s" commit -qm "feat(fix): no export"; certify; metric verified.export_intake | grep -q "^fail the declared export cannot be read" && ran_case || fail "negative self-test: a missing export did not fail: $(metric verified.export_intake)"
mk "$fx" "$good"; git -C "$T/s" rm -q proof/export.ndjson; mkdir -p "$T/s/proof"; ln -s /etc/hostname "$T/s/proof/export.ndjson"; git -C "$T/s" add -A; git -C "$T/s" commit -qm "feat(fix): symlink"; certify; metric verified.export_intake | grep -q "symlink" && ran_case || fail "negative self-test: a symlinked export was read: $(metric verified.export_intake)"
ran_done test_export
echo "tier1: export: a real lean4export export is accepted; hostile, oversize, malformed, cyclic-by-forward-reference and nesting-bomb exports are rejected; the bounds stop a runaway; certify turns each into a failed metric: ok"
