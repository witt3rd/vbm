#!/usr/bin/env bash
# Tier 1: scorecard/card-to-page renders a card as ONE house page (a one-slide deck, slides.py): every metric is a table row, every unmeasured metric carries its reason, the notes (libc symbols, hand-written cases and drivers,
# throughput and gap, comparator pins, the fast gate) are on the page, the footer names the subject commit, date and age; the same card gives the same bytes. Text the SUBJECT controls (file names, reasons, symbols) is HTML-escaped.
# Negative self-tests: a not-measurable metric with no reason is refused, a card with no subject commit date is refused, a hostile string is not injected as markup.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (.land/tool/docs/ran-evidence.md)
cp=$(pwd)/scorecard/card-to-page
fail() { echo "tier1: card-to-page: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
python3 - "$T" "$(pwd)" <<'PY'
import json, sys
def m(i, d, st, v=None, fl=None, **k): return {"id": i, "dimension": d, "status": st, "value": v, "floor": fl, "dir": "up", "definition": "x", "implemented": True, **k}
base = lambda ms, dims, res=None: {"schema": "scorecard-1", "scorecard": {"sha": "a" * 40, "dirty": False}, "subject": {"name": "fix", "kind": "library", "commit": "b" * 40, "commit_date": "2026-11-04T11:56:29-08:00"}, "adapter": {"sha256": "c" * 64}, "metrics": ms, "dimensions": dims}
bad = base([m("verified.unproved_escapes", "verified", "pass", 0, {"op": "==", "value": 0}), m("verified.specified_share", "verified", "not-measurable", None, {"op": ">=", "value": 100}, reason="needs the <script>alert(1)</script> sandbox"),
            m("construction.hand_written_tests", "construction", "fail", 4, {"op": "==", "value": 0}, files=["tests/a_test.c"], cases_by_file={"tests/<b>a_test.c": 3, "tests/b_test.py": 1}, drivers=["tests/load.py"]),
            m("bare_metal.libc_symbols", "bare_metal", "fail", 2, {"op": "==", "value": 0}, symbols=["malloc", "pthread_once"]), m("bare_metal.wasm_freestanding_build", "bare_metal", "pass", 1, {"op": "==", "value": 1}, bytes=60740),
            m("efficiency.throughput_vs_best", "efficiency", "fail", 30.0, {"op": ">=", "value": 50}, subject_mb_s=50.0, comparators_mb_s={"serde": 160.0, "simd": 1500.0}, best_scalar="serde", gap_to_best_scalar_x=3.2, gap_to_non_scalar_x={"simd": 30.0}, corpus={"sha256": "c" * 64, "bytes": 100}, comparator_provenance={"serde": {"version": "1.2.3", "sha256": "d" * 64, "inputs_sha256": "e" * 64}, "simd": {"version": "5.0", "sha256": "f" * 64, "inputs_sha256": "-"}}),
            m("velocity.tier1_seconds", "velocity", "pass", 41.0, {"op": "<", "value": 60}, command="cp -a /subject /tmp/w && scripts/tier1.sh")],
          {"verified": {"status": "fail", "below_floor": [], "below_floor_implemented": []}, "construction": {"status": "fail", "below_floor": [], "below_floor_implemented": []},
           "bare_metal": {"status": "fail", "below_floor": [], "below_floor_implemented": []}, "efficiency": {"status": "fail", "below_floor": [], "below_floor_implemented": []}, "velocity": {"status": "pass", "below_floor": [], "below_floor_implemented": []}})
good = base([m("verified.unproved_escapes", "verified", "pass", 0, {"op": "==", "value": 0})], {"verified": {"status": "pass", "below_floor": [], "below_floor_implemented": []}})
eff = next(x for x in bad["metrics"] if x["id"] == "efficiency.throughput_vs_best")
eff.update(corpora=[{"name": "primary", "sha256": "d" * 64, "bytes": 1033424, "mb_s": {"subject": 120.0, "serde": 160.0, "simd": 1500.0}, "best_scalar": "serde", "percent_of_best_scalar": 75.0},
                    {"name": "<b>big</b>", "sha256": "e" * 64, "bytes": 2251051, "mb_s": {"subject": 40.0, "serde": 331.0, "simd": 1439.5}, "best_scalar": "serde", "percent_of_best_scalar": 12.1}], corpora_at_or_above_floor=1, corpora_floor_percent=50)
bad["metrics"] += [m("honesty.gates_self_tested", "honesty", "fail", 50.0, {"op": ">=", "value": 100}, gates=["a", "<i>b</i>"], self_test_ran=["a"], no_evidence=["<i>b</i>"]),
                   m("honesty.selftests_ran_cases", "honesty", "fail", 0, {"op": ">=", "value": 1}, reason="the fast-gate log has 1 line(s) with SKIPPED: <b>x</b>", cases=3, evidence_names=2, cases_by_name={"a": 3, "b": 0}, ran_names_declared=[], weakness="a count regex proves a count was printed, not that every case was meaningful"),
                   m("honesty.attack_suite", "honesty", "pass", 1, {"op": "==", "value": 1}, pass_line="PASS relabel-attacks: 3 of 3", sabotage_line="FAIL relabel-attacks: 0 of 3")]
bad["sandbox"] = {"limits": {"cpus": 2}}
noreason = json.loads(json.dumps(bad)); del noreason["metrics"][1]["reason"]
nodate = json.loads(json.dumps(bad)); del nodate["subject"]["commit_date"]
# a scorecard-3 card (the warm/cold split and its verdicts): correctness passes, the warm run regressed, the profile fails and is in neither verdict line
sys.path.insert(0, sys.argv[2] + "/scorecard"); import scorecard_verdicts
dd = lambda st: {"status": st, "below_floor": [], "below_floor_implemented": []}
v3 = base([m("verified.unproved_escapes", "verified", "pass", 0, {"op": "==", "value": 0}), m("velocity.tier1_seconds_warm", "velocity", "fail", 75.0, {"op": "<", "value": 60}, command="scripts/tier1.sh", change_command="touch x", gates_shown=["a"], gates_skipped=["b"]),
           m("velocity.tier1_seconds_cold", "velocity", "pass", 494.5, {"op": "<=", "value": 600}, command="cp -a /subject /tmp/w && scripts/tier1.sh"), m("efficiency.throughput_vs_best", "efficiency", "fail", 30.0, {"op": ">=", "value": 50})],
          {"verified": dd("pass"), "velocity": {**dd("fail"), "below_floor": ["velocity.tier1_seconds_warm"]}, "efficiency": dd("fail")})
v3["schema"] = "scorecard-3"; v3["verdicts"] = scorecard_verdicts.verdicts(v3); v3["sandbox"] = {"limits": {"cpus": 2, "memory_mb": 4096}}
lie = json.loads(json.dumps(v3)); lie["verdicts"]["landedness"]["status"] = "pass"
for n, c in (("bad", bad), ("good", good), ("noreason", noreason), ("nodate", nodate), ("v3", v3), ("lie", lie)): json.dump(c, open(f"{sys.argv[1]}/{n}.json", "w"))
PY
"$cp" "$T/bad.json" --as-of 2026-11-04T20:10:00+00:00 -o "$T/bad.py" && ran_case || fail "a failing card did not render"
# execute the generated slides.py against a stub Deck and look at what it would put on the page
page() { python3 - "$1" <<'PY'
import runpy, sys, types, json
cap = []
class Deck:
    def __init__(self, here, title): cap.append(("deck", title))
    def slide(self, *a, **k): cap.append(("slide", a, k)); self.TITLE = "t"; self.S = []
m = types.ModuleType("publishing.page"); m.Deck = Deck; pkg = types.ModuleType("publishing"); pkg.page = m; sys.modules.update({"publishing": pkg, "publishing.page": m})
runpy.run_path(sys.argv[1])
s = [x for x in cap if x[0] == "slide"]
assert len(s) == 1, "the page must be exactly one slide"
_, a, k = s[0]; print(json.dumps({"kicker": a[0], "h1": a[1], "h2": a[2], "body": a[3], "foot": a[4], "cls": k.get("cls")}))
PY
}
page "$T/bad.py" > "$T/bad.json.out" && ran_case || fail "the generated slides.py is not one valid slide"
has() { python3 - "$T/bad.json.out" "$1" <<'PY' && ran_case || fail "the page lacks: $1"
import json, sys
p = json.load(open(sys.argv[1])); t = " ".join(str(v) for v in p.values())
sys.exit(0 if sys.argv[2] in t else 1)
PY
}
for s in "Correctness: FAIL" "Landedness: PENDING" "scored before the warm/cold split" "Profile (in neither verdict)" "specified share" "unproved escapes" "libc symbols" "wasm freestanding build" "60740 B" "tier1 seconds" "not measurable (1)" "<code>malloc</code>, <code>pthread_once</code>" \
         "Hand-written cases</b> (4)" "<code>b_test.py</code> 1" "Drivers, 0 cases: <code>load.py</code>" "Gap to simd: 30x (non-scalar, not floored)" "best scalar serde is 3.2x faster (floor: within 2x)" "serde 1.2.3" "<code>scripts/tier1.sh</code>, cold" \
         "committed 2026-11-04 11:56 -0800, 14 min before this card" "subject bbbbbbbbbbbb" "tight" \
         "<b>2 corpora</b>" "1 of 2 at or above the 50% line" "75%" "12.1%" \
         "Level 1, Certified" "is not built yet"; do has "$s"; done
python3 - "$T/bad.json.out" <<'PY' && ran_case || fail "a metric row is missing, or a hostile string was injected as markup"
import json, sys
p = json.load(open(sys.argv[1])); b = p["body"]
assert b.count("<tr><td>") == 10, b.count("<tr><td>")                     # every metric is a row, none dropped
assert "<script>" not in b and "&lt;script&gt;alert(1)&lt;/script&gt;" in b      # a reason the subject controls is escaped
assert "<b>a_test.c" not in b and "&lt;b&gt;a_test.c" in b                  # so is a file name
assert "<b>big</b>" not in b and "&lt;b&gt;big&lt;/b&gt;" in b                  # and a corpus name
PY
"$cp" "$T/bad.json" --as-of 2026-11-04T20:10:00+00:00 --note "busy <b>host</b>" -o "$T/note.py"; page "$T/note.py" > "$T/note.out"; grep -q "busy &lt;b&gt;host&lt;/b&gt;" "$T/note.out" && ! grep -q "busy <b>host" "$T/note.out" && ran_case || fail "the run-conditions note is missing from the page or was injected as markup"
"$cp" "$T/bad.json" --as-of 2026-11-04T20:10:00+00:00 -o "$T/bad2.py"; cmp -s "$T/bad.py" "$T/bad2.py" && ran_case || fail "same card, different bytes"
"$cp" "$T/good.json" --as-of 2026-11-06T20:10:00+00:00 -o "$T/good.py"; page "$T/good.py" > "$T/good.out"; grep -q "Correctness: PASS" "$T/good.out" && ! grep -q "FAIL" "$T/good.out" && grep -q "2 days before this card" "$T/good.out" && ran_case || fail "a passing card was not shown as PASS with its age in days"
"$cp" "$T/nodate.json" -o "$T/nd.py" 2>"$T/err" && fail "negative self-test: a card with no subject commit date was rendered"; grep -q "no subject commit date" "$T/err" && ran_case || fail "wrong refusal for a missing commit date"
"$cp" "$T/noreason.json" -o "$T/nr.py" 2>"$T/err" && fail "negative self-test: a not-measurable metric without a reason was rendered"; grep -q "without a reason" "$T/err" && ran_case || fail "wrong refusal: $(cat "$T/err")"
# a scorecard-3 card: the two verdict lines come first and say what the dimensions say; the warm and cold rows and notes are there; a card whose stored verdicts disagree with its dimensions is refused
"$cp" "$T/v3.json" --as-of 2026-11-04T20:10:00+00:00 -o "$T/v3.py"; page "$T/v3.py" > "$T/v3.out"
python3 - "$T/v3.out" <<'PY' && ran_case || fail "the scorecard-3 page: the verdict lines, the warm and cold rows or the group titles are wrong"
import json, re, sys
p = json.load(open(sys.argv[1])); h2, b = p["h2"], p["body"]
assert h2.startswith('<b class="good">Correctness: PASS (1 of 3 primary dimensions measured; Trusted generation not yet defined)</b><br><b class="bad">Landedness: FAIL</b>'), h2        # the first line is the correctness verdict, the second the landedness verdict
assert "Profile (in neither verdict): Efficiency fail" in b and "Efficiency fail" not in h2   # the profile is shown, and is in neither verdict line
assert "tier1 seconds warm" in b and "tier1 seconds cold" in b and "494.5" in b and "&lt;= 600" in b and "<b>Warm run</b>" in b and "<b>Cold run</b>" in b and "skipped 1 of 2 gates by design: b" in b and "75 (skipped 1 of 2 gates)" in b
assert "Correctness: PASS</b>" not in h2 and "Correctness: PASS<" not in b      # NEVER a bare PASS while a primary dimension is undefined (page and title row)
assert b.index("Correctness: PASS") < b.index("Landedness: FAIL") < b.index("Profile (in neither verdict)")       # grouped in that order
assert b.index("unproved escapes") < b.index("tier1 seconds warm") < b.index("throughput vs best")
PY
"$cp" "$T/lie.json" -o "$T/lie.py" 2>"$T/err" && fail "negative self-test: a card whose verdicts disagree with its dimensions was rendered"; grep -q "disagree with its dimensions" "$T/err" && ran_case || fail "wrong refusal for a lying verdict: $(cat "$T/err")"
# the verdict groups are PINNED (a dimension cannot be moved between Correctness, Landedness and the profile to make a verdict pass), cover every dimension the runner defines exactly once, and each regression flips only its own verdict
python3 - "$(pwd)" <<'PY' && ran_case || fail "the verdict groups or their flips are wrong"
import importlib.machinery, importlib.util, sys
root = sys.argv[1]; sys.path.insert(0, root + "/scorecard"); import scorecard_verdicts as V
l = importlib.machinery.SourceFileLoader("sc", root + "/scorecard/scorecard"); s = importlib.util.spec_from_loader("sc", l); sc = importlib.util.module_from_spec(s); l.exec_module(sc)
assert V.CORRECTNESS == ("verified", "construction", "generation", "honesty") and V.LANDEDNESS == ("velocity",) and V.PROFILE == ("bare_metal", "efficiency"), "the groups moved"
assert all(sum(d in g for g in V.GROUPS.values()) == 1 for d in {m["dim"] for m in sc.METRICS}), "a dimension is in no group or in two"
d = lambda st, bf=(): {"status": st, "below_floor": list(bf), "below_floor_implemented": list(bf)}
ids = [{"id": "velocity.tier1_seconds_warm"}]
good = {"verified": d("pass"), "construction": d("pass"), "honesty": d("pass"), "velocity": d("pass"), "bare_metal": d("pass"), "efficiency": d("pass")}
get = lambda dims, mets=ids: {k: v["status"] for k, v in V.verdicts({"dimensions": dims, "metrics": mets}).items() if k != "profile"}
assert get(good) == {"correctness": "pass", "landedness": "pass"}
for dim, want in (("verified", ("fail", "pass")), ("construction", ("fail", "pass")), ("honesty", ("fail", "pass")), ("velocity", ("pass", "fail")), ("bare_metal", ("pass", "pass")), ("efficiency", ("pass", "pass"))):
    got = get({**good, dim: d("fail", [dim + ".x"])}); assert (got["correctness"], got["landedness"]) == want, (dim, got)   # a profile ideal flips NEITHER line
assert V.verdicts({"dimensions": {**good, "bare_metal": d("fail", ["bare_metal.x"])}, "metrics": ids})["profile"]["below_floor"] == ["bare_metal.x"]
assert get({**good, "newidea": d("fail")}) == {"correctness": "pass", "landedness": "pass"}                       # an unknown dimension is a profile entry
assert get({}) == {"correctness": "pending", "landedness": "pending"}                                              # nothing judged is never a pass
assert get(good, [{"id": "velocity.tier1_seconds"}])["landedness"] == "pending" and get(good, [{"id": "velocity.tier1_seconds"}, ids[0]])["landedness"] == "pass"   # only a card with the retired metric and no split is pending
assert V.verdicts({"dimensions": good, "metrics": ids})["correctness"]["not_defined_yet"] == ["generation"]
cv = V.verdicts({"dimensions": good, "metrics": ids})["correctness"]
assert V.label(cv) == "PASS (3 of 4 primary dimensions measured; Trusted generation not yet defined)" and V.label(cv, short=True) == "PASS (3 of 4; Trusted generation not yet defined)"
assert V.label({**cv, "status": "fail"}).startswith("FAIL (3 of 4") and V.label({"status": "pass", "not_defined_yet": [], "measured": 4, "of": 4}) == "PASS" and V.label({"status": "pending"}) == "pending".upper()   # coverage only while something is undefined       # the correctness ideal with no metric is said, not dropped
PY
ran_done test_card_page
echo "tier1: card-to-page: one slide, every metric a row, reasons and notes on the page, subject commit date and age in the footer, hostile text escaped, unexplained not-measurable refused: ok"
