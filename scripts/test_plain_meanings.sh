#!/usr/bin/env bash
# Tier 1: every metric in the scorecard has a plain one-line meaning (at most 140 chars, ASCII, no backticks, no snake_case identifiers), and the rendered card shows it.
# Negative self-tests: a missing, over-long, backticked, snake_case or non-ASCII meaning is reported, and a metric with no plain line is reported.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/0001-ran-evidence.md)
python3 - <<'PY'
import importlib.machinery, importlib.util, sys
sys.path.insert(0, "scorecard"); sys.dont_write_bytecode = True
import scorecard_plain as P, scorecard_card_md as C
ldr = importlib.machinery.SourceFileLoader("sc", "scorecard/scorecard"); spec = importlib.util.spec_from_loader("sc", ldr); sc = importlib.util.module_from_spec(spec); ldr.exec_module(sc)
ids = {m["id"] for m in sc.METRICS}
miss = ids - set(P.PLAIN)
assert not miss, f"metrics with no plain meaning: {sorted(miss)}"
assert not (set(P.PLAIN) - ids), "plain meaning for an unknown metric"
assert not P.problems({i: m["plain"] for i, m in ((m["id"], m) for m in sc.METRICS)}), P.problems(P.PLAIN)
assert not P.problems(P.PLAIN), P.problems(P.PLAIN)
for bad, why in [("", "empty"), ("x" * 141, "141"), ("see `sorry_pattern`", "backtick"), ("uses nonvac_kill here", "snake"), ("caf\u00e9", "ASCII")]:
    r = P.problems({"a.b": bad}); assert r, f"negative self-test: {bad!r} not reported"
assert P.problems({"a.b": "fine"}) == []
m = {"id": "verified.unproved_escapes", "definition": "technical sorry_pattern text"}
assert C.meaning(m) == P.PLAIN[m["id"]], "card does not show the plain meaning"
print("plain meanings: ok", len(ids))
PY
ran_case   # the python block above asserts every metric has a plain meaning and each negative case is reported; it printed its ok line and exited 0
ran_done test_plain_meanings
