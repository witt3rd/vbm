#!/usr/bin/env bash
# Tier 1: scripts/hub-areas composes .land/areas.json from the libraries' own declarations, deterministically, and refuses what the contract refuses (vbm-land docs/family-repo.md 1.3). The committed file is the composition; each refusal has a case that provokes it.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. .land/tool/lib/ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (.land/tool/docs/ran-evidence.md)
ha=$(pwd)/scripts/hub-areas
fail() { echo "tier1: hub-areas: $*" >&2; exit 1; }
"$ha" --check && ran_case || fail ".land/areas.json is not the composition of lib/*/areas.json"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/.land" "$T/lib/alpha" "$T/lib/beta"
git -C "$T" init -q
lib() { printf '%s\n' "$2" > "$T/lib/$1/areas.json"; }
lib alpha '{"version":1,"areas":[{"name":"alpha","paths":["*"],"steps":[{"run":"mise exec -- scripts/tier1.sh"}]}]}'
lib beta  '{"version":1,"areas":[{"name":"beta__defs","paths":["Beta/*"],"steps":[{"run":"lake build Beta","cwd":"build"}]},{"name":"beta__proofs","paths":["BetaProofs/*","areas.json","deps"],"steps":[{"run":"lake build BetaProofs"}]}]}'
echo alpha > "$T/lib/beta/deps"; mkdir -p "$T/lib/beta/Beta" "$T/lib/beta/BetaProofs" "$T/lib/alpha"; : > "$T/lib/beta/Beta/A.lean"; : > "$T/lib/beta/BetaProofs/B.lean"; : > "$T/lib/alpha/x"
git -C "$T" add -A
export HUB_GATE_AREAS="hub alpha"   # the fixture has no vbm-rng
out=$("$ha" --root "$T"); echo "$out" | python3 -c '
import sys, json
d = json.load(sys.stdin)["areas"]; n = [a["name"] for a in d]
assert n == ["hub", "alpha", "beta__defs", "beta__proofs"], n
g = {"run": "mise exec -- scripts/repo-gates.sh"}
assert all(a["steps"][0] == g for a in d), "the whole-repository gates are not the first step of every area"
a = {x["name"]: x for x in d}
assert a["alpha"]["steps"][1] == {"run": "mise exec -- scripts/tier1.sh", "cwd": "lib/alpha"}
assert a["beta__defs"]["steps"][1] == {"run": "lake build Beta", "cwd": "lib/beta/build"}
assert "lib/beta/Beta/*" in a["beta__defs"]["paths"] and "lib/alpha/*" in a["beta__defs"]["paths"], "the default uses is the whole dependency closure"
' && ran_case || fail "the composition of two libraries (one with two areas and a dependency) is wrong"
[ "$out" = "$("$ha" --root "$T")" ] && ran_case || fail "the composition is not deterministic"
# documents no gate reads are an inert area: excluded from the library's main area, owned by its own area with no steps, and NOT part of what a dependent depends on
lib alpha '{"version":1,"areas":[{"name":"alpha","paths":["*"],"exclude":["README.md"],"steps":[{"run":"mise exec -- scripts/tier1.sh"}]},{"name":"alpha__docs","paths":["README.md"],"steps":[]}]}'
lib beta '{"version":1,"areas":[{"name":"beta","paths":["*"],"exclude":["README.md"],"steps":[{"run":"true"}]},{"name":"beta__docs","paths":["README.md"],"steps":[]}]}'
touch "$T/lib/alpha/README.md" "$T/lib/beta/README.md"; git -C "$T" add -A
"$ha" --root "$T" | python3 -c '
import sys, json
a = {x["name"]: x for x in json.load(sys.stdin)["areas"]}
assert a["alpha"]["exclude"] == ["lib/alpha/README.md"], a["alpha"]
assert a["alpha__docs"]["paths"] == ["lib/alpha/README.md"] and len(a["alpha__docs"]["steps"]) == 1, "the inert area keeps only the whole-repository gates"
assert "lib/alpha/README.md" in a["beta"]["exclude"] and "lib/alpha/*" in a["beta"]["paths"], "a dependent carries the excludes of what it depends on"
assert a["beta__docs"]["paths"] == ["lib/beta/README.md"], "an inert area does not inherit the dependency closure"
' && ran_case || fail "the inert documents area is composed wrongly (exclude, own area, or the dependency closure)"
# put the fixture back as the later cases expect it
lib alpha '{"version":1,"areas":[{"name":"alpha","paths":["*"],"steps":[{"run":"mise exec -- scripts/tier1.sh"}]}]}'
lib beta '{"version":1,"areas":[{"name":"beta__defs","paths":["Beta/*"],"steps":[{"run":"lake build Beta","cwd":"build"}]},{"name":"beta__proofs","paths":["BetaProofs/*","areas.json","deps"],"steps":[{"run":"lake build BetaProofs"}]}]}'
rm -f "$T/lib/alpha/README.md" "$T/lib/beta/README.md"; git -C "$T" add -A -f
echo "$out" | python3 -c 'import sys, json; d = json.load(sys.stdin); assert d["gate_areas"] == ["hub", "alpha"] and all(g in [a["name"] for a in d["areas"]] for g in d["gate_areas"])' && ran_case || fail "gate_areas is not emitted, or names an area that does not exist"
HUB_GATE_AREAS="hub nope" "$ha" --root "$T" >/dev/null 2>"$T/err" && fail "negative self-test: a gate area that is not an area passed"; grep -q "is not an area" "$T/err" && ran_case || fail "wrong message: $(cat "$T/err")"
lib beta '{"version":1,"areas":[{"name":"beta__defs","paths":["Beta/*","BetaProofs/*","areas.json","deps"],"steps":[{"run":"true"}],"uses":[{"lib":"alpha","area":"alpha"}]}]}'
"$ha" --root "$T" | python3 -c 'import sys, json; a = {x["name"]: x for x in json.load(sys.stdin)["areas"]}; assert a["beta__defs"]["paths"][-1] == "lib/alpha/*"' && ran_case || fail "a declared uses does not add the named area"
refuses() {   # refuses WHAT PATTERN: the composition fails with exit 2 and a message naming the cause
  "$ha" --root "$T" >/dev/null 2>"$T/err" && fail "negative self-test: $1 was NOT refused"
  grep -q "$2" "$T/err" && ran_case || fail "$1: wrong message: $(cat "$T/err")"
}
lib beta '{"version":1,"areas":[{"name":"gamma","paths":["*"],"steps":[{"run":"true"}]}]}'; refuses "an area whose name does not start with its library's" "must be 'beta'"
lib beta '{"version":1,"areas":[{"name":"beta","paths":["../alpha/*"],"steps":[{"run":"true"}]}]}'; refuses "a path that leaves the library" "leaves the library"
lib beta '{"version":1,"areas":[{"name":"beta","paths":["Beta/*"],"steps":[{"run":"true"}]}]}'; refuses "a library path no area owns" "owned by no area"
lib beta '{"version":1,"areas":[{"name":"beta","paths":["*"],"steps":[{"run":"true"}],"extra":1}]}'; refuses "an unknown key" "unknown key 'extra'"
lib beta '{"version":1,"areas":[{"name":"beta","paths":["*"],"steps":[{"run":"true"}],"uses":[{"lib":"zeta"}]}]}'; refuses "a uses outside the dependency closure" "not in the library's dependency closure"
echo zeta > "$T/lib/beta/deps"; lib beta '{"version":1,"areas":[{"name":"beta","paths":["*"],"steps":[{"run":"true"}]}]}'; refuses "an unknown dependency" "unknown library 'zeta'"
echo alpha > "$T/lib/beta/deps"; echo beta > "$T/lib/alpha/deps"; refuses "a dependency cycle" "dependency cycle"
rm "$T/lib/alpha/deps"; lib beta '{"version":1,"areas":[{"name":"beta","paths":["*"],"steps":[{"run":"true"}]}]}'
"$ha" --root "$T" --write; "$ha" --root "$T" --check && ran_case || fail "a written file does not check"
echo ' ' >> "$T/.land/areas.json"; "$ha" --root "$T" --check >/dev/null 2>&1 && fail "negative self-test: a hand-edited areas file passed --check"; ran_case
ran_done test_hub_areas
echo "tier1: hub-areas: the areas file is the composition of the libraries' declarations (defaults, uses, determinism) and each refusal is provoked: ok"
