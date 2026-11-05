#!/usr/bin/env bash
# Tier 1: Level 1 slice 1: the proof manifest (scorecard/scorecard_manifest.py) and the allowlist rule of the runner. A good manifest loads; every required key removed in turn is rejected naming the key;
# unknown keys and sections, wrong types, a path that escapes, a malformed hash, a duplicate or empty claim list, equal generator and compiler ids and a manifest holding no [[artifact]] are rejected; `scorecard certify`
# reads the manifest from the PINNED commit, executes nothing and leaves the scratch clone removed; and the runner REFUSES a repo whose origin is not on the allowlist (SPEC rule 10), at both levels.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/0001-ran-evidence.md)
sc=$(pwd)/scorecard/scorecard; here=$(pwd)
fail() { echo "tier1: manifest: $*" >&2; exit 1; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT; export TMPDIR=$T/tmp; mkdir -p "$TMPDIR"
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_SYSTEM=/dev/null GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
H=$(printf 'a%.0s' $(seq 64))
manifest() { cat <<TOML
[export]
path = "proof/export.ndjson"
sha256 = "$H"
lean_version = "4.35.0"
[claims]
theorems = ["Demo.parse_ok", "Demo.parse_total"]
definitions = ["Demo.parse"]
[[artifact]]
path = "build/demo.wasm"
kind = "wasm"
allowed_symbols = []
[binding]
generator = "T3"
compiler = "T4"
[source]
globs = ["Demo/**/*.lean"]
[proof]
sorry_pattern = "\\\\b(sorry|admit|axiom|unsafe)\\\\b"
allow_marker = "allow"
[trust]
c_files = ["c/*.c"]
ledger = "docs/trust-ledger.md"
entry_regex = "^### T[0-9]"
[tests]
generated = ["vectors/**"]
extra = []
gate_selftests = ["scripts/test_*.sh"]
entry_points = ["parse"]
scenario_files = []
[velocity]
window_hours = 168
TOML
}
load() { python3 - "$1" <<'PY'
import sys; sys.path.insert(0, "scorecard"); import scorecard_manifest as m
try: m.load(open(sys.argv[1]).read())
except m.ManifestError as e: print(e); sys.exit(1)
PY
}
manifest > "$T/m.toml"; load "$T/m.toml" && ran_case || fail "a good manifest was rejected"
rej() {   # rej DESCRIPTION SUBSTRING < manifest text
  cat > "$T/bad.toml"; load "$T/bad.toml" > "$T/out" && fail "negative self-test: $1 was accepted"; grep -q -- "$2" "$T/out" && ran_case || fail "$1: wrong finding: $(cat "$T/out")"; }
# every required key, removed one at a time (sections and the [[artifact]] keys included)
python3 - "$T/m.toml" <<'PY' > "$T/keys"
import sys, tomllib; d = tomllib.load(open(sys.argv[1], "rb"))
for s, v in d.items():
    if s == "artifact": [print(f"artifact {k}") for k in v[0]]
    else: [print(f"{s} {k}") for k in v]
PY
n=0; while read -r sec key; do
  n=$((n + 1))
  if [ "$sec" = artifact ]; then sed "/^\\[\\[artifact\\]\\]/,/^\\[binding\\]/{/^$key = /d}" "$T/m.toml"; else sed "/^\\[$sec\\]/,/^\\[/{/^$key = /d}" "$T/m.toml"; fi | rej "removing [$sec] $key" "missing key"
done < "$T/keys"
[ "$n" -ge 22 ] && ran_case || fail "only $n keys were removed in turn: the schema walk did not run"
sed '/^\[\[artifact\]\]/,/^allowed_symbols/d' "$T/m.toml" | rej "a manifest with no artifact" "at least one \[\[artifact\]\]"
sed '/^\[binding\]/,/^compiler/d' "$T/m.toml" | rej "a manifest with no [binding] section" "missing section .binding."
{ cat "$T/m.toml"; echo 'x = 1'; } | rej "an unknown key (appended to [velocity])" "unknown key .velocity. x"
{ cat "$T/m.toml"; printf '[extra]\nx = 1\n'; } | rej "an unknown section" "unknown section .extra."
sed 's#path = "proof/export.ndjson"#path = "../export.ndjson"#' "$T/m.toml" | rej "an export path that escapes" "absolute, empty or"
sed 's#path = "proof/export.ndjson"#path = "/etc/passwd"#' "$T/m.toml" | rej "an absolute export path" "absolute, empty or"
sed 's#path = "build/demo.wasm"#path = "a/../../x"#' "$T/m.toml" | rej "an artifact path that escapes" "absolute, empty or"
sed 's#c_files = \["c/\*.c"\]#c_files = ["../c/*.c"]#' "$T/m.toml" | rej "a trusted-file glob that escapes" "absolute, empty or"
sed "s/sha256 = \"$H\"/sha256 = \"ABC\"/" "$T/m.toml" | rej "a malformed export hash" "64 lower-case hex"
sed 's/kind = "wasm"/kind = "exe"/' "$T/m.toml" | rej "an artifact kind that is not wasm or object" "kind must be"
sed 's/allowed_symbols = \[\]/allowed_symbols = ["a b"]/' "$T/m.toml" | rej "a symbol name with a space" "allowed_symbols must be symbol names"
sed 's/theorems = \[.*\]/theorems = []/' "$T/m.toml" | rej "no claim theorem" "1..200 distinct"
sed 's/theorems = \[.*\]/theorems = ["A", "A"]/' "$T/m.toml" | rej "a duplicated claim theorem" "1..200 distinct"
sed 's/definitions = \[.*\]/definitions = ["a b"]/' "$T/m.toml" | rej "a definition name with a space" "1..200 distinct"
sed 's/compiler = "T4"/compiler = "T3"/' "$T/m.toml" | rej "one ledger entry as both generator and compiler" "two different ledger entries"
sed 's/generator = "T3"/generator = "rm -rf"/' "$T/m.toml" | rej "a ledger id that is not an id" "trust-ledger entry id"
sed 's/window_hours = 168/window_hours = "168"/' "$T/m.toml" | rej "a mistyped window" "must be int"
sed 's/window_hours = 168/window_hours = 0/' "$T/m.toml" | rej "a zero window" "window_hours must be"
sed 's/entry_regex = .*/entry_regex = "("/' "$T/m.toml" | rej "an invalid regex" "not a valid regex"
sed 's/lean_version = "4.35.0"/lean_version = 4/' "$T/m.toml" | rej "a mistyped self-reported field" "must be str"
echo 'not toml [' | rej "a file that is not TOML" "not valid TOML"
# `scorecard certify`: reads the manifest from the PINNED commit, runs nothing, removes its scratch clone; the allowlist is enforced at both levels
printf 'repos = ["example/fixture"]\nmeasured_per_month = 1\n' > "$T/allow.toml"
S=$T/subject; mkdir -p "$S"; git init -q -b main "$S"; ( cd "$S"; manifest > vbm-proof.toml; git remote add origin git@github.com:example/fixture.git; git add -A; git commit -qm "feat(fix): fixture" ); sha=$(git -C "$S" rev-parse HEAD)
sed -i 's/Demo.parse_ok/Demo.later/' "$S/vbm-proof.toml"; git -C "$S" commit -qam "feat(fix): later"
snap() { find "$1" -xdev -printf '%p %y %s %T@\n' | sort | sha256sum; }
before=$(snap "$S"); "$sc" certify --repo "$S" --commit "$sha" --allowlist "$T/allow.toml" > "$T/card.json" 2> "$T/err" && ran_case || fail "certify refused a good subject: $(cat "$T/err")"
[ "$(snap "$S")" = "$before" ] && [ -z "$(ls "$TMPDIR")" ] && ran_case || fail "certify mutated the subject or left its scratch clone"
python3 - "$T/card.json" "$sha" "$(git -C "$S" show "$sha:vbm-proof.toml" | sha256sum | cut -d' ' -f1)" <<'PY' && ran_case || fail "the certify output does not name the pinned commit and the manifest hash it read"
import json, sys; c = json.load(open(sys.argv[1])); assert c["schema"] == "scorecard-2" and c["level"] == 1 and c["subject"]["commit"] == sys.argv[2] and c["manifest"]["sha256"] == sys.argv[3], c
PY
"$sc" certify --repo "$S" --commit "$sha" --manifest nope.toml --allowlist "$T/allow.toml" > /dev/null 2> "$T/err" && fail "negative self-test: certify accepted a missing manifest"; grep -q "no manifest" "$T/err" && ran_case || fail "wrong message: $(cat "$T/err")"
git -C "$S" show "$sha:vbm-proof.toml" | sed '/^\[velocity\]/,$d' > "$S/vbm-proof.toml"; git -C "$S" commit -qam "feat(fix): broken"
"$sc" certify --repo "$S" --commit HEAD --allowlist "$T/allow.toml" > /dev/null 2> "$T/err" && rc=0 || rc=$?; [ "$rc" = 2 ] && grep -q "missing section .velocity." "$T/err" && ran_case || fail "negative self-test: certify accepted a broken manifest: $(cat "$T/err")"
# the allowlist: an origin that is not on it is refused (exit 2) with the isolation requirement named, at Level 1 and Level 2, and nothing is cloned; the real allowlist refuses this fixture too
git -C "$S" remote set-url origin https://github.com/evil/widget.git
for cmd in certify run; do
  "$sc" $cmd --repo "$S" --commit "$sha" --allowlist "$T/allow.toml" > /dev/null 2> "$T/err" && rc=0 || rc=$?
  [ "$rc" = 2 ] && grep -q "not allowlisted: outside submissions wait for the Level 2 isolation (scorecard/SPEC.md" "$T/err" && [ -z "$(ls "$TMPDIR")" ] && ran_case || fail "negative self-test: $cmd accepted a repo that is not allowlisted (exit $rc): $(cat "$T/err")"
done
git -C "$S" remote set-url origin git@github.com:example/fixture.git
"$sc" certify --repo "$S" --commit "$sha" > /dev/null 2> "$T/err" && fail "negative self-test: the REAL allowlist accepted the example fixture"; grep -q "not allowlisted" "$T/err" && ran_case || fail "wrong message: $(cat "$T/err")"
git -C "$S" remote set-url origin https://gitlab.com/example/fixture.git
"$sc" certify --repo "$S" --commit "$sha" --allowlist "$T/allow.toml" > /dev/null 2> "$T/err" && fail "negative self-test: a non-GitHub remote was accepted"
ran_done test_manifest
echo "tier1: manifest: the proof manifest schema (every key, types, paths, hashes, claims, binding) is enforced; certify reads the pinned commit and runs nothing; a repo that is not allowlisted is refused at both levels: ok"
