#!/usr/bin/env bash
# Tier 1: the registry validator (scorecard/registry-validate): every entry in registry/ is valid, and the validator is shown able to reject: a bad file name, a missing or unknown key, a repo URL that does not match the
# file name, a short or non-hex commit, a manifest or adapter path that escapes, a score written by a contributor ([latest] changed from main), a PR that touches anything but exactly one entry, a repo that is NOT ON THE ALLOWLIST
# (SPEC rule 10: refused with a message naming the isolation requirement), a PR that edits the allowlist, a Level 2 request without a reason or approved by a contributor, and more approvals in a month than the cap.
export LC_ALL=C
set -euo pipefail
cd "$(dirname "$0")/.."
. scripts/lib-ran.sh   # ran_case counts each executed check, ran_done prints the evidence line `ran: NAME: N cases` (docs/0001-ran-evidence.md)
v=$(pwd)/scorecard/registry-validate
fail() { echo "tier1: registry: $*" >&2; exit 1; }
for e in registry/*__*.toml; do "$v" "$e" && ran_case || fail "a registry entry is invalid: $e"; done
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT; mkdir -p "$T/registry" "$T/base/registry"
printf 'repos = ["acme/widget", "acme/other"]\nmeasured_per_month = 1\n' > "$T/allow.toml"
good() { cat <<TOML
kind = "library"
status = "live"
what = "A widget"
milestone = "m"
depends_on = []
repo = "https://github.com/acme/widget"
commit = "$(printf 'a%.0s' $(seq 40))"
manifest = "vbm-proof.toml"
targets = ["C", "Rust"]

[latest]
date = ""
correctness = "unscored"
landedness = "unscored"
level = "unscored"
card = ""
TOML
}
V() { "$v" --allowlist "$T/allow.toml" "$@"; }
MEAS='[measured]\nreason = "Our own library whose throughput against comparators is the evidence."\nadapter = "scorecard.toml"\napproved = "%s"\n'
meas() { { good | sed '/^\[latest\]/,$d'; printf "$MEAS" "$1"; good | sed -n '/^\[latest\]/,$p'; } ; }
bad() {   # bad DESCRIPTION SUBSTRING-OF-FINDING < entry text   (the entry is acme__widget.toml)
  cat > "$T/registry/acme__widget.toml"; V "$T/registry/acme__widget.toml" > "$T/out" && fail "negative self-test: $1 was accepted"; grep -q -- "$2" "$T/out" && ran_case || fail "$1: wrong finding: $(cat "$T/out")"; }
good > "$T/registry/acme__widget.toml"; V "$T/registry/acme__widget.toml" && ran_case || fail "a valid fixture entry was rejected"
good | sed '/^commit/d' | bad "a missing key" "missing key commit"
good | sed '/^what/d' | bad "a missing common key" "missing key what"
good | sed 's/status = "live"/status = "soon"/' | bad "an unknown status" "status must be one of"
good | sed 's/kind = "library"/kind = "gadget"/' | bad "an unknown kind" "kind must be one of"
good | sed 's/status = "live"/status = "planned"/' | bad "a repo key on an entry that is not live" "only allowed when status is live"
# an entry that is not public carries the common keys only and is unscored
printf 'kind = "tool"\nstatus = "planned"\nwhat = "x"\nmilestone = "m"\ndepends_on = []\n' > "$T/registry/acme__soon.toml"; V "$T/registry/acme__soon.toml" && ran_case || fail "a planned entry without scoring keys was rejected"
printf 'kind = "tool"\nstatus = "planned"\nwhat = "x"\nmilestone = "m"\ndepends_on = []\n' > "$T/registry/evil__soon.toml"; V "$T/registry/evil__soon.toml" >/dev/null && fail "negative self-test: a planned entry of a non-allowlisted owner was accepted"
good | sed '/^targets/d' | bad "a missing targets key" "missing key targets"
good | sed 's/targets = .*/targets = []/' | bad "empty targets" "targets must be"
good | sed 's/targets = .*/targets = ["C; rm -rf"]/' | bad "a target that is not a short language name" "targets must be"
{ echo 'extra = 1'; good; } | bad "an unknown key" "unknown key extra"
# a live TOOL is listed and linked, never scored: it carries the repo and none of the scoring keys; the kind is no way round the rules for a library
tool() { printf 'kind = "tool"\nstatus = "live"\nwhat = "A tool"\nmilestone = "m"\ndepends_on = []\nrepo = "https://github.com/acme/widget"\n'; }
tool > "$T/registry/acme__widget.toml"; V "$T/registry/acme__widget.toml" && ran_case || fail "a live tool entry with a repo and no scoring keys was rejected"
tool | sed '/^repo/d' | bad "a live tool without its link" "missing key repo"
tool | sed 's#acme/widget#acme/other#' | bad "a tool whose repo does not match the file name" "repo must be"
{ tool; echo 'commit = "'"$(printf 'a%.0s' $(seq 40))"'"'; } | bad "a tool carrying a commit to score" "commit is not allowed on a tool entry"
{ tool; echo 'manifest = "vbm-proof.toml"'; } | bad "a tool carrying a manifest" "manifest is not allowed on a tool entry"
{ tool; echo 'targets = ["C"]'; } | bad "a tool carrying targets" "targets is not allowed on a tool entry"
{ tool; printf '[latest]\ndate = ""\ncorrectness = "unscored"\nlandedness = "unscored"\nlevel = "unscored"\ncard = ""\n'; } | bad "a tool carrying a [latest] block" "latest is not allowed on a tool entry"
{ tool; printf '[measured]\nreason = "Our own tool whose throughput against comparators is the evidence."\nadapter = "scorecard.toml"\napproved = ""\n'; } | bad "a tool asking for Level 2" "only allowed when status is live and the kind is not tool"
good | sed 's/kind = "library"/kind = "tool"/' | bad "a scored library relabelled a tool" "is not allowed on a tool entry"
good | sed 's/kind = "library"/kind = "foundation"/' > "$T/registry/acme__widget.toml"; V "$T/registry/acme__widget.toml" && ran_case || fail "a live foundation entry with its scoring keys was rejected"
good | sed 's/kind = "library"/kind = "foundation"/' | sed '/^manifest/d' | bad "a foundation piece without a manifest" "missing key manifest"
tool | sed 's#acme/widget#evil/widget#' | sed 's#^repo = .*#repo = "https://github.com/evil/widget"#' | { cat > "$T/registry/evil__widget.toml"; V "$T/registry/evil__widget.toml" > "$T/out" && fail "negative self-test: a live tool of a non-allowlisted repo was accepted"; grep -q "not allowlisted" "$T/out" && ran_case || fail "wrong refusal for a non-allowlisted tool: $(cat "$T/out")"; }
good | sed 's#acme/widget#acme/other#' | bad "a repo that does not match the file name" "repo must be"
good | sed 's#https://#http://#' | bad "a non-https URL" "repo must be"
good | sed 's/commit = "a*"/commit = "abc123"/' | bad "a short commit" "40-hex"
good | sed 's/commit = "a*"/commit = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"/' | bad "an upper-case commit" "40-hex"
good | sed 's#vbm-proof.toml#../../etc/x.toml#' | bad "a manifest path that escapes" "manifest must be"
good | sed 's#vbm-proof.toml#/etc/x.toml#' | bad "an absolute manifest path" "manifest must be"
good | sed '/^manifest/d' | bad "a missing manifest" "missing key manifest"
good | sed 's/level = "unscored"/level = "gold"/' | bad "an unknown level" "level must be one of"
meas "" | sed 's#scorecard.toml#../x.toml#' | bad "a measured adapter path that escapes" "adapter must be"
meas "" | sed 's/reason = .*/reason = "because"/' | bad "a Level 2 request without a real reason" "at least 40 characters"
meas "2026-1-1" | bad "a malformed approval date" "approved is empty or"
meas "" | sed 's/^approved = .*/&\nx = 1/' | bad "an unknown key in [measured]" "unknown key .measured. x"
good | sed 's/correctness = "unscored"/correctness = "great"/' | bad "an unknown verdict" "correctness must be pass or fail and landedness"
good | sed 's/correctness = "unscored"/correctness = "pass"/; s/landedness = "unscored"/landedness = "pass"/' | bad "a score without date and card" "scored entry needs"
good | sed 's/correctness = "unscored"/correctness = "pass"/' | bad "one verdict scored and the other unscored" "correctness must be pass or fail and landedness"
good | sed 's/correctness = "unscored"/correctness = "pending"/' | bad "a half-pending entry" "correctness must be pass or fail and landedness"
good | sed 's/correctness = "unscored"/correctness = "pass"/; s/landedness = "unscored"/landedness = "unscored"/' | bad "a correctness verdict beside an unscored landedness" "correctness must be pass or fail and landedness\|an unscored entry has"
good | sed '/^correctness/d' | bad "a missing verdict" "correctness missing"
good | sed 's/^correctness = .*/result = "unscored"/' | bad "the retired blended result key" "unknown key"
cp "$T/registry/acme__widget.toml" "$T/registry/bad name.toml"; V "$T/registry/bad name.toml" >/dev/null && fail "a bad file name was accepted"
# the allowlist (SPEC rule 10): an entry for a repo that is not on it is REFUSED with the isolation requirement named; the real registry entries are all on the real allowlist
good | sed 's#acme/widget#evil/widget#' | sed 's#^repo = .*#repo = "https://github.com/evil/widget"#' > "$T/registry/evil__widget.toml"
V "$T/registry/evil__widget.toml" > "$T/out" && fail "negative self-test: an entry for a repo that is not allowlisted was accepted"; grep -q "not allowlisted: outside submissions wait for the Level 2 isolation (scorecard/SPEC.md" "$T/out" && ran_case || fail "wrong refusal for a non-allowlisted repo: $(cat "$T/out")"
"$v" "$T/registry/evil__widget.toml" > /dev/null && fail "negative self-test: the REAL allowlist accepts an outside repo"
printf 'repos = ["acme/widget"]\n' > "$T/allow-bad.toml"; "$v" --allowlist "$T/allow-bad.toml" "$T/registry/acme__widget.toml" > /dev/null 2>&1 && fail "negative self-test: a malformed allowlist was accepted"
# Level 2 requests: a request with an approval is valid; the monthly cap (1 here) is enforced across entries; a contributor cannot approve
meas "2026-11-04" > "$T/registry/acme__widget.toml"; V "$T/registry/acme__widget.toml" && ran_case || fail "an approved Level 2 request was rejected"
meas "2026-11-09" | sed 's#acme/widget#acme/other#' | sed 's#^repo = .*#repo = "https://github.com/acme/other"#' > "$T/registry/acme__other.toml"; V "$T/registry/acme__other.toml" > "$T/out" && fail "negative self-test: two approvals in a month over a cap of one were accepted"; grep -q "exceed measured_per_month" "$T/out" && ran_case || fail "wrong finding for the monthly cap: $(cat "$T/out")"
meas "2026-12-09" | sed 's#^repo = .*#repo = "https://github.com/acme/other"#' > "$T/registry/acme__other.toml"; V "$T/registry/acme__other.toml" && ran_case || fail "an approval in another month was rejected"
rm "$T/registry/acme__other.toml"; meas "" > "$T/registry/acme__widget.toml"; cp "$T/registry/acme__widget.toml" "$T/base/registry/acme__widget.toml"; meas "2026-11-04" > "$T/registry/acme__widget.toml"
V --pr-file registry/acme__widget.toml --base-root "$T/base" "$T/registry/acme__widget.toml" > "$T/out" && fail "negative self-test: a contributor approved their own Level 2 request"; grep -q "only a maintainer approves" "$T/out" && ran_case || fail "wrong finding for a self-approval: $(cat "$T/out")"
V --pr-file registry/allowlist.toml --base-root "$T/base" "$T/registry/acme__widget.toml" > /dev/null && fail "negative self-test: a PR that edits the allowlist was accepted"
V --pr-file registry/allowlist.toml --pr-file registry/acme__widget.toml --base-root "$T/base" "$T/registry/acme__widget.toml" > /dev/null && fail "negative self-test: a PR that edits the allowlist next to an entry was accepted"
rm -f "$T/base/registry/acme__widget.toml"
# PR mode: exactly one entry; [latest] equal to main's
good > "$T/registry/acme__widget.toml"; good > "$T/base/registry/acme__widget.toml"
V --pr-file registry/acme__widget.toml --base-root "$T/base" "$T/registry/acme__widget.toml" && ran_case || fail "a clean one-entry PR was rejected"
V --pr-file registry/acme__widget.toml --pr-file scripts/x.sh --base-root "$T/base" "$T/registry/acme__widget.toml" >/dev/null && fail "negative self-test: a PR touching a script was accepted"
V --pr-file registry/scores/acme__widget.json --base-root "$T/base" "$T/registry/acme__widget.toml" >/dev/null && fail "negative self-test: a PR writing a score file was accepted"
V --pr-file registry/a__b.toml --pr-file registry/c__d.toml "$T/registry/acme__widget.toml" >/dev/null && fail "negative self-test: a PR with two entries was accepted"
good > "$T/registry/acme__widget.toml"; good > "$T/base/registry/acme__widget.toml"
sed -i 's/correctness = "unscored"/correctness = "pass"/; s/landedness = "unscored"/landedness = "pending"/; s/level = "unscored"/level = "certified"/; s/date = ""/date = "2026-11-04"/; s#card = ""#card = "registry/scores/acme__widget.json"#' "$T/registry/acme__widget.toml"
V "$T/registry/acme__widget.toml" && ran_case || fail "a scored entry with date and card was rejected"
V --pr-file registry/acme__widget.toml --base-root "$T/base" "$T/registry/acme__widget.toml" > "$T/out" && fail "negative self-test: a contributor-written score was accepted"; grep -q "only the scoring job" "$T/out" && ran_case || fail "wrong finding for a contributor-written score: $(cat "$T/out")"
# a tool on the allowlist is NOT scored automatically: scoring is only ever an explicit run (scorecard run|certify --repo --commit, a manifest for certify), no code enumerates registry/ to pick subjects,
# and a tool entry has no commit, manifest or card to score, so its row stays unscored however the allowlist reads
grep -q '"witt3rd/vbm-land"' registry/allowlist.toml && grep -q '^kind = "tool"' registry/witt3rd__vbm-land.toml && ran_case || fail "the real registry no longer lists vbm-land as an allowlisted tool (the cases below read it)"
for k in commit manifest targets latest measured; do ! grep -q "^\[\?$k" registry/witt3rd__vbm-land.toml && ran_case || fail "the vbm-land tool entry carries $k: a tool is never scored"; done
readers=$(grep -l 'registry/\|\*__\*\.toml' scorecard/scorecard scorecard/scorecard_*.py scorecard/registry-* 2>/dev/null | sed 's#.*/##' | sort | tr '\n' ' ')
case "$readers" in "registry-table registry-validate scorecard ") ran_case ;; *) fail "a new reader of registry/ appeared ($readers): a scoring job must not pick subjects from the registry or allowlist without a test here" ;; esac
grep -n 'registry/\|__\*\.toml' scorecard/scorecard scorecard/scorecard_policy.py | grep -v -i 'allowlist\|#\|"""' > "$T/enum" || true; [ ! -s "$T/enum" ] && ran_case || fail "the scorer reads registry entries: $(cat "$T/enum")"
scorecard/registry-table --root "$(pwd)" | grep '^| \[vbm-land\]' | grep -q '| tool | live | unscored | unscored | - |$' && ran_case || fail "the vbm-land row is not an unscored tool row with no card"
ran_done test_registry
echo "tier1: registry: entries validate; bad names, keys, URLs, commits, adapter paths, contributor-written scores and multi-file PRs are rejected; a non-allowlisted repo, a self-approved or over-cap Level 2 request and an allowlist edit (protected-set) are refused: ok"
