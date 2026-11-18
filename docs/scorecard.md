# Scorecard

Status: draft by a worker, 2026-11-18; goals and targets are the owner's to set.

This is the scorecard of the vbm repository itself (the hub: the guidelines, the scorecard program and the registry), not of a library it scores. It follows the project scorecard format: each metric is an integer with a direction, a floor that only moves toward better (set equal to the value now), a target the owner sets, and a history (add a dated row to the table's `now` when it is re-measured; git keeps the earlier values). The scorecard program in `scorecard/` scores other repositories; the metrics here are about this one.

## Goals as the repository states them

- **G1.** Publish the guidelines: best practices for agent-built, verified-by-construction software, in small files of one idea each. Source: AGENTS.md:19; guidelines/INDEX.md:3; README.md:94.
- **G2.** Keep every page a third party reads true to the repository: README, ROADMAP, guidelines, skills and registry change together, and a page that no longer matches reality is a defect (the guidelines are all linked from README.md and listed in guidelines/INDEX.md). Source: AGENTS.md:13; scripts/test_readme.sh:12; README.md:92-99.
- **G3.** Stay public-ready at every commit: no private name, no path of ours, no retired name anywhere in the tree. Source: AGENTS.md:44; CONTRIBUTING.md:21.
- **G4.** Keep the registry table in README.md a generated render of `registry/*.toml` and their cards, never a second source. Source: AGENTS.md:22; scripts/test_readme.sh:2.
- **G5.** Keep a registry of scored repositories, each scored by a program with a card (correctness first, landedness second). That the live ones all reach a card is my reading of README.md:7 ("no card yet"), not a stated target. Source: AGENTS.md:21; README.md:7; MANIFESTO.md:14.
- **G6.** Record the owner's decisions on the scorecard, and decide anything reversible without waiting. Source: scorecard/DECISIONS.md:1; AGENTS.md:7.
- **G7.** Take the landing tool as a pinned, hash-checked, unedited copy. Source: AGENTS.md:6; README.md:50.
- **G8.** Gate every change with Tier 1, every gate with a negative self-test, and run each test script to real cases (ran-evidence). Source: AGENTS.md:39; AGENTS.md:48; scripts/tier1.sh:8.
- **G9.** Velocity: the fast gate warm under 60 s, a cold clone within 600 s, 0 open pull requests. Source: README.md:76; AGENTS.md:31.

## Metrics

All values were measured on 2026-11-18 at commit `6c69857` unless marked `unmeasured`. Every command is run from the repository root; `mise exec -- ...` is the repository's own prefix. Units are in the names: `-count` is a count, `-lines` a line count, `-seconds` a duration in seconds, `-flag` is 0 for no and 1 for yes (a shell exit status).

| metric | direction (higher or lower is better) | goal it serves | how to measure (the exact command, from the repository root) | now (value and date) | floor (= now) | target (blank: the owner sets it) |
|---|---|---|---|---|---|---|
| `guidelines-count` | higher | G1 | `ls guidelines/*.md \| grep -vc INDEX.md` | 21 (2026-11-18) | 21 | |
| `guideline-longest-lines` | lower | G1 | `wc -l guidelines/*.md \| grep -v ' total$' \| grep -v INDEX.md \| sort -n \| tail -1 \| awk '{print $1}'` | 31 (2026-11-18) | 31 | |
| `guidelines-unlinked-from-readme-count` | lower | G2 | `for g in guidelines/*.md; do [ "$g" = guidelines/INDEX.md ] \|\| grep -q "($g)" README.md \|\| echo "$g"; done \| wc -l` | 0 (2026-11-18) | 0 | |
| `guidelines-unlisted-in-index-count` | lower | G2 | `for g in guidelines/*.md; do b=${g##*/}; [ "$b" = INDEX.md ] \|\| grep -q "\`$b\`" guidelines/INDEX.md \|\| echo "$b"; done \| wc -l` | 0 (2026-11-18) | 0 | |
| `broken-relative-links-count` | lower | G2 | `python3 -c "import re,glob,os;fs=['README.md','MANIFESTO.md','CONTRIBUTING.md','ROADMAP.md']+glob.glob('guidelines/*.md')+glob.glob('skills/*/SKILL.md')+glob.glob('docs/*.md');print(sum(1 for f in fs for t in re.findall(r'\]\(([^)#\s]+)',open(f).read()) if not re.match(r'[a-z]+:',t) and not os.path.exists(os.path.normpath(os.path.join(os.path.dirname(f),t)))))"` | 0 (2026-11-18) | 0 | |
| `public-lint-violations` | lower | G3 | `scripts/lint-public \| wc -l` | 0 (2026-11-18) | 0 | |
| `readme-table-drift-flag` | lower | G4 | `scorecard/registry-table --check README.md >/dev/null 2>&1; echo $?` | 0 (2026-11-18) | 0 | |
| `registry-live-entries-count` | higher | G5 | `grep -l '^status = "live"' registry/*__*.toml \| wc -l` | 12 (2026-11-18) | 12 | |
| `registry-live-unscored-count` | lower | G5 | `grep -L '^card = "registry' $(grep -l '^status = "live"' registry/*__*.toml) \| wc -l` | 10 (2026-11-18) | 10 | |
| `registry-failing-verdicts-count` | lower | G5 | `grep -hE '^(correctness\|landedness) = "fail"' registry/*__*.toml \| wc -l` | 2 (2026-11-18) | 2 | |
| `decisions-awaiting-owner-count` | lower | G6 | `grep -cE '^[0-9]+\. \*\*[^*]*(awaiting\|OPEN QUESTION)' scorecard/DECISIONS.md` | 4 (2026-11-18) | 4 | |
| `vendored-tool-failures-count` | lower | G7 | `(.land/tool/bin/land-check && .land/tool/bin/land-pin verify) >/dev/null 2>&1; echo $?` | 0 (2026-11-18) | 0 | |
| `tier1-failing-count` | lower | G8 | `mise exec -- scripts/tier1.sh >/dev/null 2>&1; echo $?` (exit status: 0 when every gate passes) | 0 (2026-11-18) | 0 | |
| `test-cases-ran-count` | higher | G8 | `mise exec -- scripts/tier1.sh 2>&1 \| grep '^ran: tests:' \| awk '{print $3}'` | 492 (2026-11-18) | 492 | |
| `tier1-seconds` | lower | G9 | `s=$(date +%s); mise exec -- scripts/tier1.sh >/dev/null 2>&1; echo $(( $(date +%s) - s ))` | 64 (2026-11-18; first run in a fresh worktree, so neither clearly warm nor cold) | 64 | |
| `open-pull-requests-count` | lower | G9 | `gh pr list --state open --json number --jq length` (needs `gh auth login` or GH_TOKEN and network) | unmeasured: no forge credentials or network in the jail | unmeasured | |

Notes on the table:
- `tier1-failing-count` is the exit status of the whole gate (`tier1: ok` and 14 scripts passed on 2026-11-18); `test-cases-ran-count` is the `ran: tests:` line the gate prints (the sum of the cases every test script reports).
- `tier1-seconds` is the whole gate on a fresh worktree, 64 s (user 37 s, system 15 s); the repository's floor for a warm run is 60 s and for a cold clone 600 s (README.md:76), so the warm figure needs a second run on a warm cache, which was not done (the gate runs once per piece of work).
- `registry-live-unscored-count` counts live entries with no card; the README says 2 of the live libraries are scored and the others are released and unscored (README.md:7).
- The vbm repository holds no Lean code, so the specified share, proof ledger, vectors and trust ledger of a library have no value here; they are measured per library by `scorecard/scorecard run` and sit on each library's card, not in this table.

## Health today

- **Nothing is regressed against its own floor**: every floor is today's value, so a first re-measure can only be equal or worse; the gate is green, the vendored tool is intact, the public lint is clean, the README table matches the registry, and every guideline is linked from README.md and listed in guidelines/INDEX.md.
- **Unmeasured:** `open-pull-requests-count` (needs forge credentials and a network, which the jail does not have). The cold-clone time of the gate, and a warm second run, are also not recorded. `tier1-seconds` is 64 s, just over the 60 s warm floor the repository states (README.md:76), though that run was not warm.
- **Far from where the goals point:** 10 of the 12 live registry entries have no card (`registry-live-unscored-count`) (two of those, vbm-land and vbm-rt, are a tool and a foundation the README says are not scored or not extracted yet); of the two scored libraries vbm-json fails both verdicts and vbm-sse passes both (`registry-failing-verdicts-count` is 2). Four decisions still wait for the owner (`decisions-awaiting-owner-count`).
- There is no history yet: the clone has no release tag (`git tag` is empty; the remote could not be reached), and the metrics have one dated value each.

## What a steward would do first

1. Score the ten live, unscored libraries, so that `registry-live-unscored-count` falls from 10 toward 0 (each score is a card the program writes; the table gets a real verdict for each).
2. Bring vbm-json to a passing card (its two failing verdicts) so `registry-failing-verdicts-count` falls from 2 to 0.
3. Take the gate under the 60 s warm line, or measure it warm and cold, so `tier1-seconds` is a real figure against the stated floors (and measure `open-pull-requests-count` on a host with the forge login).

## Questions for the owner

- Targets: none of the metrics has a target. What is the target for each, for example: how many guidelines are wanted (`guidelines-count`), and how many live entries should be scored (`registry-live-unscored-count`) and by when?
- Is the right unit of progress for the hub the guidelines and the registry, or should the scorecard program's own size and quality (1548 lines of runner; the repository states no goal for either) also be a goal? I did not add it.
- Should the four decisions awaiting the owner (DECISIONS 10, 11, 13, 15) count as a regression while they wait, and what is the date by which they are answered (`decisions-awaiting-owner-count`)?
- Is a release of this repository wanted (it has `VERSION` 0.1.0 and no tag in the clone I could see)? The repository states no release goal for itself, so no release metric is in the table.
- Which guidelines would be a goal to add (for example one per listed ideal)? The repository states the seven ideals but not how many guidelines each needs.
- Is the 60 s / 600 s floor for the gate (README.md:76) meant for this repository's Tier 1 as well, or only for the libraries it scores?
