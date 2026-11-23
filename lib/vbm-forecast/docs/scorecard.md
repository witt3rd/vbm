# Scorecard

Status: draft by a worker, 2026-11-19; goals and targets are the owner's to set.

## Goals as the repository states them
1. Verify forecasts: proper scoring rules (Brier, logarithmic, pinball, interval), calibration and reliability, and the comparison of two probabilistic forecasts, "in exact arithmetic or within a stated epsilon" (README.md:3, AGENTS.md:16, docs/decisions/0001-vbm-forecast.md:6).
2. Be the instrument for any claim that a forecast has edge or is trustworthy, so it is exact, deterministic and "its properties are proved" (docs/spec.md:6).
3. Prove every property the specification lists, one ledger claim each, with a non-vacuity witness; only `proved` may be called verified (docs/spec.md:166, docs/spec.md:227, docs/proof-ledger.md:5, AGENTS.md:25).
4. Stay pure: exact integer arithmetic or a proved epsilon, no floating point, no input or output, `VbmForecast` imports `Init` and itself only (docs/spec.md:8, AGENTS.md:18, AGENTS.md:33).
5. Forbid `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp`; build with zero warnings (AGENTS.md:24, CONTRIBUTING.md:7-8, scripts/check-zero-warning.sh:2).
6. Know the answers: known-answer vectors re-derived by an independent reference (docs/spec.md:190, docs/spec.md:224).
7. Refuse to issue a verdict of edge from fewer than `minEvents` events (docs/spec.md:135, docs/spec.md:159).
8. Account for what is trusted and nothing else (docs/spec.md:188, docs/trust-ledger.md:3-5).
9. Stay public-ready: no private name, path, number or e-mail (AGENTS.md:28).
10. Land small and fast: at most 150 production lines per change, a fast Tier 1 (AGENTS.md:2, AGENTS.md:5, CONTRIBUTING.md:10).
11. Finish the slices of the plan and its open questions; today the status is pre-release, nothing published (docs/spec.md:210-237, docs/decisions/0001-vbm-forecast.md:8-10, README.md:5).

## Metrics
All values were measured on 2026-11-19 in a jail without network, so `mise` could not fetch the pinned toolchain; the commands were run with the same Lean 4.35.0 already on `PATH` (`lake`, `lean`), and the gate as `scripts/tier1.sh` without the `mise exec --` prefix. Run each command from the repository root; in a checkout with network, prefix `lake`/gate commands with `mise exec --` as in `.land/land.conf`. Run `lake build VbmForecast VbmForecastProofs LandLedger` once before the `land-lean` and `lake env` commands.

| metric | direction (higher or lower is better) | goal it serves | how to measure (the exact command, from the repository root) | now (value and date) | floor (= now) | target (blank: the owner sets it) |
|---|---|---|---|---|---|---|
| `proof-ledger-claims-proved` (count) | higher | spec.md:166, spec.md:227 | `.land/tool/bin/land-lean ledger \| sed -nE 's/^ledger: ([0-9]+) proved.*/\1/p'` | 25 (2026-11-19) | 25 | |
| `proof-ledger-gaps` (count of partial + open + limit claims) | lower | spec.md:166, spec.md:227 | `.land/tool/bin/land-lean ledger \| awk -F'[ ,]+' '{print $4+$6+$8}'` | 0 (2026-11-19) | 0 | |
| `proof-ledger-proved-share-hundredths-of-percent` | higher | spec.md:166 | `.land/tool/bin/land-lean ledger \| awk -F'[ ,]+' '{print int(10000*$2/$11)}'` | 10000 (2026-11-19) | 10000 | |
| `spec-properties-unledgered` (properties 1-17 with no `pN-` claim) | lower | spec.md:227 | `for n in $(seq 1 17); do grep -qE "^[^p]*p$n-" docs/proof-ledger.md \|\| echo $n; done \| wc -l` | 0 (2026-11-19) | 0 | |
| `ledger-baseline-lag-claims` (proved now minus the ratchet floor) | lower | README.md:8, spec.md:227 | `.land/tool/bin/land-lean ledger \| sed -nE 's/^ledger: ([0-9]+) proved.*/\1/p' \| awk -v b=$(sed -nE 's/^proved ([0-9]+)/\1/p' scripts/ledger-baseline.txt) '{print $1-b}'` | 24 (2026-11-19) | 24 | |
| `axiom-offending-constants` (count) | lower | AGENTS.md:24, spec.md:188 | `.land/tool/bin/land-lean axiom \| sed -nE 's/.*checked, ([0-9]+) offending.*/\1/p'` | 0 (2026-11-19) | 0 | |
| `forbidden-construct-hits` (count) | lower | AGENTS.md:24 | `grep -rnwE 'sorry\|admit\|axiom\|unsafe\|implemented_by\|csimp' VbmForecast VbmForecastProofs vectors VbmForecast.lean VbmForecastProofs.lean \| grep -vc tier1-allow` | 0 (2026-11-19) | 0 | |
| `core-import-violations` (imports in VbmForecast other than itself) | lower | AGENTS.md:33, spec.md:8 | `grep -rhE '^[[:space:]]*(import\|prelude)\b' VbmForecast VbmForecast.lean \| grep -vcE '^import VbmForecast(\.[A-Za-z0-9_]+)*[[:space:]]*$'` | 0 (2026-11-19) | 0 | |
| `core-float-or-io-uses` (count) | lower | spec.md:8, AGENTS.md:18 | `grep -rnwE 'Float\|IO\|BaseIO\|EIO' VbmForecast VbmForecast.lean \| wc -l` | 0 (2026-11-19) | 0 | |
| `build-warnings` (count) | lower | AGENTS.md:24 and the zero-warning gate, CONTRIBUTING.md:7 | `for f in $(find VbmForecast VbmForecastProofs vectors -name '*.lean') VbmForecast.lean VbmForecastProofs.lean; do lake env lean -DautoImplicit=false $f; done 2>&1 \| grep -c 'warning:'` | 0 (2026-11-19) | 0 | |
| `vectors-run` (count of known-answer cases that ran) | higher | spec.md:190, spec.md:224 | `scripts/test_vectors.sh \| sed -nE 's/^ran: vectors: ([0-9]+) cases.*/\1/p'` | 22 (2026-11-19) | 22 | |
| `spec-vectors-uncovered` (V ids of spec section 10 absent from vectors/Vectors.lean) | lower | spec.md:190 | `for i in $(grep -oE '^\| V[0-9]+' docs/spec.md \| tr -d '\| '); do grep -qw "$i" vectors/Vectors.lean \|\| echo $i; done \| wc -l` | 0 (2026-11-19) | 0 | |
| `trust-ledger-gaps` (required items with no written contract or no test) | lower | trust-ledger.md:5, spec.md:188 | `.land/tool/bin/land-lean trust \| sed -nE 's/.*covered; ([0-9]+) with no.*/\1/p'` | 2 (2026-11-19) | 2 | |
| `public-lint-violations` (count of findings) | lower | AGENTS.md:28 | `scripts/lint-public 2>&1 \| grep -c '[^[:space:]]'` | 0 (2026-11-19) | 0 | |
| `spec-open-questions` (count) | lower | spec.md:3, spec.md:231 | `awk '/^## Open questions/{f=1;next} f&&/^[0-9]+\. /{n++} END{print n+0}' docs/spec.md` | 7 (2026-11-19) | 7 | |
| `spec-slices-unlanded` (slices of spec.md with no landed commit) | lower | spec.md:210-229, 0001-vbm-forecast.md:8-10 | `echo $(( $(grep -cE '^- \*\*S[0-9]+\.' docs/spec.md) - $(git log --format=%s \| grep -oE 'slice: S[0-9]+' \| sort -u \| wc -l) ))` | 1 (2026-11-19) | 1 | |
| `verified-core-lines` (lines under VbmForecast/) | lower | CONTRIBUTING.md:10, spec.md:8 | `cat VbmForecast/*.lean \| wc -l` | 631 (2026-11-19) | 631 | |
| `version-tags-missing` (1 if no tag v$(cat VERSION) exists) | lower | README.md:5 | `git tag -l "v$(cat VERSION)" \| grep -c . \| awk '{print 1-$1}'` | 1 (2026-11-19) | 1 | |
| `tier1-seconds` (wall time of the whole gate) | lower | AGENTS.md:5, CONTRIBUTING.md:7 | `s=$(date +%s); scripts/tier1.sh >/dev/null 2>&1; echo $(( $(date +%s) - s ))` | 169 (2026-11-19) | 169 | |

Notes on units: every value is a count, except `proof-ledger-proved-share-hundredths-of-percent` (hundredths of a percent, 10000 = 100.00%) and `tier1-seconds` (seconds). The floor only moves toward better; when a value improves, the floor is set to the new value in the same change. `ledger-baseline-lag-claims` is the distance between the ledger (25 proved) and the ratchet file `scripts/ledger-baseline.txt` (1 proved), which the owner records; the floor for it is the value above until the owner moves the ratchet.

## Health today
- Nothing regressed: every gate metric (ledger gaps, axiom-offending constants, forbidden constructs, import violations, float/IO uses, warnings, public-lint violations, uncovered vectors) is 0, and the whole of Tier 1 passed on 2026-11-19 in 169 seconds.
- Goal 3 is met in the ledger: 25 of 25 claims proved and every property 1 to 17 has a claim. The ratchet is lagging: `scripts/ledger-baseline.txt` still says 1 proved, so a regression from 25 down to 2 would pass the gate (`ledger-baseline-lag-claims` = 24).
- Goal 8 is the weakest on the table: `trust-ledger-gaps` = 2 (both entries have "no written contract or no test", by their own admission, trust-ledger.md T1 and T2).
- Goal 11 is the furthest from where the repository points: `spec-slices-unlanded` = 1 (S8, the generator adapter, waits on a vendored generator) and `spec-open-questions` = 7, among them the proposed values of the named limits including `minEvents`.
- Release state: `version-tags-missing` = 1: `VERSION` is 0.1.0 and a release commit exists, but no tag; the README says pre-release and nothing is published.
- Unmeasured: none of the listed metrics. Not measured because the repository gives no goal for it: runtime speed of the library, and the share of the 17 properties that are STATED rather than proved (the ledger has no `limit` or `open` claim today).
- Size is not a goal with a direction in the repository; `verified-core-lines` is recorded so growth is visible (631 lines of code against the 150-line per-change limit).

## What a steward would do first
1. Move the ratchet: have the owner record the baseline from the ledger (25 proved), which takes `ledger-baseline-lag-claims` from 24 to 0 and makes `proof-ledger-claims-proved` a floor that cannot silently fall.
2. Close the trust-ledger gaps by giving T1 and T2 a written contract and a test that can fail, which moves `trust-ledger-gaps` from 2 toward 0, or have the owner decide that accepting them is the end state and say so in the target.
3. Answer the open questions of the specification (limit defaults, `minEvents`, `badLimit`), then land S8 once a generator is pinned, which moves `spec-open-questions` from 7 and `spec-slices-unlanded` from 1 toward 0.

## Questions for the owner
- Targets: the target column is blank for every metric. Which are hard targets (for example 0 for every gate metric) and which only a floor?
- Is `tier1-seconds` a goal at all? The repository says Tier 1 should be "fast and best-effort" (AGENTS.md:5) but names no number; what budget?
- Is a smaller `verified-core-lines` better, or should it only be bounded per change? The repository states only the 150-line limit per change.
- Should a release tag (`v0.1.0`) be cut now, or is the library to stay unpublished until S8 and the open questions are settled? (`version-tags-missing`)
- `docs/spec.md` (section 7) proposes `minEvents` = 30 and the other limits "for the owner to confirm": what are they? A metric for the share of verdicts refused, or for the power of the verdict, needs your goal for what "enough evidence" means; the repository states none.
- Which STATED-only claims (log-score propriety, spec.md:96) are wanted as proved in the ledger? The ledger carries none today, so the gap is invisible to the table.
- Should the squared calibration error (spec.md:117, open question 4) become a goal?
