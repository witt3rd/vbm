# 0001: vbm-scoreboard, a project's scorecard

Status: accepted (2026-11-18).

## Why
Every project of the family measures how it is doing against its own goals, and the measure that decides whether a change may land (a floor that only moves toward better) was written as shell in the first project that needed it. A shared, proved core lets every project keep its own scorecard in one schema, lets its caretakers read health and progress the same way everywhere, and keeps the ratchet's rules (a check fails closed on an unmeasured metric, banking never records a worse number, a floor is loosened only by a reasoned reset) out of every project's glue.

## What
Metrics (a name and an integer; the unit is the provider's, in the name), a direction, floors, readings, a check that gives one verdict per floor, banking, resets with a recorded reason and author, an append-only history, and progress toward a target. The wire formats (the provider protocol and the baseline and history files) are `VbmScoreboardWire`; a command-line tool is a separate slice.

## Slices
- S0 (this commit): the skeleton and the direction order (`better`), each theorem with a non-vacuity witness.
- S1 (landed): the core (`check`, `bank`, `reset`, `history`, `progress`), extracted from the first consumer's specification; definitions in `VbmScoreboard/Core.lean`, theorems and witnesses in `VbmScoreboardProofs/Core.lean`.
- S2 (landed): `VbmScoreboardWire`, extracted from the first consumer's format specification; definitions in `VbmScoreboardWire/Format.lean` (it imports `Lean` and the core, and is linked), theorems and witnesses in `VbmScoreboardProofs/Wire.lean`. The text round trips are proved of any parser and renderer faithful on the lines the encoder writes; that `Lean.Json.parse` reads back `Lean.Json.compress` is the one trusted fact, checked by `#guard` on concrete values.
- S3 (landed): the command-line tool `vbm-scoreboard` (`VbmScoreboardTool/`, a `lean_exe`), which replaces the first consumer's shell script. It is a boundary: the decisions it needs were added to the libraries first, with proofs (`VbmScoreboard/Journal.lean`: banking refused unless every floor held, one history line per moved floor, adding a metric, where a floor started; `VbmScoreboardWire/Provider.lean`: what a provider's exit and output mean). Its process-boundary test is `scripts/test_tool.sh`.

## Rules
Pure data and total functions over `Init`. The words of the wire formats are kept exactly once released; a change to one needs the consumers' word.
