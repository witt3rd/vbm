# The conformance vectors

`vectors/vbm-dispatcher-vectors-1.jsonl`: one JSON object per line, one scenario per line, language-neutral. They are generated from the Lean reference (`VbmDispatcher.Vectors`, `Tick.step`, `Run.step`) and checked in; `scripts/test_vectors.sh` fails when the file is not what the reference gives now, so a change of a machine or a scenario is visible and a regeneration (`scripts/test_vectors.sh --write`) is a decision.

## A line

`{"name", "machine", "config" (tick only), "start", "steps", "final"}`.
- `machine` is `"tick"` or `"run"`.
- `config` (tick): `{"params": ..., "me": ...}`, the pool's parameters and who the host is.
- `start`: the actions the machine asks before any event (`readHost` for a tick, none for a run).
- `steps`: in order, `{"event": ..., "asks": [actions]}`: the event that arrives and what the machine asks in answer.
- `final`: the phase the machine ends in.

## How to use them

An interpreter conforms when, with its ports answering the events in order (an answering event when the call returns, a world event at its place), it makes exactly the calls the vector lists. The tick's events are all answers (`readings`, `queue`, `storeDown`, `claimWon`, `claimLost`); the run's world events are `beat`, `workerReported`, `workerGone` and `deadline`.

## Coverage

Tick: a won claim; skipped for no CPU headroom, a disk floor, the off switch and draining; idle for an empty queue, an unmet dependency, a held serialisation key, a label the host lacks and an item deferred to other hosts after a loss, and the end of that deferral (counted from the loss, not from the enqueue); the highest priority first; a lost race then won, then idle; the store unreachable while reading the queue, while claiming and after a lost race.
Run: the happy run; several beats; a renewal that is unreachable and then succeeds; a lost lease; the deadline; a worker that exits with no report; a worker that exits while being stopped; a finish that is refused or unreachable; a blocked report finished as it is.
