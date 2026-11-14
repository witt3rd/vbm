# 0001: The dispatcher as two machines over a specified pool

Status: decided. A host's work dispatcher is a pure specification, written once and proved, with conformance vectors for any interpreter.

## The pool

`VbmDispatcher.Pool` is the specification of a leased work queue and of a host's choice from it: the guard (`ready`: the off switch, draining, CPU pressure under a ceiling, memory under a ceiling, a disk and a memory floor), the chooser (`choose`: aging, dependencies, serialisation keys, class gates, deferral to hosts better placed, determinism), and the store's laws as a port (send, claim, renew, finish; one winner; fencing by the delivery number; finish idempotent on retry; exhaustion derived). Its change classes are the vocabulary of `vbm-work`.

## Two machines

The **tick** (one per period) reads the host, and if it has headroom reads the queue, chooses, claims exactly that item and ends `started`, or ends `skipped` (no headroom: nothing written), `idle`, or `storeUnreachable` (fail-stop). A claim lost to another host reads the queue again and chooses again from a fresh snapshot, with no cap.

The **run** (one per claimed item) renews the lease at every beat while the worker runs, finishes the item once with the worker's own typed report, and cleans up exactly once. A refused renewal and the run's deadline stop the worker and report nothing; a worker that exits with no report finishes nothing and the lease lapses.

Both are sans I/O: events in, actions out, no clock, no text. Every number (the beat period, the lease length, the ceilings and the floors) is the host's data, never a default in the machine.

## What is proved and what is not

The claims are in `docs/proof-ledger.md`. That the ports meet their laws is the application's conformance suite (a limit in the ledger), as for the orchestrator. The vectors are the interpreter's checklist.
