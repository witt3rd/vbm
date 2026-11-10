# 0001: vbm-memory, verified agent memory

## 1. What and why
An agent's memory is where what it learned outlives its process. The behaviour an agent relies on (a retained note is never lost, a recall returns only what was retained and cites it, writers need no merge) should be stated once and checked, not re-argued by every implementation. This library specifies that as data and total functions, with proofs.

## 2. Design choices
- **A port, not an engine.** The specification says what an implementation may return; how it finds and ranks is the implementation's (a boundary never decides). Any compliant implementation, a search service over a database or a file, satisfies the same laws.
- **Scopes.** A class, a domain and an identity; an agent is attached to some of them, reads from and writes to those.
- **Append-only, verbatim.** A retained note is kept whole; a later note may cite it, correct it or supersede it, never delete it. Concurrent writers need no merge.
- **Reconciliation is derived.** A consolidated note cites the notes it is drawn from, and a recall's current view is a function of the notes.
- **Conformance vectors.** The specification generates language-neutral scenarios with expected results; an implementation runs them in its own suite.
- **Scope.** Pure data and total functions over `Init`. No model call, no network, no storage.

## 3. Slices
M1 the scope and note types, the bank, and monotone append-only retain. M2 the recall contract (every hit cites a retained note, only from the attached scopes). M3 supersession and consolidation. M4 the reference model and the vectors.

## 4. Ran-evidence (the gate rule)
A check that never ran must not pass. Every test script prints `ran: NAME: N cases` (N > 0).
