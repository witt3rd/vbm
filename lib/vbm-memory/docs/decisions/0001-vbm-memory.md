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
M1 the scope and note types, the bank, and monotone append-only retain. **Landed:** a scope is one of three kinds (a class, a domain, an identity) and the kinds stay distinct under one name (`VbmMemory/Scope.lean`, `VbmMemoryProofs/Note.lean`); a note is its identifier, its scope, where it came from and the identifiers of the notes it derives from, empty for an experience note (`VbmMemory/Note.lean`); a bank is the notes retained so far, retaining appends so the notes held before are a prefix of the notes held after (nothing rewritten, reordered or dropped) and each retain adds exactly one note, two writers retaining at once leave the same notes in either order (the two results are permutations of each other, not equal lists), a recall considers exactly the retained notes whose scope was asked for and nothing else, a derived note is accepted only when it derives from a note the bank already holds, and in a bank whose notes have distinct identifiers (`Bank.IdsUnique`, which retaining a fresh identifier keeps) a citation names exactly one held note, where otherwise an identifier two notes share makes it ambiguous (`VbmMemory/Bank.lean`, `VbmMemoryProofs/Bank.lean`); an instance is attached to a class, some domains and an identity if it bears one, it has no identity scope and cannot write one when it bears none, and it writes only into the scopes it is attached to (`VbmMemory/Attach.lean`, `VbmMemoryProofs/Attach.lean`). Every theorem carries a witness beside it that its hypothesis can hold.

M2 the recall contract (every hit cites a retained note, only from the attached scopes). M3 supersession and consolidation. M4 the reference model and the vectors.

## 4. Ran-evidence (the gate rule)
A check that never ran must not pass. Every test script prints `ran: NAME: N cases` (N > 0).
