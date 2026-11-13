# No decision is made from text

**A decision comes from typed data, or from a model's typed answer. Never from matching a string.** Typed data is an exit code, a record read by a typed decoder (JSON against its schema, a journal record), or a closed value a specification defines. A model's typed answer is one of a closed set of values (`progressing` or `stuck`, a finding rated `fix` or `note`), and code, in the specification, turns it into the decision with a truth table that fails closed.

This holds in every language: Lean, C, Python, shell. A regular expression, a prefix test, a substring search or a word list over text that was written for a reader (an agent's last words, a reviewer's prose, a tool's log, an error message) is a heuristic, and a heuristic guesses. It is wrong in the case nobody tried, and it fails silently.

- **A human-readable log is never parsed.** If a program needs a fact that a log carries, the producer emits it as typed data (a results file, a typed JSON answer, an exit code with a defined meaning), and the log stays for people.
- **Where text cannot be avoided, a judge model interprets it into one of the conforming types.** The decision model reads the prose (it may; that is its job) and answers with a value from a closed set; if it cannot be reached or its answer does not decode, the decision fails closed. Code never reads the prose itself.
- **Carrying text is fine; deciding on it is not.** A machine may copy a report into a record or a message for a reader. The proof that it does only that is non-interference: erase every text of an event and neither its next phase nor the kinds of its actions change (vbm-orchestrator proves it of its machine).
- **A format with a grammar is not prose.** Reading JSON with a decoder, a path against its rule, or git's own plumbing output is parsing a syntax someone defined, and is fine; matching words in a log is not. When the same fact is available typed (git's list of unmerged paths, not a search of files for conflict markers), take the typed one.

Reviewers treat a string match on text that decides something as a `fix`-level finding. This builds on `logic-lives-in-the-spec.md` and `boundary-never-decides.md`.
