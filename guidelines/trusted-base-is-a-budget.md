# The trusted base is a budget, not a label

Every executable definition is exactly one of two things:
- **Specified**: a definition with its theorems, or mechanically derived from one. The proofs are the guarantee.
- **Boundary**: it performs I/O or calls code you do not control, and nothing else. It is small, named, has a written contract, and a conformance suite that can fail.

There is no third class. Keep a single trust ledger naming everything you do not control (native substrate, libraries, language runtime, compiler, operating system), each with an owner and a plan: verify it, replace it, sandbox it, or accept it with a stated reason.
Count the base, never guess it: the specified share of executed code, the boundary size, the number of ledger entries. Report them on every change.
