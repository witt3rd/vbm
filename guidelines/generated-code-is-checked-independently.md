# Generated code is checked independently

Trust the generator as little as possible.
- **Reproducible**: build twice from clean, hash every artifact; the hashes are identical.
- **Lineage**: every artifact carries stamps naming the specification commit, the generator commit and the toolchain pin.
- **A second compiler**: if one compiler built it, a different one builds it again and runs the same vectors.
- **Independent proof checkers**: re-check the proofs with a checker that does not share the main kernel's code.
- Anything left on the generator path is a named, bounded entry in the trust ledger.
