# The trust ledger

What vbm-rng relies on without proof: the facilities outside this repository that every proof and every run assumes. vbm-rng is pure Lean (specifications, proofs, a reference model): it has no C, no foreign function and no vendored dependency, so nothing in its own tree is trusted code; its trusted base is the toolchain that checks and compiles it and the tools its scripts run.

Entry format: **What** it is; **Enters** where it enters; **Assumes** what we assume of it (the contract); **Test** the test that can fail; **Owner**; **Plan** (verify, replace, sandbox or accept, with a reason); **Covers** the keys it accounts for. `land-lean trust` derives what must be covered from the tree and `.land/lean.conf`, so a trusted thing cannot be left out unseen (vbm-land `docs/lean-gates.md`, guideline `mark-what-is-trusted.md` of the hub).

### T1. The Lean toolchain and the build pins
- **What:** the Lean compiler and kernel, the runtime (`lean.h`, `libleanrt`) and the bundled clang and ld.lld, pinned by `lean-toolchain` and `mise.toml`; `lakefile.lean` drives the build.
- **Enters:** `lean-toolchain`, `mise.toml`, `lakefile.lean`; the kernel checks every proof and the compiler produces every artifact built from this library.
- **Assumes:** the kernel is sound and the compiler is faithful (a miscompile would void what the proofs say about the compiled code): no written contract beyond the Lean project's own documentation.
- **Test:** the axiom gate (`.land/tool/bin/land-lean axiom`, configured by `.land/lean.conf`) fails when any constant depends on an axiom beyond the three standard ones; `lake build` re-checks every proof.
- **Owner:** the owner
- **Plan:** accept because the kernel and the compiler are outside this repository and every claim in it assumes them.
- **Covers:** `file:lean-toolchain` `file:mise.toml` `file:lakefile.lean` `lean-compiler` `lean-runtime` `clang-lld`

### T2. The tools the scripts run
- **What:** `lake` builds the library and its proofs; `mise` provides the pinned toolchain; `git` lists the files the checks read; `python3` runs the trust-ledger checker of the landing tool.
- **Enters:** `scripts/tier1.sh`, `lakefile.lean`.
- **Assumes:** each behaves as documented (a wrong build would be caught by the proofs, a wrong checker by its own negative self-tests): no written contract.
- **Test:** none beyond the tools' own; a wrong build fails the proofs.
- **Owner:** the owner
- **Plan:** accept because they are the host's own tools and nothing from them executes in an artifact.
- **Covers:** `tool:git` `tool:lake` `tool:mise` `tool:python3`

## Quality assumptions (trusted, not proved)

These are claims about behaviour, not files or tools, so the checker above derives no key for them; they are listed here, and in `VbmRngProofs/Ledger.lean` as `limit`, so that no statement leans on them unseen. Both are stated in `docs/spec.md`, part P.

**Q1 (independence and uniformity of mixed outputs and of split children).** The streams of distinct children, and the outputs of different streams, behave as statistically independent, uniform sources. Every counter-based generator assumes this of its mixer; it is not provable in general. Enters at `VbmRng/Split.lean` (`childKey`, `Stream.split`) and `VbmRng/Mix.lean` (`mix`); every statement about the statistics of a draw depends on it. What IS proved is only the distinctness of keys (P1) and of outputs within one stream (T2). No statistical test battery is run or claimed. Test: none, no test in the gate can decide a statistical assumption. Owner: the owner. Plan: accept, because independence of a fixed mixer's outputs cannot be proved and the library claims distinctness only.

**Q2 (the stream-overlap bound).** Two streams with different keys `k`, `k'` are windows on the same cycle of 2^64 values, shifted by `(k' - k) * gammaInv` positions, and share outputs exactly when their windows overlap. With keys spread uniformly (Q1) the chance that two streams of length `L` overlap is about `2 L / 2^64` per pair, and for `m` streams of length `L` about `m^2 L / 2^64`. Users keep `m^2 L` far below 2^64; the library does not enforce it. Enters wherever several streams are used (`VbmRng/Split.lean`, `VbmRng/Stream.lean`). Test: none. Owner: the owner. Plan: accept, because the bound rests on Q1 and the library states it rather than enforcing it.
