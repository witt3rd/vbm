# vbm-memory

**Verified agent memory.** The theory of what an agent's memory may and may not do, written once in Lean 4 and machine-checked: scopes (a class, a domain, an identity), verbatim append-only notes, recall that returns only what was retained, in the scopes asked for, and cites its sources, and supersession without deletion.

> **Status: pre-release.** The first slice only. Nothing is published to a package registry.

## What it is, and what it is not

A specification, its proofs, a reference model (a small in-memory implementation) and conformance vectors: language-neutral scenarios with their expected results, which any implementation runs in its own tests. It is not a retrieval engine: how relevant a note is, how hits are ranked and how many are shown belong to the implementation. What an implementation may return is the specification's.

## Build and test

Prerequisites: `git`, [mise](https://mise.jdx.dev). `mise exec -- scripts/tier1.sh` is the gate (Lean 4.35.0, pinned in `mise.toml`).

## How it is built

Agents write it under mechanical gates instead of line-by-line review, to the [VBM standard](https://github.com/witt3rd/vbm). It lands directly on `main` with `.land/land-direct`, a pinned copy of [vbm-land](https://github.com/witt3rd/vbm-land).

## License

Apache-2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
