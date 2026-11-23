---
name: new-vbm-library
description: >-
  Add a new verified-bare-metal library to the family: a directory lib/<name>/ of THIS repository (never a new repository): spec first, Lean skeleton, the library's own gate, its own areas, its card. Use when starting a library or turning an idea into one.
---

# New VBM library (a directory of the family repository)

A library is a pure Lean specification (types, grammar as a relation, reference implementation, fast implementation, theorems), compiled to C and WebAssembly, with a small boundary that only moves bytes. Read `guidelines/library-design.md` first (a cohesive family of FEW libraries: scope, tiers, a named second consumer) and check `lib/` for something you would only duplicate. **The family has one repository, so a library is a directory `lib/<name>/` here, with a signed per-library tag `<name>/vX.Y.Z`. Do not create a repository.** (Migrating an existing repository is a different job: `docs/migrating-a-library.md`.)

## Steps
1. Work in a worktree (`scripts/wt switch -c agent/<task>`), never in the primary clone. Pick `<name>`: `vbm-<word>`, `[a-z0-9][a-z0-9_-]*`, unique, never `registry`, `docs`, `tooling`, `inert` or `hub`.
2. `lib/<name>/` is SELF-CONTAINED: its own `lean-toolchain`, `lakefile.lean`, `lake-manifest.json` and `mise.toml` live inside it, so the directory alone, exported, builds. A family dependency is required ONLY by the relative path `require «vbm-dep» from "../vbm-dep"` and named, one per line, in `lib/<name>/deps` (the file exists even when empty).
3. Write `lib/<name>/docs/spec.md` BEFORE any Lean: the inputs, outputs, every named limit, every typed refusal, one sentence per property to prove. Bytes in, bytes out; time and randomness are inputs; no allocator across the ABI.
4. Lean skeleton: `<Name>.lean` (spec + code) and a separate `<Name>Proofs.lean` (theorems). The obligation ledger is a Lean `Ledger` module checked by `land-lean ledger` (it generates `docs/proof-ledger.md`); the trust ledger is `docs/trust-ledger.md` (every boundary and tool, a plan from the closed set, a test path).
5. The library's own gate, `lib/<name>/scripts/tier1.sh`: COPY one from a migrated library of the same shape (`lib/vbm-prob/scripts/tier1.sh`) and keep its conventions: it runs with the LIBRARY directory as its working directory; the lander is two levels up, so tools are `../../.land/tool/bin/...`; the Lean gates take the library as their root (`LAND_LEAN_ROOT="$PWD" ../../.land/tool/bin/land-lean axiom|trust|recheck|ledger`, configured by the library's own `lib/<name>/.land/lean.conf`); `run-tests-parallel` works from the git root, so pass it ABSOLUTE test paths. If the library needs the lander's Lean package: `require «land-ledger» from "../../.land/tool/lean"`. Do NOT copy a lander, a lint, a secret-gate configuration, CI or hook files: the family repository has each once, and `scripts/repo-gates.sh` (the pinned lander, no build outside the guard, public-readiness, no secret in the history or the tree) is the first step of EVERY area.
6. Declare the library: `lib/<name>/areas.json` (`{"version":1,"areas":[{"name":"<name>","paths":["*"],"steps":[{"run":"mise exec -- scripts/tier1.sh"}]}]}`; a large library may declare several areas named `<name>:<part>`, with paths relative to the library; an area with no `uses` owns its dependency closure), `VERSION` (`0.1.0`), `CHANGELOG.md`, `README.md`, `LICENSE` (Apache-2.0), `NOTICE` (`Copyright <year> the vbm-<name> authors.`), and `card.toml` (`docs/hub-cards.md`: name, scope, kind, status, license, consumers; NO `[scores]` section until the library has a score command: unscored is a state, never invented numbers).
7. Derive the areas file: `scripts/hub-areas --write` (never hand-edit `.land/areas.json`; `scripts/hub-areas --check` is a Tier 1 test). Check it: `.land/tool/bin/land-areas validate`, no unmapped path, and a change inside `lib/<name>/` selects ONLY your area.
8. Public text: the family is public, so a library's text names no product, person or machine, and writes no home-directory path with a tilde (use `$HOME`; `scripts/lint-public` refuses it).
9. Land: commit with the project identity (`witt3rd@witt3rd.com`, author AND committer: the lander refuses any other) and a `Task-ID:` trailer, and land with `.land/land-direct`. **Adding a library changes `.land/areas.json`, which is gate-defining: that landing runs EVERY library's suite and needs the owner's word (`Protected:` trailer).** It is long (about three minutes per library); batch new libraries into one landing. Every later change inside the library runs only its own area.
10. Release, on the host that holds the release key: set `VERSION`, land it, then `land-release --area <name> --push` (the tag is `<name>/vX.Y.Z`; it requires every area of the library and every area that uses it to pass; the candidate branch is `rc/<name>/vX.Y.Z` and is deleted after the tag). The first release is `v0.1.0`.
11. A library that others vendor is pinned by them with `land-pin vendor <name> https://github.com/witt3rd/vbm <name>/vX.Y.Z --path lib/<name>`.

## Verify
- `cd lib/<name> && mise exec -- scripts/tier1.sh` prints `tier1: ok` and the gates' counts.
- From the repository root: `scripts/tier1.sh` and `scripts/repo-gates.sh` pass, and `scripts/hub-areas --check` is clean.

## Do not
- Create a repository, vendor the lander, add a ruleset, or copy CI: the family repository has them.
- Write Lean before the spec, or tests by hand (vectors come from the reference).
- Add an axiom, `sorry`, `unsafe` or an `implemented_by` to make something pass; put it in the trust ledger or leave the claim `open`.
- Let the boundary make decisions.
- Make a mass number (specified share, unverified mass, closure counts) fail a landing: mass numbers are advisory, reported and never gated.
