# Library Scoring (`scripts/score` and `lib/<name>/score`)

Status: normative definition (Part 1 of 3: definitions and source metrics).

Every family library under `lib/<name>/` computes its own advisory `[scores]` and `[scores.provenance]` block for `lib/<name>/card.toml` (`docs/hub-cards.md`, section 1.3). Scores are **advisory only** and never gate a landing or release. Until a library exposes `lib/<name>/score`, its card carries no `[scores]` section and the library is **unscored**.

This document defines every common core metric in `docs/hub-cards.md` section 1.3, its exact source in a library tree, how it is measured, and what is not yet honestly measurable in the shared script.

---

## 1. Common Core Metrics

| Metric | Type | Source in `lib/<name>/` | Measurement | Status (Part 1) |
|---|---|---|---|---|
| `spec_lines` | int >= 0 | Pure specification `.lean` files (e.g. `spec/**/*.lean` when present; otherwise `0` unless separated from `code_lines`) | Newline count (`b"\n"`) of tracked regular files | Implemented |
| `code_lines` | int >= 0 | Executable/compiled `.lean` library modules (root `<Lib>.lean`, `<Lib>/**/*.lean`, `<Lib>Simd`, `<Lib>Wire`, `<Lib>Tool`, excluding `*Proofs*`, `vectors/`, `tests/`, `scripts/`, `bench/`, `docs/`, `lakefile.lean`) | Newline count (`b"\n"`) of tracked regular files | Implemented |
| `proof_lines` | int >= 0 | Machine-checked proof `.lean` files (`*Proofs.lean`, `*Proofs/**/*.lean`) | Newline count (`b"\n"`) of tracked regular files | Implemented |
| `trusted_native_lines` | int >= 0 | Trusted native boundary files (`abi/*.c`, `runtime/**/*.c`, `native/*.c`, `include/*.h`, `scripts/rt/runtime/**/*.c`, or `[trust] c_files` in `scorecard.toml` when present) | Newline count (`b"\n"`) of tracked regular files (matches `scorecard/scorecard` `verified.trusted_c_lines`) | Implemented |
| `generated_share_pct` | float (0.0..100.0) | `scripts/ClosureGate.lean` (or `[proof] closure_cmd` in `scorecard.toml`) | Executed spec expression nodes / total executed expression nodes * 100 | Not measurable yet (requires Lean build/closure run; Part 2) |
| `proved_claims` | int >= 0 | `docs/proof-ledger.md` summary line (`**N proved, ... of M.**`) produced by `land-lean ledger` | Count of claims with status `proved` | Not measurable yet (Part 2) |
| `total_claims` | int >= 0 | `docs/proof-ledger.md` summary line (`**N proved, ... of M.**`) produced by `land-lean ledger` | Total claims in the obligation ledger | Not measurable yet (Part 2) |
| `unproved_escapes` | int >= 0 | Static scan of tracked `.lean` source files (matches `scorecard/scorecard` `verified.unproved_escapes`: `\b(sorry|admit|axiom|unsafe|implemented_by|csimp)\b` excluding lines with `tier1-allow`) | Count of matching lines | Not measurable yet (Part 2) |
| `trust_ledger_entries` | int >= 0 | `docs/trust-ledger.md` (`^### T[0-9]` headers, matching `scorecard/scorecard` `verified.trust_ledger_entries`) | Count of matching entry headers | Not measurable yet (Part 2) |

### Provenance (`[scores.provenance]`)

Every `[scores]` output includes `[scores.provenance]`:
- `commit`: 40-hex git commit SHA (`git rev-parse HEAD` of the enclosing repository, or `"working-tree"` if no commit exists yet).
- `tool_version`: version string read from the repository `VERSION` file.

No wall-clock timestamp is recorded. Identical tree state and `VERSION` produce byte-identical output.

---

## 2. Exact Source-Metric Definitions

All source-line metrics reuse `scorecard/scorecard`'s line-counting convention: read each tracked regular file (skipping symlinks and `..` paths) as bytes and count `b"\n"` (`data.count(b"\n")`). Only git-tracked files (`git ls-files`) are counted, falling back to non-hidden regular files when run outside a git repository (e.g., an uninitialized fixture directory).

### 2.1 `spec_lines` vs `code_lines` vs `proof_lines`

In VBM libraries, `lakefile.lean` and `.land/lean.conf` define the library's Lean targets:
1. **Proofs (`proof_lines`):** Modules whose top-level name or directory ends in `Proofs` (`*Proofs.lean`, `*Proofs/**/*.lean`). These are never linked into artifacts.
2. **Specifications (`spec_lines`):** Pure specification files kept separate from executable code (`spec/**/*.lean`, e.g. `lib/vbm-areas/spec/Compose.lean`). In most VBM libraries, the Lean specification and the executable implementation are the same `Init`-only module tree (`<Lib>.lean` and `<Lib>/**/*.lean`); in that unified model, those files are counted under `code_lines` and `spec_lines` is `0` rather than double-counting the same lines.
3. **Executable / compiled code (`code_lines`):** All tracked `.lean` files belonging to the library's compiled targets (`<Lib>.lean`, `<Lib>/**/*.lean`, including `*Simd`, `*Wire`, `*Tool` targets), excluding:
   - `lakefile.lean` (build configuration),
   - proof modules (`*Proofs.lean`, `*Proofs/**/*.lean`),
   - standalone specification files already counted in `spec_lines` (`spec/**/*.lean`),
   - non-shipped harnesses and tooling (`vectors/`, `tests/`, `scripts/`, `bench/`, `docs/`).

### 2.2 `trusted_native_lines`

Reuses `scorecard/scorecard`'s `verified.trusted_c_lines` definition:
- If `scorecard.toml` exists in the library and declares `[trust] c_files`, match those globs.
- Otherwise, match the standard trusted native boundary paths in `lib/<name>/`:
  - `abi/*.c`
  - `runtime/**/*.c`
  - `native/*.c`
  - `include/*.h`
  - `scripts/rt/runtime/**/*.c` (for runtime-only libraries such as `vbm-rt`)

Test harnesses (`tests/`), benchmarks (`bench/`), and performance prototypes (`docs/perf/`) are excluded. Generated C under `.lake/` is untracked and excluded.

---

## 3. What Is Not Honestly Measurable Yet

The following five core metrics are **not** emitted by `scripts/score` in Part 1 because they require either ledger/escape scanners or executing the Lean build/closure gate:

1. **`generated_share_pct`:** Requires running `scripts/ClosureGate.lean` (or `[proof] closure_cmd`), which needs a Lean build and only exists in libraries with C/WASM exports (`vbm-json`, `vbm-sse`). Pure-Lean libraries without a closure gate have no executed-node share defined yet.
2. **`proved_claims` and `total_claims`:** Require parsing `docs/proof-ledger.md` (and handling libraries that do not yet have a generated obligation ledger, such as `vbm-context`, `vbm-journal`, `vbm-memory`, `vbm-rt`, `vbm-simd`).
3. **`unproved_escapes`:** Requires the static escape scan across declared source globs (`scorecard/scorecard` `verified.unproved_escapes`).
4. **`trust_ledger_entries`:** Requires parsing `docs/trust-ledger.md` (and handling `vbm-rt`, which has no `docs/trust-ledger.md` yet).

Because `docs/hub-cards.md` section 2.2 rule 6 forbids committing an incomplete `[scores]` block into `card.toml`, `scripts/score` in Part 1 prints only the source metrics and `[scores.provenance]` to stdout and does **not** implement `--write` onto `lib/*/card.toml`.

---

## 4. Command Interface (`scripts/score`)

```text
scripts/score <lib-dir>
```

- Reads `<lib-dir>` (a library directory such as `lib/vbm-json`).
- Prints deterministic TOML containing `[scores]` (`spec_lines`, `code_lines`, `proof_lines`, `trusted_native_lines`) and `[scores.provenance]` (`commit`, `tool_version`) to stdout.
- Exits `0` on success, `2` on invalid input (missing directory, unsafe path).
