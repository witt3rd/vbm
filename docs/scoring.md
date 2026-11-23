# Library Scoring (`scripts/score` and `lib/<name>/score`)

Status: normative definition (Part 2 of 3: source, proof, and trust metrics).

Every family library under `lib/<name>/` computes its own advisory `[scores]` and `[scores.provenance]` block for `lib/<name>/card.toml` (`docs/hub-cards.md`, section 1.3). Scores are **advisory only** and never gate a landing or release. Until a library exposes `lib/<name>/score`, its card carries no `[scores]` section and the library is **unscored**.

This document defines every common core metric in `docs/hub-cards.md` section 1.3, its exact source in a library tree, how it is measured, and what is not yet honestly measurable in the shared script.

---

## 1. Common Core Metrics

| Metric | Type | Source in `lib/<name>/` | Measurement | Status (Part 2) |
|---|---|---|---|---|
| `spec_lines` | int >= 0 | Pure specification `.lean` files (e.g. `spec/**/*.lean` when present; otherwise `0` unless separated from `code_lines`) | Newline count (`b"\n"`) of tracked regular files | Implemented |
| `code_lines` | int >= 0 | Executable/compiled `.lean` library modules (root `<Lib>.lean`, `<Lib>/**/*.lean`, `<Lib>Simd`, `<Lib>Wire`, `<Lib>Tool`, excluding `*Proofs*`, `vectors/`, `tests/`, `scripts/`, `bench/`, `docs/`, `lakefile.lean`) | Newline count (`b"\n"`) of tracked regular files | Implemented |
| `proof_lines` | int >= 0 | Machine-checked proof `.lean` files (`*Proofs.lean`, `*Proofs/**/*.lean`) | Newline count (`b"\n"`) of tracked regular files | Implemented |
| `trusted_native_lines` | int >= 0 | Trusted native boundary files (`abi/*.c`, `runtime/**/*.c`, `native/*.c`, `include/*.h`, `scripts/rt/runtime/**/*.c`, or `[trust] c_files` in `scorecard.toml` when present) | Newline count (`b"\n"`) of tracked regular files (matches `scorecard/scorecard` `verified.trusted_c_lines`) | Implemented |
| `generated_share_pct` | float (0.0..100.0) | `scripts/ClosureGate.lean` | Executed spec expression nodes / total executed expression nodes * 100 (omitted when no closure gate or unbuilt) | Implemented (when measurable) |
| `proved_claims` | int >= 0 | Typed obligation ledger (`LAND_LEAN_LEDGER_MODULE` via `land-lean ledger --no-write`) | Count of claims with status `proved` (omitted when no ledger module or unbuilt) | Implemented (when measurable) |
| `total_claims` | int >= 0 | Typed obligation ledger (`LAND_LEAN_LEDGER_MODULE` via `land-lean ledger --no-write`) | Total claims in the obligation ledger (omitted when no ledger module or unbuilt) | Implemented (when measurable) |
| `unproved_escapes` | int >= 0 | Lexer/AST-level Lean token scan (skipping comments, strings, char literals, guillemets) and typed `land-lean axiom` audit | Maximum of token hits (`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `csimp`) and non-standard axiom offenders | Implemented |
| `trust_ledger_entries` | int >= 0 | `docs/trust-ledger.md` (or `[trust] ledger` in `scorecard.toml`) via `.land/tool/lean/trust_ledger.py` `parse()` | Count of parsed `### T<N>. ...` entries (omitted when no trust ledger file exists) | Implemented (when measurable) |

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

## 3. When Metrics Are Omitted (Never Invented)

Per `docs/hub-cards.md` section 1.3 ("unscored is a state, not a number"), `scripts/score` omits a metric rather than inventing `0` or `0.0` when its source does not exist or cannot be evaluated:

1. **`generated_share_pct`:** Measured by running `lake env lean --run scripts/ClosureGate.lean` when `scripts/ClosureGate.lean` exists and prints `specified share <P>%`. Pure-Lean libraries without a closure gate (or unbuilt trees) omit `generated_share_pct`.
2. **`proved_claims` and `total_claims`:** Measured from the typed `List Obligation` evaluation of `LAND_LEAN_LEDGER_MODULE` via `land-lean ledger --no-write` (never by regex-matching `docs/proof-ledger.md`). Libraries without `LAND_LEAN_LEDGER_MODULE` in `.land/lean.conf` (such as `vbm-context`, `vbm-journal`, `vbm-memory`, `vbm-rt`, `vbm-simd`) or unbuilt trees omit both fields.
3. **`trust_ledger_entries`:** Measured by `.land/tool/lean/trust_ledger.py` `parse()` over `docs/trust-ledger.md` (or `[trust] ledger` in `scorecard.toml`). Libraries without a trust ledger file (such as `vbm-rt`) omit `trust_ledger_entries`.

Because `docs/hub-cards.md` section 2.2 rule 6 forbids committing an incomplete `[scores]` block into `card.toml`, `scripts/score` in Part 2 prints the measured `[scores]` fields and `[scores.provenance]` to stdout and does **not** implement `--write` onto `lib/*/card.toml` (Part 3).

---

## 4. Command Interface (`scripts/score`)

```text
scripts/score <lib-dir>
```

- Reads `<lib-dir>` (a library directory such as `lib/vbm-json`).
- Prints deterministic TOML containing `[scores]` (all measurable core metrics) and `[scores.provenance]` (`commit`, `tool_version`) to stdout.
- Exits `0` on success, `2` on invalid input (missing directory, unsafe path).
