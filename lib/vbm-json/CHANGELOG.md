# Changelog

## 0.2.1

- A release cut after `vbm-simd` 0.2.0, so that the tree this tag records for its dependency is a RELEASED `vbm-simd` (0.2.0 recorded the unreleased tree it was built against, which a consumer cannot pin together with the library). No change to the code.

## 0.2.0

- **`LeanJson.Compat`: a drop-in, Init-only replacement for the slice of the toolchain's `Lean.Json` that products use** (slices a to d3). The same names (`Json`, `JsonNumber`, `ToJson`, `FromJson`, `mkObj`, the accessors, `compress`, `pretty`, `parse`), no import beyond `Init`, so that a program which opens `LeanJson.Compat` in place of `Lean` no longer links the toolchain's `Lean.Data.Json` (which pulls about 66 MB of the toolchain's static library into an executable). Objects keep their keys sorted and unique by construction (proved); printing is byte-equal to the toolchain's on a corpus of more than 500 values, checked at build time; parsing makes the same accept and refuse decisions with the same values. Not provided: the `deriving ToJson, FromJson` handlers (they need the elaborator).
- The library's gates are the landing tool's Lean gates: the axiom audit, the trust ledger, the replay of every proof by Lean's own checker, and the obligation ledger.
- The library lives in the family repository (`lib/vbm-json`) and depends on `../vbm-simd`; releases are tagged `vbm-json/vX.Y.Z`.

## 0.1.0

- The first release: an RFC 8259 JSON parser whose correctness is a machine-checked theorem, written once in Lean 4 and compiled to freestanding C and WebAssembly, with generated bindings (pre-release status).
