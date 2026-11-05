---
name: write-a-binding
description: >-
  Generate a language binding (Python, Rust, TypeScript, C#) for a VBM library from its ABI description (vbm-abi). Use when a library needs a new language binding.
---

# Write a binding

A binding is generated, never hand-written: the ABI is described once in Lean (`abi/*.lean`) and generators emit the C header and each binding. Until a shared `vbm-abi` exists, each library carries its own generator; follow the exemplar `vbm-json` (`abi/`, `include/`).

## Steps
1. Make sure the ABI description covers the entry points: caller-owned buffers, a "needed size" return, typed results, no allocator across the boundary; a layout theorem fixes the result record.
2. Add a generator target for the language that reads the ABI description and emits the binding source. Commit the generator, not hand edits of its output.
3. Regenerate: run the repo's generate command and check that a second run gives identical bytes.
4. Run the generated test vectors (from the reference implementation) through the binding unchanged. No hand-written cases.
5. Add the binding to the trust ledger (`docs/trust-ledger.md`) as a `### T<n>` entry: unproved, owner, plan.
6. Add the language to `targets` in the registry entry when the card is rerun.

## Verify
Vectors pass in the new language; regenerating gives no diff; the ledger lists the binding.

## Do not
- Edit generated files by hand or add libc to the freestanding path.
- Test the binding with cases of your own.
