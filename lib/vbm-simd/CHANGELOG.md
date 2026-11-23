# Changelog

## 0.2.0

- The library is released from the family repository (`lib/vbm-simd`), where its gate, its areas and its signed `vbm-simd/vX.Y.Z` tags now live. The specification, the shims, the models and the proofs are unchanged; the old standalone repository is archived. A dependent (`vbm-json`, `vbm-sse`) requires it by the relative path `../vbm-simd` and records its tree in its own signed tag.

## 0.1.1

- The previous release, made from the standalone repository.

## 0.1.0

- The first release: bit-vector models of vector instructions, a trusted shim per instruction set, and proved kernels.
