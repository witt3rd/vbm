import Lake
open System Lake DSL

package «vbm-memory» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The library: specification and code, one Lean core. Imports `Init` and itself only (checked by Tier 1). No dependency. -/
@[default_target]
lean_lib VbmMemory where
  globs := #[.andSubmodules `VbmMemory]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `VbmMemory` may import it). -/
lean_lib VbmMemoryProofs where
  globs := #[.andSubmodules `VbmMemoryProofs]
