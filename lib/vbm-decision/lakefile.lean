import Lake
open System Lake DSL

package «vbm-decision» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The library: specification and code, one Lean core. Imports `Init` and itself only (checked by Tier 1). No dependency. -/
@[default_target]
lean_lib VbmDecision where
  globs := #[.andSubmodules `VbmDecision]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `VbmDecision` may import it). -/
lean_lib VbmDecisionProofs where
  globs := #[.andSubmodules `VbmDecisionProofs]

/-- The landing tool's Lean modules (the obligation-ledger vocabulary and the reach walk, `land-lean ledger`), a small package it ships; required, never declared here, so a repository that vendors this library and requires it too shares one copy. -/
require «land-ledger» from ".land/tool/lean"
