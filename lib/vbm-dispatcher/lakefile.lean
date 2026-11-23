import Lake
open System Lake DSL

package «vbm-dispatcher» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The vocabulary of work (the typed outcome, the review words, the task): the one dependency, vendored at a signed release. -/
require «vbm-work» from "../vbm-work"

/-- The library: specification and code, one Lean core. Imports `Init` and itself only (checked by Tier 1). No dependency. -/
@[default_target]
lean_lib VbmDispatcher where
  globs := #[.andSubmodules `VbmDispatcher]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `VbmDispatcher` may import it). -/
lean_lib VbmDispatcherProofs where
  globs := #[.andSubmodules `VbmDispatcherProofs]

/-- The landing tool's Lean modules (the obligation-ledger vocabulary and the reach walk, `land-lean ledger`), a small package it ships; required, never declared here, so a repository that vendors this library and requires it too shares one copy. -/
require «land-ledger» from "../../.land/tool/lean"

/-- The wire: JSON for the machine's data, both ways. A BINDING (it may import `Lean`; nothing in `VbmDispatcher` imports it): the vectors and an interpreter's own records use it. -/
lean_lib VbmDispatcherWire where
  globs := #[.one `VbmDispatcherWire]

/-- The vector generator (`vbm-dispatcher-vectors-1`): the scenarios and the machine's answers come from the Lean reference only; this executable only writes them. Not part of the library. -/
lean_exe «vbm-dispatcher-vectors» where
  srcDir := "vectors"
  root := `Main
