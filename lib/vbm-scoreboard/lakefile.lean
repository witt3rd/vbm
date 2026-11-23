import Lake
open System Lake DSL

package «vbm-scoreboard» where
  leanOptions := #[⟨`warningAsError, true⟩, ⟨`autoImplicit, false⟩]

/-- The library: specification and code, one Lean core. Imports `Init` and itself only (checked by Tier 1). No dependency. -/
@[default_target]
lean_lib VbmScoreboard where
  globs := #[.andSubmodules `VbmScoreboard]

/-- The wire formats (the provider protocol, the baseline and the history files): a sibling library that MAY import `Lean`, is linked, and imports the core. Imports `Lean`, `VbmScoreboard` and itself only (checked by Tier 1). -/
lean_lib VbmScoreboardWire where
  globs := #[.andSubmodules `VbmScoreboardWire]

/-- The proofs: may import `Std` and `Lean`; NEVER linked (nothing in `VbmScoreboard` may import it). -/
lean_lib VbmScoreboardProofs where
  globs := #[.andSubmodules `VbmScoreboardProofs]

/-- The landing tool's Lean modules (the obligation-ledger vocabulary and the reach walk, `land-lean ledger`), a small package it ships; required, never declared here, so a repository that vendors this library and requires it too shares one copy. -/
require «land-ledger» from ".land/tool/lean"

/-- The command-line tool `vbm-scoreboard` (slice S3): the boundary over the core and the wire formats. It reads files and the output of a provider command, calls the specified functions, prints their typed results and sets the exit code; it decides nothing. -/
lean_lib VbmScoreboardTool where
  globs := #[.andSubmodules `VbmScoreboardTool]

@[default_target]
lean_exe «vbm-scoreboard» where
  root := `VbmScoreboardTool.Main
