import VbmScoreboardProofs.Direction
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and checked by `land-lean ledger` (`.land/tool/docs/lean-gates.md`): a claim is `proved` only by naming theorems
(double-backtick names are checked at elaboration, so a renamed or deleted theorem breaks this file), or it is a `limit` no machine decides. -/
open Land.Ledger

def ledger : List Obligation := [
  O "a-value-is-at-least-as-good-as-itself" (.proved [``VbmScoreboard.Direction.better_refl]),
  O "any-two-values-are-comparable" (.proved [``VbmScoreboard.Direction.better_total, ``VbmScoreboard.Direction.better_trans]),
  O "the-two-directions-are-opposite" (.proved [``VbmScoreboard.Direction.better_opposite])
]
