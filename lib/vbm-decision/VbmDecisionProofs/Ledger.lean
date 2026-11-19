import VbmDecisionProofs.Core
import VbmDecisionProofs.Prob
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and checked by `land-lean ledger` (`.land/tool/docs/lean-gates.md`): a claim is `proved` only by naming theorems
(double-backtick names are checked at elaboration), or it is a `limit` no machine decides. -/
open Land.Ledger

def ledger : List Obligation := [
  O "the-library-has-a-name" (.proved [``VbmDecision.libraryName_nonempty]),
  O "prob-ofdecimal-exact" (.proved [``VbmDecision.ofDecimal_exact]),
  O "prob-toscaled-refuses-imprecise" (.proved [``VbmDecision.toScaled_tooPrecise]),
  O "prob-roundtrip" (.proved [``VbmDecision.ofDecimal_toDecimal]),
  O "prob-range" (.proved [``VbmDecision.ofDecimal_range, ``VbmDecision.ofDecimal_negative, ``VbmDecision.ofDecimal_outOfRange])
]
