import VbmDecisionProofs.Core
import VbmDecisionProofs.Prob
import VbmDecisionProofs.Refusal
import VbmDecisionProofs.Limits
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
  O "prob-range" (.proved [``VbmDecision.ofDecimal_range, ``VbmDecision.ofDecimal_negative, ``VbmDecision.ofDecimal_outOfRange]),
  O "refusal-codes-complete" (.proved [``VbmDecision.refusalCode_all_complete, ``VbmDecision.refusalCode_all_nodup, ``VbmDecision.refusalCode_count, ``VbmDecision.refusal_ext_code, ``VbmDecision.scaleRefusal_toCode_injective]),
  O "named-limits-values" (.proved [``VbmDecision.limits_values, ``VbmDecision.maxSample_quadratic]),
  O "named-limits-consistent" (.proved [``VbmDecision.sumEpsilon_le, ``VbmDecision.sumEpsilon_lt_scale, ``VbmDecision.calibration_limits_consistent, ``VbmDecision.structural_limits_roomy])
]
