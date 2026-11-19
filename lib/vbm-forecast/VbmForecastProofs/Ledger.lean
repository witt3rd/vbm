import VbmForecastProofs.Core
import VbmForecastProofs.Rep
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and checked by `land-lean ledger` (`.land/tool/docs/lean-gates.md`): a claim is `proved` only by naming theorems
(double-backtick names are checked at elaboration), or it is a `limit` no machine decides. -/
open Land.Ledger

def ledger : List Obligation := [
  O "the-library-has-a-name" (.proved [``VbmForecast.libraryName_nonempty]),
  O "ratio-order-is-a-total-preorder" (.proved [``VbmForecast.Ratio.le_refl, ``VbmForecast.Ratio.le_trans, ``VbmForecast.Ratio.le_total,
    ``VbmForecast.Ratio.eqv_refl, ``VbmForecast.Ratio.eqv_symm, ``VbmForecast.Ratio.eqv_trans, ``VbmForecast.Ratio.eqv_iff_le,
    ``VbmForecast.Ratio.add_comm_eqv]),
  O "p17-validation-is-total-and-sound" (.proved [``VbmForecast.validateBinary_ok, ``VbmForecast.validateBinary_badScale,
    ``VbmForecast.validateBinary_probOutOfRange, ``VbmForecast.validateCategorical_ok, ``VbmForecast.validateCategorical_badScale,
    ``VbmForecast.validateCategorical_tooFew, ``VbmForecast.validateCategorical_empty, ``VbmForecast.validateCategorical_tooMany,
    ``VbmForecast.validateCategorical_probOutOfRange, ``VbmForecast.validateCategorical_notNormalised,
    ``VbmForecast.validateCategorical_outcome, ``VbmForecast.validateOrdered_ok, ``VbmForecast.validateOrdered_badScale,
    ``VbmForecast.validateOrdered_lengthMismatch, ``VbmForecast.validateOrdered_notIncreasing, ``VbmForecast.validateOrdered_tooFew,
    ``VbmForecast.validateOrdered_notNormalised, ``VbmForecast.validateQuantile_ok, ``VbmForecast.validateQuantile_badScale,
    ``VbmForecast.validateQuantile_badLevel, ``VbmForecast.validateInterval_ok, ``VbmForecast.validateInterval_badScale,
    ``VbmForecast.validateInterval_badLevel, ``VbmForecast.validateInterval_crossed, ``VbmForecast.checkEdges_ok,
    ``VbmForecast.checkEdges_empty, ``VbmForecast.checkEdges_bad, ``VbmForecast.checkEdges_tooMany, ``VbmForecast.checkSample_ok,
    ``VbmForecast.checkSample_empty, ``VbmForecast.checkSample_tooMany, ``VbmForecast.checkDraws_ok,
    ``VbmForecast.checkDrawsFrom_refuses, ``VbmForecast.checkNonzero_ok, ``VbmForecast.checkNonzero_zero,
    ``VbmForecast.checkAligned_ok, ``VbmForecast.checkAligned_refuses])
]
