import VbmForecastProofs.Core
import VbmForecastProofs.Rep
import VbmForecastProofs.Brier
import VbmForecastProofs.Ordered
import VbmForecastProofs.LogScore
import VbmForecastProofs.Calibration
import VbmForecastProofs.Compare
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
    ``VbmForecast.checkAligned_ok, ``VbmForecast.checkAligned_refuses]),
  O "p1-brier-bounded-and-zero-exactly-for-perfect" (.proved [``VbmForecast.brierBinary_nonneg, ``VbmForecast.brierBinary_le,
    ``VbmForecast.brierBinary_eq_zero_iff, ``VbmForecast.brierCategorical_nonneg, ``VbmForecast.brierCategorical_le,
    ``VbmForecast.brierCategorical_eq_zero_iff]),
  O "p2-brier-binary-strictly-proper" (.proved [``VbmForecast.expBrierBinary_diff, ``VbmForecast.expBrierBinary_ge,
    ``VbmForecast.expBrierBinary_eq_iff]),
  O "p3-brier-categorical-strictly-proper" (.proved [``VbmForecast.expBrierCat_diff, ``VbmForecast.expBrierCat_ge,
    ``VbmForecast.expBrierCat_eq_iff]),
  O "p4-brier-additive-over-events" (.proved [``VbmForecast.brierTotal_append, ``VbmForecast.brierCatTotal_append,
    ``VbmForecast.brierTotal_cons, ``VbmForecast.brierMean_ok, ``VbmForecast.brierMean_badScale, ``VbmForecast.brierMean_empty]),
  O "p5-brier-permutation-invariant" (.proved [``VbmForecast.brierTotal_perm, ``VbmForecast.brierCatTotal_perm]),
  O "brier-validated-entry-points" (.proved [``VbmForecast.brierBinaryV_ok, ``VbmForecast.brierCategoricalV_ok]),
  O "p4-ordered-totals-additive-over-events" (.proved [``VbmForecast.rpsTotal_append, ``VbmForecast.pinballTotal_append,
    ``VbmForecast.intervalTotal_append, ``VbmForecast.rpsTotal_cons, ``VbmForecast.pinballTotal_cons, ``VbmForecast.intervalTotal_cons]),
  O "p5-ordered-totals-permutation-invariant" (.proved [``VbmForecast.rpsTotal_perm, ``VbmForecast.pinballTotal_perm,
    ``VbmForecast.intervalTotal_perm]),
  O "p8-rps-is-brier-thresholds-interval-is-two-pinballs" (.proved [``VbmForecast.rps_eq_sum_brier, ``VbmForecast.rpsTotal_eq_sum_brier,
    ``VbmForecast.rpsEvents_hit, ``VbmForecast.intervalScore_eq_pinball]),
  O "p9-pinball-quantile-minimises-expected-score" (.proved [``VbmForecast.pinball_support, ``VbmForecast.expPinball_support,
    ``VbmForecast.expPinball_quantile_le]),
  O "ordered-validated-entry-points" (.proved [``VbmForecast.rpsV_ok, ``VbmForecast.pinballV_ok, ``VbmForecast.intervalScoreV_ok]),
  O "p10-log-comparison-is-exact-and-consistent" (.proved [``VbmForecast.logCompare_antisymm, ``VbmForecast.logCompare_trans,
    ``VbmForecast.logCompare_gt_iff, ``VbmForecast.logCompare_gt_swap, ``VbmForecast.logCompare_perm, ``VbmForecast.logCompare_append,
    ``VbmForecast.natProd_append, ``VbmForecast.natProd_perm, ``VbmForecast.logCompare_enclosure, ``VbmForecast.separated_lt,
    ``VbmForecast.logCompare_of_separated, ``VbmForecast.logCompareV_ok, ``VbmForecast.logCompareV_lengthMismatch,
    ``VbmForecast.logCompareV_empty, ``VbmForecast.logVerdict_refused, ``VbmForecast.logVerdict_decided]),
  O "p11-log-enclosure-is-sound-and-has-width-at-most-2" (.proved [``VbmForecast.log2Enclosure_sound, ``VbmForecast.log2Enclosure_total,
    ``VbmForecast.log2Enclosure_badScale, ``VbmForecast.log2Enclosure_zero, ``VbmForecast.log2Enclosure_over,
    ``VbmForecast.log2EnclosureV_sound, ``VbmForecast.log2EnclosureV_limit, ``VbmForecast.log2Enclosure_half,
    ``VbmForecast.log2Enclosure_one, ``VbmForecast.logRun_inv]),
  O "p5-reliability-table-permutation-invariant" (.proved [``VbmForecast.table_perm, ``VbmForecast.reliability_perm]),
  O "p6-reliability-counts-and-every-probability-in-one-bin" (.proved [``VbmForecast.bin_unique, ``VbmForecast.binOf_iff,
    ``VbmForecast.reliability_n_sum, ``VbmForecast.reliability_hits_sum, ``VbmForecast.reliability_sumP_sum,
    ``VbmForecast.reliability_length, ``VbmForecast.reliability_ok]),
  O "p7-calibration-error-zero-iff-perfectly-calibrated" (.proved [``VbmForecast.calibrationError_ok,
    ``VbmForecast.calibrationError_zero_iff, ``VbmForecast.calibNum_zero_iff]),
  O "calibration-in-the-large" (.proved [``VbmForecast.citl_ok, ``VbmForecast.citl_gap_zero_iff]),
  O "p12-bootstrap-is-a-function-of-data-and-draws" (.proved [``VbmForecast.bootstrapSums_deterministic,
    ``VbmForecast.bootstrapSums_congr, ``VbmForecast.bootstrapSums_of_seed, ``VbmForecast.bootstrapSums_ok,
    ``VbmForecast.bootstrapSums_length, ``VbmForecast.bootstrapSums_empty, ``VbmForecast.bootstrapSums_tooManyEvents,
    ``VbmForecast.bootstrapSums_tooManyResamples, ``VbmForecast.bootstrapSums_mismatch, ``VbmForecast.bootstrapSums_badDraws,
    ``VbmForecast.pairedDiffs_ok, ``VbmForecast.pairedDiffs_mismatch, ``VbmForecast.pairedDiffs_neg, ``VbmForecast.diffMean_ok]),
  O "p13-identical-resamples-give-the-point-interval" (.proved [``VbmForecast.ci_const, ``VbmForecast.bootstrapSums_const,
    ``VbmForecast.bootstrap_const_contains]),
  O "p14-ci-is-well-formed" (.proved [``VbmForecast.ci_wellFormed, ``VbmForecast.ci_ok, ``VbmForecast.ci_badLevel,
    ``VbmForecast.ci_empty, ``VbmForecast.ciK_lt, ``VbmForecast.ciK_le, ``VbmForecast.sortInts_perm, ``VbmForecast.sortInts_sorted]),
  O "p15-verdict-refused-below-the-minimum-sample" (.proved [``VbmForecast.verdict_refused, ``VbmForecast.compare_refused]),
  O "p16-verdict-is-monotone-in-the-evidence" (.proved [``VbmForecast.verdict_nested, ``VbmForecast.verdict_minEvents,
    ``VbmForecast.verdict_minEvents_sign, ``VbmForecast.verdict_better_iff, ``VbmForecast.verdict_worse_iff,
    ``VbmForecast.not_better_and_worse_evidence])
]
