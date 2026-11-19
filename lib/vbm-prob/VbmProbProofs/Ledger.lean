import VbmProbProofs.Core
import VbmProbProofs.Refusal
import VbmProbProofs.Limits
import VbmProbProofs.Prob
import VbmProbProofs.Prob.Bayes
import VbmProbProofs.Scaled
import VbmProbProofs.Apportion
import VbmProbProofs.Dist
import VbmProbProofs.Dist.Canon
import VbmProbProofs.Dist.Query
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and checked by `land-lean ledger` (`.land/tool/docs/lean-gates.md`): a claim is `proved` only by naming theorems
(double-backtick names are checked at elaboration), or it is a `limit` no machine decides. -/
open Land.Ledger

def ledger : List Obligation := [
  O "the-library-has-a-name" (.proved [``VbmProb.libraryName_nonempty]),
  O "refusal-carries-its-evidence" (.proved [``VbmProb.Refusal.tooManyAtoms_inj, ``VbmProb.Refusal.eq_iff_decide]),
  O "limits-default-values" (.proved [``VbmProb.Limits.default_values]),
  O "bit-length-exact" (.proved [``VbmProb.bitLength_zero, ``VbmProb.bitLength_of_ne_zero, ``VbmProb.bitLength_eq_zero_iff,
    ``VbmProb.lt_two_pow_bitLength, ``VbmProb.two_pow_bitLength_pred_le, ``VbmProb.bitLength_mono]),
  O "rat-bits-positive" (.proved [``VbmProb.Rat.bits_pos, ``VbmProb.Rat.bits_ofInt]),
  O "key-order-laws" (.proved [``VbmProb.Key.le_iff, ``VbmProb.Key.le_refl, ``VbmProb.Key.le_trans, ``VbmProb.Key.le_total,
    ``VbmProb.Key.le_antisymm, ``VbmProb.Key.lt_asymm]),
  O "PR1-prob-make" (.proved [``VbmProb.Prob.make_ok_iff, ``VbmProb.Prob.make_val, ``VbmProb.Prob.make_belowZero, ``VbmProb.Prob.make_aboveOne]),
  O "PR2-prob-ofFrac" (.proved [``VbmProb.Prob.ofFrac_denominatorZero_iff, ``VbmProb.Prob.ofFrac_eq_make]),
  O "PR3-prob-complement" (.proved [``VbmProb.Prob.complement_val, ``VbmProb.Prob.complement_complement, ``VbmProb.Prob.complement_zero,
    ``VbmProb.Prob.val_add_complement]),
  O "PR4-prob-mul" (.proved [``VbmProb.Prob.mul_val, ``VbmProb.Prob.mul_comm, ``VbmProb.Prob.mul_assoc, ``VbmProb.Prob.one_mul,
    ``VbmProb.Prob.mul_one, ``VbmProb.Prob.zero_mul, ``VbmProb.Prob.mul_zero, ``VbmProb.Prob.mul_le_left, ``VbmProb.Prob.mul_le_right]),
  O "PR5-prob-add" (.proved [``VbmProb.Prob.add_ok_iff, ``VbmProb.Prob.add_val, ``VbmProb.Prob.add_refuses, ``VbmProb.Prob.add_comm,
    ``VbmProb.Prob.add_complement]),
  O "PR10-prob-order" (.proved [``VbmProb.Prob.le_refl, ``VbmProb.Prob.le_trans, ``VbmProb.Prob.le_antisymm, ``VbmProb.Prob.le_total]),
  O "PR6-prob-bayes" (.proved [``VbmProb.Prob.evidence_val, ``VbmProb.Prob.bayes_ok_iff, ``VbmProb.Prob.bayes_zeroEvidence,
    ``VbmProb.Prob.bayes_val, ``VbmProb.Prob.bayes_mul_evidence, ``VbmProb.Prob.bayes_val_expanded]),
  O "PR7-prob-bayes-boundaries" (.proved [``VbmProb.Prob.bayes_prior_zero, ``VbmProb.Prob.bayes_prior_one,
    ``VbmProb.Prob.bayes_like_eq, ``VbmProb.Prob.bayes_likeNot_zero]),
  O "PR8-prob-conditional" (.proved [``VbmProb.Prob.conditional_ok_iff, ``VbmProb.Prob.conditional_mul,
    ``VbmProb.Prob.conditional_zeroMarginal, ``VbmProb.Prob.conditional_jointExceedsMarginal]),
  O "PR9-prob-bayes-is-conditional" (.proved [``VbmProb.Prob.bayes_eq_conditional,
    ``VbmProb.Prob.conditional_evidence_ne_jointExceeds, ``VbmProb.Prob.bayes_conditional_zero]),
  O "prob-ext" (.proved [``VbmProb.Prob.ext]),
  O "FX1-scale-make" (.proved [``VbmProb.Scale.make_zero, ``VbmProb.Scale.make_tooLarge, ``VbmProb.Scale.make_ok,
    ``VbmProb.Scale.make_n]),
  O "FX2-toScaled-range" (.proved [``VbmProb.toScaled_le, ``VbmProb.toScaled_zero, ``VbmProb.toScaled_one]),
  O "FX3-toScaled-error-bound" (.proved [``VbmProb.toScaled_bounds, ``VbmProb.toScaled_error]),
  O "FX4-toScaled-monotone" (.proved [``VbmProb.div_round_mono, ``VbmProb.toScaled_mono]),
  O "FX5-ofScaled" (.proved [``VbmProb.ofScaled_ok_iff, ``VbmProb.ofScaled_val, ``VbmProb.ofScaled_above]),
  O "FX6-toScaled-ofScaled" (.proved [``VbmProb.num_mul_scale, ``VbmProb.toScaled_ofScaled]),
  O "FX7-ofScaledInt" (.proved [``VbmProb.ofScaledInt_neg, ``VbmProb.ofScaledInt_above, ``VbmProb.ofScaledInt_in_range,
    ``VbmProb.ofScaledInt_natCast]),
  O "FX8-apportion-sum" (.proved [``VbmProb.apportion_sum, ``VbmProb.Apportion.units_sum, ``VbmProb.Apportion.units_length,
    ``VbmProb.Apportion.chosen_length, ``VbmProb.Apportion.sum_floor_rem]),
  O "FX9-apportion-within-one" (.proved [``VbmProb.apportion_within_one, ``VbmProb.apportion_zero_weight,
    ``VbmProb.Apportion.chosen_rem_pos]),
  O "FX10-apportion-refusal" (.proved [``VbmProb.apportion_refuses_iff, ``VbmProb.apportion_ok_of_pos]),
  O "FX11-apportion-ties" (.proved [``VbmProb.apportion_tie]),
  O "FX12-apportion-idempotent" (.proved [``VbmProb.apportion_idem]),
  O "DS4-canon" (.proved [``VbmProb.canon_keys_increasing, ``VbmProb.canon_weightSum, ``VbmProb.canon_weightAt,
    ``VbmProb.canon_idem]),
  O "DS1-dist-make" (.proved [``VbmProb.Dist.make_atoms, ``VbmProb.Dist.make_tooManyAtoms, ``VbmProb.Dist.make_numberTooLarge,
    ``VbmProb.Dist.make_emptyDist, ``VbmProb.Dist.make_keysNotIncreasing, ``VbmProb.Dist.make_zeroAtom,
    ``VbmProb.Dist.make_atomSumNotOne, ``VbmProb.Dist.make_ok_iff]),
  O "DS2-dist-ext" (.proved [``VbmProb.Dist.ext, ``VbmProb.Dist.ext_iff, ``VbmProb.Dist.make_unique]),
  O "DS3-point-atoms" (.proved [``VbmProb.Dist.point_atoms, ``VbmProb.Dist.point_support, ``VbmProb.Dist.point_size,
    ``VbmProb.Dist.size_pos, ``VbmProb.Dist.make_point]),
  O "DS3-point-mean-cdf" (.proved [``VbmProb.Dist.mean_point, ``VbmProb.Dist.point_cdf_ge, ``VbmProb.Dist.point_cdf_lt]),
  O "DS6-mass" (.proved [``VbmProb.Dist.mass_true, ``VbmProb.Dist.mass_false, ``VbmProb.Dist.mass_or_val, ``VbmProb.Dist.mass_or,
    ``VbmProb.Dist.mass_not, ``VbmProb.Dist.mass_mono, ``VbmProb.Dist.mass_congr]),
  O "DS7-cdf" (.proved [``VbmProb.Dist.cdf_mono, ``VbmProb.Dist.cdf_below, ``VbmProb.Dist.cdf_above, ``VbmProb.Dist.cdf_right_cont]),
  O "DS10-expect" (.proved [``VbmProb.Dist.expect_add, ``VbmProb.Dist.expect_smul, ``VbmProb.Dist.expect_const,
    ``VbmProb.Dist.expect_mono, ``VbmProb.Dist.expect_point, ``VbmProb.Dist.mean_point])
]
