import VbmProbProofs.Core
import VbmProbProofs.Refusal
import VbmProbProofs.Limits
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
    ``VbmProb.Key.le_antisymm, ``VbmProb.Key.lt_asymm])
]
