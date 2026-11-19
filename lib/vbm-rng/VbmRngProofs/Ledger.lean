import VbmRngProofs.Core
import VbmRngProofs.Refusal
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and checked by `land-lean ledger` (`.land/tool/docs/lean-gates.md`): a claim is `proved` only by naming theorems
(double-backtick names are checked at elaboration), or it is a `limit` no machine decides. -/
open Land.Ledger

def ledger : List Obligation := [
  O "the-library-has-a-name" (.proved [``VbmRng.libraryName_nonempty]),
  O "the-refusals-are-distinct" (.proved [``VbmRng.refusal_pairwise_distinct, ``VbmRng.refusal_ne_ok])
]
