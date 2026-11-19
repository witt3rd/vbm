import VbmRngProofs.Core
import VbmRngProofs.Refusal
import VbmRngProofs.Mix
import VbmRngProofs.Stream
import VbmRngProofs.Split
import VbmRngProofs.Below
import LandLedger
/-! # The obligation ledger

Every claim the library makes, keyed by a slug and checked by `land-lean ledger` (`.land/tool/docs/lean-gates.md`): a claim is `proved` only by naming theorems
(double-backtick names are checked at elaboration), or it is a `limit` no machine decides. -/
open Land.Ledger

def ledger : List Obligation := [
  O "the-library-has-a-name" (.proved [``VbmRng.libraryName_nonempty]),
  O "the-refusals-are-distinct" (.proved [``VbmRng.refusal_pairwise_distinct, ``VbmRng.refusal_ne_ok]),
  O "m1-xor-shift-is-invertible" (.proved [``VbmRng.invXorShift_xorshift, ``VbmRng.xorshift_invXorShift]),
  O "m2-mix-is-a-bijection-with-its-inverse" (.proved [``VbmRng.unmix_mix, ``VbmRng.mix_unmix]),
  O "m3-mix-is-injective" (.proved [``VbmRng.mix_injective]),
  O "m4-multiplication-by-an-odd-constant-is-a-bijection" (.proved [``VbmRng.mul_gamma_injective, ``VbmRng.gamma_gammaInv]),
  O "t1-determinism" (.proved [``VbmRng.Stream.ofSeed_inj, ``VbmRng.Stream.at_det, ``VbmRng.Stream.next_det, ``VbmRng.Stream.advance_det]),
  O "t2-no-repeats-the-full-range" (.proved [``VbmRng.Stream.at_injective, ``VbmRng.Stream.at_ne, ``VbmRng.Stream.at_surjective]),
  O "t3-skip-ahead-agrees-with-stepping" (.proved [``VbmRng.Stream.at_add]),
  O "t4-next-is-at-and-advance" (.proved [``VbmRng.Stream.next_fst, ``VbmRng.Stream.next_snd, ``VbmRng.Stream.advance_advance]),
  O "t5-seeds-give-distinct-streams" (.proved [``VbmRng.Stream.ofSeed_key_injective]),
  O "p1-distinct-children" (.proved [``VbmRng.childKey_injective, ``VbmRng.childKey_ne, ``VbmRng.Stream.split_key_ne]),
  O "p2-split-is-a-function-of-the-parents-key-and-the-index" (.proved [``VbmRng.Stream.split_key_eq, ``VbmRng.Stream.split_key]),
  O "p3-children-start-at-zero" (.proved [``VbmRng.Stream.split_pos]),
  O "u1-the-result-is-in-range" (.proved [``VbmRng.uniformBelowWith_lt, ``VbmRng.uniformBelow_lt]),
  O "u2-exactness" (.proved [``VbmRng.uniformBelow_exact, ``VbmRng.count_range_ge, ``VbmRng.count_blocks]),
  O "u3-the-specification-matches-the-counting" (.proved [``VbmRng.uniformBelowWith_ok_iff, ``VbmRng.uniformBelowWith_error_iff, ``VbmRng.drawGo_ok, ``VbmRng.drawGo_error]),
  O "u4-accepted-fraction" (.proved [``VbmRng.accepted_gt_half]),
  O "u5-the-fuel-is-enough-when-the-threshold-is-small" (.proved [``VbmRng.uniformBelowWith_ne_fuelExhausted]),
  O "u6-refusals" (.proved [``VbmRng.uniformBelowWith_boundZero, ``VbmRng.uniformBelowWith_boundTooLarge, ``VbmRng.uniformBelowWith_zero_fuel]),
  O "u7-determinism-and-advance" (.proved [``VbmRng.uniformBelowWith_det, ``VbmRng.uniformBelowWith_advance]),
  O "q1-independence-of-split-children-and-mixed-outputs" (.limit "trusted, not proved: docs/trust-ledger.md Q1; only the distinctness of keys (P1) is proved"),
  O "q2-stream-overlap-bound" (.limit "trusted, not proved: docs/trust-ledger.md Q2; users keep m^2 L far below 2^64"),
  O "q3-expectation-and-tail-of-rejection" (.limit "trusted, not proved: docs/trust-ledger.md Q3; a consequence of Q1, only the accepted fraction above one half (U4) is proved")
]
