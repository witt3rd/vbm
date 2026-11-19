import VbmRngProofs.Core
import VbmRngProofs.Refusal
import VbmRngProofs.Mix
import VbmRngProofs.Stream
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
  O "t5-seeds-give-distinct-streams" (.proved [``VbmRng.Stream.ofSeed_key_injective])
]
