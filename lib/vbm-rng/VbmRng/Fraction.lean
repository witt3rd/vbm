import VbmRng.Stream
import VbmRng.Refusal
/-! # Uniform dyadic fractions (S6)

`uniformFraction k st` is the exact dyadic rational `num / 2^k`: the top `k` bits of the next word of the stream, for `1 ≤ k ≤ 64`. It consumes exactly one word and needs no rejection: every numerator in `[0, 2^k)` has exactly `2^(64-k)` preimages among the `2^64` words. Any other `k` is the typed refusal `fractionBitsOutOfRange`. The properties F1-F4 are proved in `VbmRngProofs/Fraction.lean`. -/
namespace VbmRng

/-- A uniform dyadic fraction `num / 2^k` from the top `k` bits of one word, or a typed refusal. -/
def uniformFraction (k : Nat) (st : Stream) : DrawWith Stream Fraction :=
  if k = 0 ∨ 64 < k then .error .fractionBitsOutOfRange
  else .ok ({ num := (st.next.1 >>> (64 - k).toUInt64).toNat, bits := k }, st.next.2)

end VbmRng
