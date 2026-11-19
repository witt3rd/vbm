/-! # Refusals, draws and fractions (S3)

Every way a primitive refuses is a `Refusal` value inside an `Except`, never a default and never a panic. `DrawWith σ α` is a value and the advanced state, or a refusal; the spec's `Draw α` is `DrawWith Stream α` and is stated beside `Stream` (the stream slice), because `Stream` is not defined at this slice. `Fraction` is the exact dyadic rational `num / 2^bits`. -/
namespace VbmRng

/-- Every way a primitive refuses. -/
inductive Refusal where
  /-- `uniformBelow` with `n = 0`. -/
  | boundZero
  /-- `uniformBelow` with `n > 2^64` (also a Bernoulli denominator above `2^64`). -/
  | boundTooLarge
  /-- `uniformFraction` with `k = 0` or `k > 64`. -/
  | fractionBitsOutOfRange
  /-- Bernoulli with `den = 0`. -/
  | probabilityDenominatorZero
  /-- Bernoulli with `num < 0` or `num > den`. -/
  | probabilityOutOfRange
  /-- The rejection loop used all its fuel. -/
  | fuelExhausted
  deriving DecidableEq, Repr

/-- A value and the advanced state `σ`, or a refusal. `Draw α` of the spec is `DrawWith Stream α`. -/
abbrev DrawWith (σ : Type) (α : Type) : Type := Except Refusal (α × σ)

/-- The exact dyadic rational `num / 2^bits`. -/
structure Fraction where
  /-- The numerator. -/
  num : Nat
  /-- The number of fractional bits. -/
  bits : Nat
  deriving DecidableEq, Repr

end VbmRng
