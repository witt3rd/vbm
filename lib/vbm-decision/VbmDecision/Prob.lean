/-! # Probabilities as whole millionths, and exact decimals (S1a)

`Prob` is a natural number of millionths in `[0, scale]`; `Decimal` is an exact signed decimal. `Decimal.toScaled` and `Prob.ofDecimal` convert exactly or refuse: never rounded, never truncated. Pure data and total functions over `Init`. -/
namespace VbmDecision

/-- One, in millionths. -/
def scale : Nat := 1000000

/-- A probability: `val / scale`. A value has one representation, so equality of `Prob` is equality of probabilities. -/
structure Prob where
  val : Nat
  le : val ≤ scale
  deriving DecidableEq, Repr

/-- An exact decimal: `± mantissa × 10^exp`. -/
structure Decimal where
  neg : Bool
  mantissa : Nat
  exp : Int
  deriving DecidableEq, Repr

/-- The numeric refusals of a decimal-to-probability conversion (the numbers group of the spec's refusal codes). -/
inductive ScaleRefusal where
  | negative | tooPrecise | outOfRange | exponentTooLarge
  deriving DecidableEq, Repr

namespace Decimal

/-- The largest exponent magnitude read, so that `10^exp` is never computed for a hostile exponent. -/
def maxExponent : Nat := 1000

/-- The numerator of the value as a fraction: `± mantissa × 10^exp` when `exp ≥ 0`, else `± mantissa`. -/
def numer (d : Decimal) : Int :=
  (if d.neg then -1 else 1) * ((d.mantissa : Int) * 10 ^ d.exp.toNat)

/-- The denominator of the value as a fraction: `10^(-exp)` when `exp < 0`, else `1`. -/
def denom (d : Decimal) : Nat := 10 ^ (-d.exp).toNat

/-- The value times `scale`, exactly, or a refusal. A signed zero is zero. -/
def toScaled (d : Decimal) : Except ScaleRefusal Nat :=
  if d.mantissa = 0 then .ok 0
  else if d.neg then .error .negative
  else if maxExponent < d.exp.natAbs then .error .exponentTooLarge
  else if 0 ≤ d.exp + 6 then .ok (d.mantissa * 10 ^ (d.exp + 6).toNat)
  else if d.mantissa % 10 ^ (-(d.exp + 6)).toNat = 0 then .ok (d.mantissa / 10 ^ (-(d.exp + 6)).toNat)
  else .error .tooPrecise

end Decimal

namespace Prob

/-- Strip up to `f` trailing decimal zeros of a nonzero `m`, counting them in `k`. -/
def stripZeros : Nat → Nat → Nat → Nat × Nat
  | 0, m, k => (m, k)
  | f + 1, m, k => if m ≠ 0 ∧ m % 10 = 0 then stripZeros f (m / 10) (k + 1) else (m, k)

/-- The value as an exact decimal over millionths: trailing zeros of `val` move into the exponent; zero is `{false, 0, 0}`. -/
def toDecimal (p : Prob) : Decimal :=
  if p.val = 0 then ⟨false, 0, 0⟩
  else ⟨false, (stripZeros 6 p.val 0).1, ((stripZeros 6 p.val 0).2 : Int) - 6⟩

/-- A decimal as a probability: exactly a whole number of millionths, then in range, or a refusal. -/
def ofDecimal (d : Decimal) : Except ScaleRefusal Prob :=
  match d.toScaled with
  | .error e => .error e
  | .ok v => if h : v ≤ scale then .ok ⟨v, h⟩ else .error .outOfRange

/-- The error per printed entry, in millionths (four decimals, truncated). -/
def entryError : Nat := 100

/-- The tolerance of a sum of `n` entries. -/
def sumEpsilon (n : Nat) : Nat := entryError * n

end Prob

/-- The sum rule: `n` probabilities sum to one within `sumEpsilon n`. -/
def SumOk (n : Nat) (ps : List Prob) : Prop :=
  (ps.map Prob.val).sum + Prob.sumEpsilon n ≥ scale ∧ (ps.map Prob.val).sum ≤ scale + Prob.sumEpsilon n

instance (n : Nat) (ps : List Prob) : Decidable (SumOk n ps) := by unfold SumOk; infer_instance

end VbmDecision
