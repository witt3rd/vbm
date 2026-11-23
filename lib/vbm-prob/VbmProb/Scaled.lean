import VbmProb.Prob
import VbmProb.Limits
/-! # Fixed point: scales, and probabilities as whole numbers of units

A `Scale` is a positive number of units in a whole. `toScaled` rounds a probability to the nearest unit (ties up) in integers only; `ofScaled` is exact (`docs/spec.md`, "Fixed point"). -/
namespace VbmProb

/-- A fixed-point scale: the number of units in a whole, never 0. -/
structure Scale where
  /-- The number of units in a whole. -/
  n : Nat
  /-- The scale is positive. -/
  pos : 0 < n

namespace Scale

/-- A scale from a number, refused when it is 0 or above the limit. -/
def make (n : Nat) (lim : Limits) : Except Refusal Scale :=
  if h : n = 0 then .error .zeroScale
  else if n > lim.maxScale then .error (.scaleTooLarge n lim.maxScale)
  else .ok ⟨n, Nat.pos_of_ne_zero h⟩

/-- One million units: parts per million. -/
def million : Scale := ⟨1000000, by decide⟩

/-- The scale as a rational is not 0. -/
theorem natCast_ne_zero (sc : Scale) : (sc.n : Rat) ≠ 0 :=
  fun h => Nat.ne_of_gt sc.pos (Rat.natCast_eq_zero_iff.mp h)

end Scale

/-- The nearest whole number of units, ties up: `(2·num·n + den) / (2·den)` in integers. -/
def toScaled (sc : Scale) (p : Prob) : Nat :=
  (2 * p.val.num.toNat * sc.n + p.val.den) / (2 * p.val.den)

/-- `k` units as a probability, exactly `k / n`, or the refusal when `k` is above the scale. -/
def ofScaled (sc : Scale) (k : Nat) : Except Refusal Prob :=
  if h : k ≤ sc.n then
    .ok ⟨(k : Rat) / (sc.n : Rat), Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr sc.pos))),
      Rat.le_of_mul_le_mul_right (c := (sc.n : Rat))
        (by rw [Rat.div_mul_cancel sc.natCast_ne_zero, Rat.one_mul]; exact Rat.natCast_le_natCast.mpr h)
        (Rat.natCast_pos.mpr sc.pos)⟩
  else .error (.scaledAboveScale k sc.n)

/-- A wire integer as a probability: below 0 and above the scale are refused, carrying `k / n`. -/
def ofScaledInt (sc : Scale) (k : Int) : Except Refusal Prob :=
  if k < 0 then .error (.belowZero ((k : Rat) / (sc.n : Rat)))
  else if (sc.n : Int) < k then .error (.aboveOne ((k : Rat) / (sc.n : Rat)))
  else ofScaled sc k.toNat

end VbmProb
