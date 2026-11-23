/-! # S1: representation, refusals, limits and validation

Fixed-point probabilities over a scale, unreduced exact ratios, the typed refusals, the named limits, the raw input structures and the validators (`docs/spec.md`, sections 1, 2 and 7). Every validator is total and returns `Except Refusal Unit`: a refusal is a value, never a default. -/
namespace VbmForecast

/-- The probability scale `s`; a probability is a numerator over `s`. It must be positive (`checkScale`). -/
abbrev Scale := Nat

/-- An unreduced exact ratio; order and equality are by cross-multiplication. -/
structure Ratio where
  num : Int
  den : Nat
  den_pos : 0 < den

namespace Ratio
/-- `a ≤ b` by cross-multiplication. -/
def le (a b : Ratio) : Prop := a.num * (b.den : Int) ≤ b.num * (a.den : Int)
/-- `a` and `b` denote the same value, by cross-multiplication. -/
def eqv (a b : Ratio) : Prop := a.num * (b.den : Int) = b.num * (a.den : Int)
/-- The exact sum over the product of the denominators. -/
def add (a b : Ratio) : Ratio :=
  { num := a.num * (b.den : Int) + b.num * (a.den : Int), den := a.den * b.den, den_pos := Nat.mul_pos a.den_pos b.den_pos }
instance (a b : Ratio) : Decidable (Ratio.le a b) := inferInstanceAs (Decidable (_ ≤ _))
instance (a b : Ratio) : Decidable (Ratio.eqv a b) := inferInstanceAs (Decidable (_ = _))
end Ratio

/-- A raw probability numerator over the scale; an `Int` so that "below zero" can be said and refused. -/
abbrev RawProb := Int

/-- A binary forecast `p` and whether the event happened. -/
structure BinaryEvent where
  p : RawProb
  hit : Bool

/-- A categorical forecast over `ps.length` outcomes and the realised outcome index. -/
structure CategoricalEvent where
  ps : List RawProb
  outcome : Nat

/-- A forecast over strictly increasing support values and the observed value. -/
structure OrderedEvent where
  vals : List Int
  ps : List RawProb
  obs : Int

/-- A quantile forecast at `level / s`. -/
structure QuantileEvent where
  level : Nat
  q : Int
  obs : Int

/-- A central interval forecast with tail mass `tail / s` on each side. -/
structure IntervalEvent where
  tail : Nat
  lo : Int
  hi : Int
  obs : Int

/-- Every way the library refuses; each constructor carries its evidence. -/
inductive Refusal where
  | badScale
  | probOutOfRange (i : Nat) (p : Int)
  | notNormalised (sum : Int)
  | outcomeNotInSupport (outcome k : Nat)
  | tooFewOutcomes (k : Nat)
  | empty
  | lengthMismatch (a b : Nat)
  | supportNotIncreasing
  | badLevel (level s : Nat)
  | crossedInterval (lo hi : Int)
  | badEdges
  | tooMany (what n limit : Nat)
  | badDraws (i d : Nat)
  | zeroProbability
  deriving DecidableEq, Repr

/-- The named limits; none is hidden inside a function. `tol` is in units of `1 / s`. -/
structure Limits where
  maxEvents : Nat
  maxOutcomes : Nat
  maxBins : Nat
  maxResamples : Nat
  minEvents : Nat
  logBits : Nat
  tol : Nat

/-- The `what` field of `Refusal.tooMany`: which limit was exceeded. -/
def limitEvents : Nat := 0
def limitOutcomes : Nat := 1
def limitBins : Nat := 2
def limitResamples : Nat := 3

/-- `IncFrom prev xs`: `prev < x₀ < x₁ < ...` (a strictly increasing chain). -/
def IncFrom {α : Type} [LT α] (prev : α) : List α → Prop
  | [] => True
  | x :: xs => prev < x ∧ IncFrom x xs

/-- Strictly increasing. -/
def StrictInc {α : Type} [LT α] : List α → Prop
  | [] => True
  | x :: xs => IncFrom x xs

/-- The decision procedure of `IncFrom`. -/
def incFromB {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] (prev : α) : List α → Bool
  | [] => true
  | x :: xs => decide (prev < x) && incFromB x xs

/-- The decision procedure of `StrictInc`. -/
def strictIncB {α : Type} [LT α] [DecidableRel (α := α) (· < ·)] : List α → Bool
  | [] => true
  | x :: xs => incFromB x xs

/-- The sum of a list of integers. -/
def sumInt : List Int → Int
  | [] => 0
  | x :: xs => x + sumInt xs

/-- `s = 0` is `badScale`. -/
def checkScale (s : Scale) : Except Refusal Unit :=
  if s = 0 then .error .badScale else .ok ()

/-- Each probability at position `i, i+1, ...` lies in `[0, s]`; the first that does not is refused with its position. -/
def checkProbsFrom (s : Scale) : Nat → List Int → Except Refusal Unit
  | _, [] => .ok ()
  | i, p :: ps => if p < 0 ∨ (s : Int) < p then .error (.probOutOfRange i p) else checkProbsFrom s (i + 1) ps

/-- Every probability of a forecast lies in `[0, s]`. -/
def checkProbs (s : Scale) (ps : List Int) : Except Refusal Unit := checkProbsFrom s 0 ps

/-- The probabilities sum to `s` within `tol` (units of `1 / s`); otherwise `notNormalised sum`. -/
def checkNormalised (s : Scale) (tol : Nat) (ps : List Int) : Except Refusal Unit :=
  if (sumInt ps - (s : Int)).natAbs ≤ tol then .ok () else .error (.notNormalised (sumInt ps))

/-- The outcome index is below the number of outcomes. -/
def checkOutcome (outcome k : Nat) : Except Refusal Unit :=
  if outcome < k then .ok () else .error (.outcomeNotInSupport outcome k)

/-- The number of outcomes: not zero (`empty`), at least two, within `maxOutcomes`. -/
def checkOutcomeCount (lim : Limits) (k : Nat) : Except Refusal Unit :=
  if k = 0 then .error .empty
  else if k < 2 then .error (.tooFewOutcomes k)
  else if lim.maxOutcomes < k then .error (.tooMany limitOutcomes k lim.maxOutcomes)
  else .ok ()

/-- Two lists that must be aligned have the same length. -/
def checkAligned (a b : Nat) : Except Refusal Unit :=
  if a = b then .ok () else .error (.lengthMismatch a b)

/-- The support is strictly increasing. -/
def checkIncreasing (vals : List Int) : Except Refusal Unit :=
  if strictIncB vals then .ok () else .error .supportNotIncreasing

/-- A quantile level `0 < level < s`. -/
def checkLevel (s level : Nat) : Except Refusal Unit :=
  if 0 < level ∧ level < s then .ok () else .error (.badLevel level s)

/-- An interval tail `0 < tail` and `2 * tail < s`. -/
def checkTail (s tail : Nat) : Except Refusal Unit :=
  if 0 < tail ∧ 2 * tail < s then .ok () else .error (.badLevel tail s)

/-- An interval is not crossed: `lo ≤ hi`. -/
def checkInterval (lo hi : Int) : Except Refusal Unit :=
  if hi < lo then .error (.crossedInterval lo hi) else .ok ()

/-- Reliability edges `0 = e₀ < e₁ < ... < e_B = s`, `B ≥ 1`, `B ≤ maxBins`. -/
def checkEdges (lim : Limits) (s : Scale) (edges : List Nat) : Except Refusal Unit :=
  match edges with
  | [] => .error .empty
  | e :: rest =>
    if e = 0 ∧ rest ≠ [] ∧ incFromB e rest = true ∧ (e :: rest).getLast? = some s then
      (if lim.maxBins < rest.length then .error (.tooMany limitBins rest.length lim.maxBins) else .ok ())
    else .error .badEdges

/-- A sample is not empty and has at most `maxEvents` events. -/
def checkSample (lim : Limits) (n : Nat) : Except Refusal Unit :=
  if n = 0 then .error .empty
  else if lim.maxEvents < n then .error (.tooMany limitEvents n lim.maxEvents)
  else .ok ()

/-- Bootstrap draws from position `i`: each is below `n`. -/
def checkDrawsFrom (n : Nat) : Nat → List Nat → Except Refusal Unit
  | _, [] => .ok ()
  | i, d :: ds => if d < n then checkDrawsFrom n (i + 1) ds else .error (.badDraws i d)

/-- Every bootstrap draw is below `n`. -/
def checkDraws (n : Nat) (draws : List Nat) : Except Refusal Unit := checkDrawsFrom n 0 draws

/-- The probability of a realised outcome is not zero (an infinite log loss). -/
def checkNonzero (num : Nat) : Except Refusal Unit :=
  if num = 0 then .error .zeroProbability else .ok ()

/-- Validate a binary event. -/
def validateBinary (s : Scale) (e : BinaryEvent) : Except Refusal Unit := do
  checkScale s
  checkProbs s [e.p]

/-- Validate a categorical event: scale, outcome count, range, normalisation, support. -/
def validateCategorical (s : Scale) (lim : Limits) (e : CategoricalEvent) : Except Refusal Unit := do
  checkScale s
  checkOutcomeCount lim e.ps.length
  checkProbs s e.ps
  checkNormalised s lim.tol e.ps
  checkOutcome e.outcome e.ps.length

/-- Validate an ordered event: scale, alignment, count, increasing support, range, normalisation. -/
def validateOrdered (s : Scale) (lim : Limits) (e : OrderedEvent) : Except Refusal Unit := do
  checkScale s
  checkAligned e.vals.length e.ps.length
  checkOutcomeCount lim e.vals.length
  checkIncreasing e.vals
  checkProbs s e.ps
  checkNormalised s lim.tol e.ps

/-- Validate a quantile event: scale and level. -/
def validateQuantile (s : Scale) (e : QuantileEvent) : Except Refusal Unit := do
  checkScale s
  checkLevel s e.level

/-- Validate an interval event: scale, tail, not crossed. -/
def validateInterval (s : Scale) (e : IntervalEvent) : Except Refusal Unit := do
  checkScale s
  checkTail s e.tail
  checkInterval e.lo e.hi

end VbmForecast
