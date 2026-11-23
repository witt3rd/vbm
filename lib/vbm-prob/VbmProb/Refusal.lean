/-! # The typed refusal

The one inductive every fallible function of the library returns on failure: a constructor per way to refuse, never a default value (`docs/spec.md`, "Typed refusals"). Positions are 0-based indices of the FIRST offending element. -/
namespace VbmProb

/-- Why a function refused its input. Every constructor is a way to refuse; none is a default. -/
inductive Refusal where
  /-- A probability below 0. -/
  | belowZero (q : Rat)
  /-- A probability above 1. -/
  | aboveOne (q : Rat)
  /-- A fraction with denominator 0. -/
  | denominatorZero
  /-- Two disjoint probabilities whose sum exceeds 1. -/
  | sumExceedsOne (s : Rat)
  /-- Bayes' rule with evidence of probability 0. -/
  | zeroEvidence
  /-- A conditional probability on a marginal of probability 0. -/
  | zeroMarginal
  /-- A joint probability above its marginal. -/
  | jointExceedsMarginal
  /-- A scale of 0 units. -/
  | zeroScale
  /-- A scale above the limit: the scale and the limit. -/
  | scaleTooLarge (n max : Nat)
  /-- `k` units above the scale `n`. -/
  | scaledAboveScale (k n : Nat)
  /-- Weights at a scale that do not sum to the scale: the sum and the scale. -/
  | scaledSumNotScale (s n : Nat)
  /-- Nothing to divide: every weight is 0. -/
  | zeroTotalWeight
  /-- A negative weight at this position. -/
  | negativeWeight (i : Nat)
  /-- A distribution with no atoms. -/
  | emptyDist
  /-- The keys are not strictly increasing at this position. -/
  | keysNotIncreasing (i : Nat)
  /-- An atom of probability 0 at this position. -/
  | zeroAtom (i : Nat)
  /-- The atom probabilities do not sum to 1: the sum. -/
  | atomSumNotOne (s : Rat)
  /-- More atoms than the limit: the count and the limit. -/
  | tooManyAtoms (n max : Nat)
  /-- An input number above the bit limit: its position (0 for a lone number), its bits, the limit. -/
  | numberTooLarge (i bits max : Nat)
  /-- A quantile level at or below 0. -/
  | levelNotPositive (q : Rat)
  /-- A quantile level above 1. -/
  | levelAboveOne (q : Rat)
  /-- Conditioning on an event of probability 0. -/
  | nullEvent
  deriving DecidableEq, Repr

end VbmProb
