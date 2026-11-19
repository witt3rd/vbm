import VbmDecision.Limits
/-! # Named limits (S1b): the values, and what they imply, as decided facts -/
namespace VbmDecision

/-- The values of section 8. -/
theorem limits_values :
    scale = 1000000 ∧ Prob.entryError = 100 ∧ maxQuestions = 32 ∧ maxOptions = 64 ∧ maxLevels = 64 ∧
    maxStateParts = 256 ∧ Decimal.maxExponent = 1000 ∧ maxNestingDepth = 32 ∧ minSample = 100 ∧
    minPerClass = 10 ∧ minSupport = 30 ∧ maxSample = 10000 := by decide

/-- The sum rule's tolerance is at most 6400 millionths for any permitted option or level count. -/
theorem sumEpsilon_le (n : Nat) (h : n ≤ maxOptions) : Prob.sumEpsilon n ≤ 6400 := by
  unfold Prob.sumEpsilon Prob.entryError maxOptions at *; omega

-- Non-vacuity: the bound is met with equality at the maximum.
example : Prob.sumEpsilon maxOptions = 6400 := by decide
example : Prob.sumEpsilon 2 ≤ 6400 := sumEpsilon_le 2 (by decide)

/-- The tolerance stays well under one (so the sum rule still checks something). -/
theorem sumEpsilon_lt_scale (n : Nat) (h : n ≤ maxOptions ∨ n ≤ maxLevels) : Prob.sumEpsilon n < scale := by
  unfold Prob.sumEpsilon Prob.entryError scale maxOptions maxLevels at *; omega

example : Prob.sumEpsilon maxLevels < scale := sumEpsilon_lt_scale _ (Or.inr (Nat.le_refl _))

/-- The calibration limits agree: both classes fit in the least sample, the support fits in it, and the least sample fits in the largest. -/
theorem calibration_limits_consistent :
    2 * minPerClass ≤ minSample ∧ minSupport ≤ minSample ∧ minSample ≤ maxSample := by decide

/-- The quadratic reference definition does at most 10^8 steps on the largest sample. -/
theorem maxSample_quadratic : maxSample * maxSample = 100000000 := by decide

/-- The structural limits leave room for what the spec requires: a choice and a score need two entries, and every cap is at least that. -/
theorem structural_limits_roomy : 2 ≤ maxOptions ∧ 2 ≤ maxLevels ∧ 1 ≤ maxQuestions ∧ 1 ≤ maxStateParts := by decide

end VbmDecision
