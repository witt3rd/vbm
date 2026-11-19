import VbmProb.Prob.Bayes
/-! # Bayes' rule and conditional probability: the properties PR6 to PR9, each with its witness -/
namespace VbmProb
namespace Prob

/-- A literal probability for the witnesses (the bounds are decided by the kernel). -/
private def lit (q : Rat) (h0 : 0 ≤ q := by decide +kernel) (h1 : q ≤ 1 := by decide +kernel) : Prob := ⟨q, h0, h1⟩

/-- Cancelling a non-zero factor on the right. -/
theorem rat_eq_of_mul_eq {a b c : Rat} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  rw [← Rat.mul_div_cancel (a := a) hc, h, Rat.mul_div_cancel hc]

/-! ## PR6: `bayes` -/

/-- PR6: the value of the evidence is the law of total probability. -/
theorem evidence_val (prior like likeNot : Prob) :
    (evidence prior like likeNot).val = prior.val * like.val + (1 - prior.val) * likeNot.val := rfl

/-- PR6: `bayes` succeeds exactly when the evidence is not 0. -/
theorem bayes_ok_iff (prior like likeNot : Prob) :
    (∃ r, bayes prior like likeNot = .ok r) ↔ (evidence prior like likeNot).val ≠ 0 := by
  unfold bayes
  by_cases h : (evidence prior like likeNot).val = 0 <;> simp [h]

/-- PR6: the evidence is zero exactly when `bayes` refuses `zeroEvidence`. -/
theorem bayes_zeroEvidence {prior like likeNot : Prob} (h : (evidence prior like likeNot).val = 0) :
    bayes prior like likeNot = .error .zeroEvidence := by
  simp [bayes, h]

/-- PR6: the quotient form of the posterior. -/
theorem bayes_val {prior like likeNot r : Prob} (h : bayes prior like likeNot = .ok r) :
    r.val = prior.val * like.val / (evidence prior like likeNot).val := by
  unfold bayes at h
  by_cases h0 : (evidence prior like likeNot).val = 0
  · simp [h0] at h
  · simp only [h0, dite_false, Except.ok.injEq] at h
    cases h; rfl

/-- PR6: the defining equation of Bayes' rule. -/
theorem bayes_mul_evidence {prior like likeNot r : Prob} (h : bayes prior like likeNot = .ok r) :
    r.val * (evidence prior like likeNot).val = prior.val * like.val := by
  have hne : (evidence prior like likeNot).val ≠ 0 := (bayes_ok_iff _ _ _).mp ⟨r, h⟩
  rw [bayes_val h]; exact Rat.div_mul_cancel hne

/-- PR6: the quotient written out. -/
theorem bayes_val_expanded {prior like likeNot r : Prob} (h : bayes prior like likeNot = .ok r) :
    r.val = prior.val * like.val / (prior.val * like.val + (1 - prior.val) * likeNot.val) :=
  bayes_val h

/-- A witness helper: a non-zero evidence gives a posterior with the quotient value. -/
theorem bayes_exists {prior like likeNot : Prob} (h : (evidence prior like likeNot).val ≠ 0) :
    ∃ r, bayes prior like likeNot = .ok r ∧ r.val = prior.val * like.val / (evidence prior like likeNot).val :=
  let ⟨r, hr⟩ := (bayes_ok_iff _ _ _).mpr h
  ⟨r, hr, bayes_val hr⟩

-- Non-vacuity witnesses for PR6.
example : ∃ r, bayes (lit (1/100)) (lit (99/100)) (lit (5/100)) = .ok r ∧ r.val = 1/6 := by
  obtain ⟨r, hr, hv⟩ := bayes_exists (prior := lit (1/100)) (like := lit (99/100)) (likeNot := lit (5/100)) (by decide +kernel)
  refine ⟨r, hr, ?_⟩
  rw [hv]; change (1/100 : Rat) * (99/100) / ((1/100) * (99/100) + (1 - 1/100) * (5/100)) = 1/6
  decide +kernel
example : bayes (lit (1/2)) (lit 0) (lit 0) = .error .zeroEvidence :=
  bayes_zeroEvidence (by decide +kernel)

/-! ## PR7: the boundaries -/

/-- PR7: a prior of 0 gives posterior 0. -/
theorem bayes_prior_zero {prior like likeNot r : Prob} (hp : prior.val = 0)
    (h : bayes prior like likeNot = .ok r) : r.val = 0 := by
  have e := bayes_mul_evidence h
  have hne : (evidence prior like likeNot).val ≠ 0 := (bayes_ok_iff _ _ _).mp ⟨r, h⟩
  rw [hp, Rat.zero_mul] at e
  exact (Rat.mul_eq_zero.mp e).resolve_right hne

/-- PR7: a prior of 1 gives posterior 1. -/
theorem bayes_prior_one {prior like likeNot r : Prob} (hp : prior.val = 1)
    (h : bayes prior like likeNot = .ok r) : r.val = 1 := by
  have e := bayes_mul_evidence h
  have hne : (evidence prior like likeNot).val ≠ 0 := (bayes_ok_iff _ _ _).mp ⟨r, h⟩
  refine rat_eq_of_mul_eq hne ?_
  have h11 : (1 : Rat) - 1 = 0 := by decide +kernel
  rw [e, Rat.one_mul, evidence_val, hp, h11, Rat.zero_mul, Rat.add_zero, Rat.one_mul]

/-- PR7: evidence that does not discriminate leaves the prior unchanged. -/
theorem bayes_like_eq {prior like likeNot r : Prob} (hl : like.val = likeNot.val)
    (h : bayes prior like likeNot = .ok r) : r.val = prior.val := by
  have e := bayes_mul_evidence h
  have hne : (evidence prior like likeNot).val ≠ 0 := (bayes_ok_iff _ _ _).mp ⟨r, h⟩
  have hev : (evidence prior like likeNot).val = like.val := by
    rw [evidence_val, ← hl, ← Rat.add_mul, Rat.sub_eq_add_neg, ← Rat.add_assoc, Rat.add_comm prior.val 1,
      Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero, Rat.one_mul]
  have hlne : like.val ≠ 0 := hev ▸ hne
  refine rat_eq_of_mul_eq hlne ?_
  rw [← hev]; rw [e, hev]

/-- PR7: no evidence under the complement, and some under the hypothesis, gives posterior 1. -/
theorem bayes_likeNot_zero {prior like likeNot r : Prob} (hn : likeNot.val = 0) (_hl : 0 < like.val)
    (h : bayes prior like likeNot = .ok r) : r.val = 1 := by
  have e := bayes_mul_evidence h
  have hne : (evidence prior like likeNot).val ≠ 0 := (bayes_ok_iff _ _ _).mp ⟨r, h⟩
  refine rat_eq_of_mul_eq hne ?_
  rw [e, Rat.one_mul, evidence_val, hn, Rat.mul_zero, Rat.add_zero]

-- Non-vacuity witnesses for PR7 (the hypotheses hold and the evidence is not 0).
example : ∃ r, bayes (lit (1/2)) (lit 1) (lit 0) = .ok r ∧ r.val = 1 := by
  obtain ⟨r, hr, _⟩ := bayes_exists (prior := lit (1/2)) (like := lit 1) (likeNot := lit 0) (by decide +kernel)
  exact ⟨r, hr, bayes_likeNot_zero (by decide +kernel) (by decide +kernel) hr⟩
example : ∃ r, bayes (lit (1/3)) (lit (1/2)) (lit (1/2)) = .ok r ∧ r.val = 1/3 := by
  obtain ⟨r, hr, _⟩ := bayes_exists (prior := lit (1/3)) (like := lit (1/2)) (likeNot := lit (1/2)) (by decide +kernel)
  exact ⟨r, hr, bayes_like_eq (by decide +kernel) hr⟩
example : ∃ r, bayes (lit 0) (lit (1/2)) (lit (1/4)) = .ok r ∧ r.val = 0 := by
  obtain ⟨r, hr, _⟩ := bayes_exists (prior := lit 0) (like := lit (1/2)) (likeNot := lit (1/4)) (by decide +kernel)
  exact ⟨r, hr, bayes_prior_zero (by decide +kernel) hr⟩
example : ∃ r, bayes (lit 1) (lit (1/2)) (lit (1/4)) = .ok r ∧ r.val = 1 := by
  obtain ⟨r, hr, _⟩ := bayes_exists (prior := lit 1) (like := lit (1/2)) (likeNot := lit (1/4)) (by decide +kernel)
  exact ⟨r, hr, bayes_prior_one (by decide +kernel) hr⟩

/-! ## PR8: `conditional` -/

/-- PR8: `conditional` succeeds exactly when the marginal is not 0 and the joint is at most the marginal. -/
theorem conditional_ok_iff (joint marginal : Prob) :
    (∃ r, conditional joint marginal = .ok r) ↔ marginal.val ≠ 0 ∧ joint.val ≤ marginal.val := by
  unfold conditional
  by_cases h0 : marginal.val = 0
  · simp [h0]
  · by_cases h1 : marginal.val < joint.val
    · simp [h0, h1, Rat.not_le.mpr h1]
    · simp [h0, h1, Rat.not_lt.mp h1]

/-- PR8: the defining equation of a conditional probability. -/
theorem conditional_mul {joint marginal r : Prob} (h : conditional joint marginal = .ok r) :
    r.val * marginal.val = joint.val := by
  have hm : marginal.val ≠ 0 := ((conditional_ok_iff _ _).mp ⟨r, h⟩).1
  unfold conditional at h
  simp only [hm, dite_false] at h
  by_cases h1 : marginal.val < joint.val
  · simp [h1] at h
  · simp only [h1, dite_false, Except.ok.injEq] at h
    cases h; exact Rat.div_mul_cancel hm

/-- PR8: a zero marginal is refused as `zeroMarginal`. -/
theorem conditional_zeroMarginal {joint marginal : Prob} (h : marginal.val = 0) :
    conditional joint marginal = .error .zeroMarginal := by
  simp [conditional, h]

/-- PR8: a joint above a non-zero marginal is refused as `jointExceedsMarginal`. -/
theorem conditional_jointExceedsMarginal {joint marginal : Prob} (h0 : marginal.val ≠ 0)
    (h : marginal.val < joint.val) : conditional joint marginal = .error .jointExceedsMarginal := by
  simp [conditional, h0, h]

-- Non-vacuity witnesses for PR8.
example : ∃ r, conditional (lit (1/4)) (lit (1/2)) = .ok r ∧ r.val = 1/2 := by
  obtain ⟨r, hr⟩ := (conditional_ok_iff (lit (1/4)) (lit (1/2))).mpr ⟨by decide +kernel, by decide +kernel⟩
  refine ⟨r, hr, rat_eq_of_mul_eq (c := 1/2) (by decide +kernel) ?_⟩
  have e := conditional_mul hr
  change r.val * (1/2) = 1/4 at e
  rw [e]; decide +kernel
example : conditional (lit (3/4)) (lit (1/2)) = .error .jointExceedsMarginal :=
  conditional_jointExceedsMarginal (by decide +kernel) (by decide +kernel)
example : conditional (lit 0) (lit 0) = .error .zeroMarginal :=
  conditional_zeroMarginal (by decide +kernel)

/-! ## PR9: Bayes agrees with conditioning -/

/-- PR9: with non-zero evidence, `bayes` is `conditional` of the joint on the evidence. -/
theorem bayes_eq_conditional {prior like likeNot : Prob} (h : (evidence prior like likeNot).val ≠ 0) :
    bayes prior like likeNot = conditional (mul prior like) (evidence prior like likeNot) := by
  have hn : ¬ (evidence prior like likeNot).val < (mul prior like).val :=
    Rat.not_lt.mpr (mul_le_evidence prior like likeNot)
  simp [bayes, conditional, h, hn]

/-- PR9: the joint of the hypothesis and the evidence is never above the evidence, so `conditional` here never refuses `jointExceedsMarginal`. -/
theorem conditional_evidence_ne_jointExceeds (prior like likeNot : Prob) :
    conditional (mul prior like) (evidence prior like likeNot) ≠ .error .jointExceedsMarginal := by
  have hn : ¬ (evidence prior like likeNot).val < (mul prior like).val :=
    Rat.not_lt.mpr (mul_le_evidence prior like likeNot)
  unfold conditional
  by_cases h0 : (evidence prior like likeNot).val = 0 <;> simp [h0, hn]

/-- PR9: with zero evidence both refuse (`bayes` as `zeroEvidence`, `conditional` as `zeroMarginal`). -/
theorem bayes_conditional_zero {prior like likeNot : Prob} (h : (evidence prior like likeNot).val = 0) :
    bayes prior like likeNot = .error .zeroEvidence ∧
    conditional (mul prior like) (evidence prior like likeNot) = .error .zeroMarginal :=
  ⟨bayes_zeroEvidence h, conditional_zeroMarginal h⟩

-- Non-vacuity witness for PR9: the PR6 witness (non-zero evidence), and a zero-evidence case where both refuse.
example : bayes (lit (1/100)) (lit (99/100)) (lit (5/100)) = conditional (mul (lit (1/100)) (lit (99/100)))
    (evidence (lit (1/100)) (lit (99/100)) (lit (5/100))) :=
  bayes_eq_conditional (by decide +kernel)
example : bayes (lit (1/2)) (lit 0) (lit 0) = .error .zeroEvidence ∧
    conditional (mul (lit (1/2)) (lit 0)) (evidence (lit (1/2)) (lit 0) (lit 0)) = .error .zeroMarginal :=
  bayes_conditional_zero (by decide +kernel)

end Prob
end VbmProb
