import VbmProb.Prob
/-! # Bayes' rule and conditional probability

The total probability of the evidence, the posterior of a hypothesis, and `P(A|B)`, each an exact `Rat` quotient that is a probability by construction (`docs/spec.md`, "Probability"). -/
namespace VbmProb
namespace Prob

/-- A product of two probabilities is at most its left factor (on the values). -/
theorem mul_val_le_left (p q : Prob) : (mul p q).val ≤ p.val := by
  have := Rat.mul_le_mul_of_nonneg_left q.le_one p.nonneg
  rwa [Rat.mul_one] at this

/-- Adding inequalities (core has only the one-sided iff forms). -/
theorem rat_add_le_add {a b c e : Rat} (h : a ≤ b) (h' : c ≤ e) : a + c ≤ b + e :=
  Rat.le_trans (Rat.add_le_add_right.mpr h) (Rat.add_le_add_left.mpr h')

/-- The probability of the evidence: `prior·like + (1−prior)·likeNot` (the law of total probability). -/
def evidence (prior like likeNot : Prob) : Prob :=
  ⟨(mul prior like).val + (mul (complement prior) likeNot).val,
   Rat.add_nonneg (mul prior like).nonneg (mul (complement prior) likeNot).nonneg,
   Rat.le_trans (rat_add_le_add (mul_val_le_left prior like) (mul_val_le_left (complement prior) likeNot))
     (by change prior.val + (1 - prior.val) ≤ 1
         rw [Rat.sub_eq_add_neg, ← Rat.add_assoc, Rat.add_comm prior.val 1, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]
         exact Rat.le_refl)⟩

/-- The quotient `a / b` as a probability, for `a ≤ b` and `b ≠ 0`. -/
def ratio (a b : Prob) (hab : a.val ≤ b.val) (hb : b.val ≠ 0) : Prob :=
  have hpos : 0 < b.val := Rat.lt_of_le_of_ne b.nonneg (Ne.symm hb)
  ⟨a.val / b.val,
   Rat.mul_nonneg a.nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hpos)),
   Rat.le_of_mul_le_mul_right (c := b.val)
     (by rw [Rat.div_mul_cancel hb, Rat.one_mul]; exact hab) hpos⟩

/-- The evidence is at least the joint of hypothesis and evidence. -/
theorem mul_le_evidence (prior like likeNot : Prob) :
    (mul prior like).val ≤ (evidence prior like likeNot).val := by
  have := Rat.add_le_add_left (c := (mul prior like).val) |>.mpr (mul (complement prior) likeNot).nonneg
  rwa [Rat.add_zero] at this

/-- The posterior of a hypothesis `H` (`prior = P(H)`, `like = P(E|H)`, `likeNot = P(E|¬H)`): refused when the evidence has probability 0. -/
def bayes (prior like likeNot : Prob) : Except Refusal Prob :=
  if h : (evidence prior like likeNot).val = 0 then .error .zeroEvidence
  else .ok (ratio (mul prior like) (evidence prior like likeNot) (mul_le_evidence prior like likeNot) h)

/-- `P(A|B)` from `P(A∧B)` and `P(B)`: refused for a zero marginal, or a joint above the marginal. -/
def conditional (joint marginal : Prob) : Except Refusal Prob :=
  if h0 : marginal.val = 0 then .error .zeroMarginal
  else if h1 : marginal.val < joint.val then .error .jointExceedsMarginal
  else .ok (ratio joint marginal (Rat.not_lt.mp h1) h0)

end Prob
end VbmProb
