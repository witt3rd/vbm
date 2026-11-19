import VbmDecision.Refusal
/-! # Typed refusals (S1b): the list of codes is complete and has no repeat, with witnesses

The spec's property section names no property of this slice; the facts below are the obligations recorded in the ledger. -/
namespace VbmDecision

/-- Every refusal code is in `RefusalCode.all`. -/
theorem refusalCode_all_complete (c : RefusalCode) : c ∈ RefusalCode.all := by
  cases c <;> decide +kernel

/-- No refusal code is listed twice. -/
theorem refusalCode_all_nodup : RefusalCode.all.Nodup := by decide +kernel

/-- The spec's section 9 lists forty-four codes. -/
theorem refusalCode_count : RefusalCode.all.length = 44 := by decide

/-- Distinct codes are distinct refusals, and the field is part of the refusal. -/
theorem refusal_ext_code (a b : RefusalCode) (f : String) (h : a ≠ b) :
    (Refusal.mk a f) ≠ (Refusal.mk b f) := by
  intro e; exact h (congrArg Refusal.code e)

-- Non-vacuity: two distinct codes at one path, and one code at two paths.
example : (Refusal.mk .outOfRange "answers.overdue.noul") ≠ (Refusal.mk .tooPrecise "answers.overdue.noul") :=
  refusal_ext_code _ _ _ (by decide)
example : (Refusal.mk .negative "a") ≠ (Refusal.mk .negative "b") := by decide

/-- The numeric refusals of S1a map to distinct spec codes. -/
theorem scaleRefusal_toCode_injective (a b : ScaleRefusal) (h : a.toCode = b.toCode) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)

-- Non-vacuity: the map on each constructor.
example : ScaleRefusal.tooPrecise.toCode = RefusalCode.tooPrecise := rfl
example : ScaleRefusal.exponentTooLarge.toCode = RefusalCode.exponentTooLarge := rfl

end VbmDecision
