import VbmDecision.Check
/-! # Checking questions and answers (S3): proofs

T1 `check-sound-complete`: `checkAnswer q a = ok ()` iff `WellFormed q a`, and likewise `Question.check` for `Question.Valid` and `Question.checkThresholds` for `Question.ThresholdsValid`. Each check is a chain of guards; a chain succeeds iff every guard holds. -/
namespace VbmDecision

theorem guardWith_ok (c : Prop) [Decidable c] (code : RefusalCode) (field : String) (k : Except Refusal Unit) :
    guardWith c code field k = .ok () ↔ c ∧ k = .ok () := by
  unfold guardWith; by_cases h : c <;> simp [h]

theorem guardLen_ok (len n : Nat) (field : String) (k : Except Refusal Unit) :
    guardLen len n field k = .ok () ↔ len = n ∧ k = .ok () := by
  unfold guardLen; by_cases h : len = n <;> simp [h]
  by_cases h2 : len < n <;> simp [h2]

/-- T1 for questions: the check succeeds iff the question is valid. -/
theorem question_check_ok_iff (q : Question) : q.check = .ok () ↔ q.Valid := by
  cases q <;> simp [Question.check, Question.Valid, guardWith_ok]

/-- T1 for answers: the check succeeds iff the answer is well formed for the question. -/
theorem checkAnswer_ok_iff (q : Question) (a : Answer) : checkAnswer q a = .ok () ↔ WellFormed q a := by
  cases q <;> cases a <;>
    simp [checkAnswer, WellFormed, checkChoice, checkScore, checkBox, ChoiceWF, ScoreWF, BoxWF,
      guardWith_ok, guardLen_ok, and_assoc]
  omega

/-- T1 for thresholds: the check succeeds iff the thresholds are valid for the question. -/
theorem checkThresholds_ok_iff (q : Question) (t : Thresholds) : q.checkThresholds t = .ok () ↔ q.ThresholdsValid t := by
  cases q <;> cases t <;> simp [Question.checkThresholds, Question.ThresholdsValid, Question.kindOf, Thresholds.kindOf, guardWith_ok]

/-- A check refuses exactly when the property fails: the refusal case of T1. -/
theorem checkAnswer_error_iff (q : Question) (a : Answer) : (∃ r, checkAnswer q a = .error r) ↔ ¬ WellFormed q a := by
  rw [← checkAnswer_ok_iff]
  cases h : checkAnswer q a <;> simp

/-- A kind mismatch is refused as `typeMismatch`. -/
theorem checkAnswer_typeMismatch (q : Question) (a : Answer) (h : q.kindOf ≠ a.kindOf) :
    checkAnswer q a = .error ⟨.typeMismatch, ""⟩ := by
  cases q <;> cases a <;> simp_all [checkAnswer, Question.kindOf, Answer.kindOf]

/-! ## Witnesses: a well-formed instance of each kind and one violating each rule -/

set_option maxRecDepth 4000

private def p (n : Nat) (h : n ≤ 1000000 := by decide) : Prob := ⟨n, h⟩

private def qc : Question := .choice "t" [("calm", none), ("angry", some "hostile")]
private def qs : Question := .score "u" ["none", "some", "high"]

example : Question.check (.noul "i" none) = .ok () := by rfl
example : qc.check = .ok () := by rfl
example : qs.check = .ok () := by rfl
example : (Question.box "i").check = .ok () := by rfl
example : (Question.choice "t" [("a", none)]).check = .error ⟨.tooFewOptions, "criteria"⟩ := by rfl
example : (Question.choice "t" [("a", none), ("", none)]).check = .error ⟨.badQuestionName, "criteria"⟩ := by rfl
example : (Question.choice "t" [("a", none), ("a", none)]).check = .error ⟨.duplicateKey, "criteria"⟩ := by rfl
example : (Question.score "u" ["only"]).check = .error ⟨.tooFewLevels, "criteria"⟩ := by rfl

example : checkAnswer (.noul "i" none) (.noul (p 973100)) = .ok () := by rfl
example : checkAnswer qc (.choice "calm" [("calm", p 800000), ("angry", p 200000)] (p 800000)) = .ok () := by rfl
example : checkAnswer qc (.choice "calm" [("angry", p 200000), ("calm", p 800000)] (p 800000)) = .ok () := by rfl
example : checkAnswer qc (.choice "calm" [("calm", p 700000), ("angry", p 100000)] (p 700000)) = .error ⟨.sumOffOne, "probabilities"⟩ := by rfl
example : checkAnswer qc (.choice "happy" [("calm", p 800000), ("angry", p 200000)] (p 800000)) = .error ⟨.unknownOption, "choice"⟩ := by rfl
example : checkAnswer qc (.choice "angry" [("calm", p 800000), ("angry", p 200000)] (p 800000)) = .error ⟨.selectedNotMaximal, "choice"⟩ := by rfl
example : checkAnswer qc (.choice "calm" [("calm", p 800000), ("calm", p 200000)] (p 800000)) = .error ⟨.duplicateKey, "probabilities"⟩ := by rfl
example : checkAnswer qc (.choice "calm" [("calm", p 800000), ("other", p 200000)] (p 800000)) = .error ⟨.unknownOption, "probabilities"⟩ := by rfl
example : checkAnswer qc (.choice "calm" [("calm", p 1000000)] (p 800000)) = .error ⟨.missingOption, "probabilities"⟩ := by rfl
example : checkAnswer qs (.score 1500000 (p 700000) [p 0, p 500000, p 500000] ["none", "some", "high"]) = .ok () := by rfl
example : checkAnswer qs (.score 2500000 (p 700000) [p 0, p 500000, p 500000] ["none", "some", "high"]) = .error ⟨.scoreOutOfScale, "score"⟩ := by rfl
example : checkAnswer qs (.score 500000 (p 700000) [p 0, p 500000, p 500000] ["none", "some", "high"]) = .error ⟨.scoreInconsistent, "score"⟩ := by rfl
example : checkAnswer qs (.score 1500000 (p 700000) [p 0, p 500000, p 500000] ["none", "some", "low"]) = .error ⟨.legendMismatch, "legend"⟩ := by rfl
example : checkAnswer qs (.score 1500000 (p 700000) [p 0, p 500000, p 500000] ["none", "some"]) = .error ⟨.missingOption, "legend"⟩ := by rfl
example : checkAnswer qs (.score 1500000 (p 700000) [p 0, p 500000, p 500000, p 0] ["none", "some", "high"]) = .error ⟨.unknownOption, "probabilities"⟩ := by rfl
example : checkAnswer qs (.score 1500000 (p 700000) [p 0, p 500000, p 100000] ["none", "some", "high"]) = .error ⟨.sumOffOne, "probabilities"⟩ := by rfl
example : checkAnswer (.box "i") (.box ⟨p 200000, p 600000, p 100000, p 900000⟩ (p 800000)) = .ok () := by rfl
example : checkAnswer (.box "i") (.box ⟨p 600000, p 200000, p 100000, p 900000⟩ (p 800000)) = .error ⟨.boxInverted, "box"⟩ := by rfl
example : checkAnswer (.box "i") (.box ⟨p 200000, p 200000, p 100000, p 900000⟩ (p 800000)) = .error ⟨.boxEmpty, "box"⟩ := by rfl
example : checkAnswer (.noul "i" none) (.choice "a" [] (p 0)) = .error ⟨.typeMismatch, ""⟩ := by rfl

example : (Question.noul "i" none).checkThresholds (.noul (p 300000) (p 800000)) = .ok () := by rfl
example : (Question.noul "i" none).checkThresholds (.noul (p 800000) (p 800000)) = .error ⟨.badThresholds, "thresholds"⟩ := by rfl
example : (Question.noul "i" none).checkThresholds (.box (p 800000)) = .error ⟨.thresholdKind, "thresholds"⟩ := by rfl
example : qs.checkThresholds (.score 1000000 2000000 (p 500000)) = .ok () := by rfl
example : qs.checkThresholds (.score 2000000 1000000 (p 500000)) = .error ⟨.badThresholds, "thresholds"⟩ := by rfl
example : qs.checkThresholds (.score 1000000 3000000 (p 500000)) = .error ⟨.badThresholds, "thresholds"⟩ := by rfl

end VbmDecision
