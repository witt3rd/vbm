import VbmDecision.Types
import VbmDecision.Refusal
import VbmDecision.Limits
/-! # Checking questions and answers (S3)

`Question.check` decides whether a question is well formed, `checkAnswer` whether an answer is well formed for its question, and `Question.checkThresholds` whether a set of thresholds is valid for a question. Each is a chain of guards in the order of the spec; the first guard that fails names the typed refusal. The Prop each one decides (`Question.Valid`, `WellFormed`, `Question.ThresholdsValid`) is stated apart from the check, and the proofs show the two agree. -/
namespace VbmDecision

/-- One guard of a check: the continuation if the condition holds, else the typed refusal at the field. -/
def guardWith (c : Prop) [Decidable c] (code : RefusalCode) (field : String) (k : Except Refusal Unit) : Except Refusal Unit :=
  if c then k else .error ⟨code, field⟩

/-- A length guard: `missingOption` when `len` is short of `n`, `unknownOption` when it is over. -/
def guardLen (len n : Nat) (field : String) (k : Except Refusal Unit) : Except Refusal Unit :=
  if len = n then k else if len < n then .error ⟨.missingOption, field⟩ else .error ⟨.unknownOption, field⟩

/-! ## Questions -/

/-- A well-formed question: a `choice` has 2 to `maxOptions` options with non-empty distinct names; a `score` has 2 to `maxLevels` levels. -/
def Question.Valid : Question → Prop
  | .noul .. => True
  | .choice _ os => 2 ≤ os.length ∧ os.length ≤ maxOptions ∧ (∀ o ∈ os, o.1 ≠ "") ∧ (os.map (·.1)).Nodup
  | .score _ ls => 2 ≤ ls.length ∧ ls.length ≤ maxLevels
  | .box _ => True

instance (q : Question) : Decidable q.Valid := by
  cases q <;> unfold Question.Valid <;> infer_instance

/-- Decide `Question.Valid`, or refuse with the first rule that fails (an empty option name is `badQuestionName`, a repeated one `duplicateKey`). -/
def Question.check : Question → Except Refusal Unit
  | .noul .. => .ok ()
  | .choice _ os =>
    guardWith (2 ≤ os.length) .tooFewOptions "criteria" <|
    guardWith (os.length ≤ maxOptions) .tooManyOptions "criteria" <|
    guardWith (∀ o ∈ os, o.1 ≠ "") .badQuestionName "criteria" <|
    guardWith (os.map (·.1)).Nodup .duplicateKey "criteria" (.ok ())
  | .score _ ls =>
    guardWith (2 ≤ ls.length) .tooFewLevels "criteria" <|
    guardWith (ls.length ≤ maxLevels) .tooManyLevels "criteria" (.ok ())
  | .box _ => .ok ()

/-! ## Answers -/

/-- A `choice` answer: its keys are exactly the options, each once; the probabilities sum to one within the epsilon; the selected option is listed and no other has a larger probability. -/
def ChoiceWF (os : List (String × Option String)) (sel : String) (ps : List (String × Prob)) : Prop :=
  (ps.map (·.1)).Nodup ∧ (∀ k ∈ ps.map (·.1), k ∈ os.map (·.1)) ∧ (∀ o ∈ os.map (·.1), o ∈ ps.map (·.1)) ∧
  SumOk os.length (ps.map (·.2)) ∧ sel ∈ os.map (·.1) ∧ ∃ p ∈ ps, p.1 = sel ∧ ∀ r ∈ ps, r.2.val ≤ p.2.val

instance (os : List (String × Option String)) (sel : String) (ps : List (String × Prob)) : Decidable (ChoiceWF os sel ps) := by
  unfold ChoiceWF; infer_instance

/-- The position implied by the probabilities: the sum of `i × pᵢ` from index `i` on, in millionths of an index. -/
def scoreWeighted : Nat → List Prob → Nat
  | _, [] => 0
  | i, p :: ps => i * p.val + scoreWeighted (i + 1) ps

/-- The tolerance between a position and its probabilities: `entryError × (n(n-1)/2 + 1)`. -/
def scoreTolerance (n : Nat) : Nat := Prob.entryError * (n * (n - 1) / 2 + 1)

/-- A `score` answer over the question's `levels`: lengths, legend, sum rule, position on the scale, position consistent with the probabilities. -/
def ScoreWF (levels : List String) (x : Pos) (ps : List Prob) (legend : List String) : Prop :=
  ps.length = levels.length ∧ legend.length = levels.length ∧ legend = levels ∧ SumOk levels.length ps ∧
  x ≤ (levels.length - 1) * scale ∧
  x ≤ scoreWeighted 0 ps + scoreTolerance levels.length ∧ scoreWeighted 0 ps ≤ x + scoreTolerance levels.length

instance (levels : List String) (x : Pos) (ps : List Prob) (legend : List String) : Decidable (ScoreWF levels x ps legend) := by
  unfold ScoreWF; infer_instance

/-- A `box` answer: a positive extent in both directions. -/
def BoxWF (b : Box) : Prop := b.top.val < b.bottom.val ∧ b.left.val < b.right.val

instance (b : Box) : Decidable (BoxWF b) := by
  unfold BoxWF; infer_instance

/-- A well-formed answer for a question; an answer of another kind than its question is not well formed. -/
def WellFormed : Question → Answer → Prop
  | .noul .., .noul _ => True
  | .choice _ os, .choice sel ps _ => ChoiceWF os sel ps
  | .score _ ls, .score x _ ps lg => ScoreWF ls x ps lg
  | .box _, .box b _ => BoxWF b
  | _, _ => False

instance (q : Question) (a : Answer) : Decidable (WellFormed q a) := by
  unfold WellFormed; split <;> infer_instance

/-- Decide the `choice` rules, refusing with the first that fails. -/
def checkChoice (os : List (String × Option String)) (sel : String) (ps : List (String × Prob)) : Except Refusal Unit :=
  guardWith (ps.map (·.1)).Nodup .duplicateKey "probabilities" <|
  guardWith (∀ k ∈ ps.map (·.1), k ∈ os.map (·.1)) .unknownOption "probabilities" <|
  guardWith (∀ o ∈ os.map (·.1), o ∈ ps.map (·.1)) .missingOption "probabilities" <|
  guardWith (SumOk os.length (ps.map (·.2))) .sumOffOne "probabilities" <|
  guardWith (sel ∈ os.map (·.1)) .unknownOption "choice" <|
  guardWith (∃ p ∈ ps, p.1 = sel ∧ ∀ r ∈ ps, r.2.val ≤ p.2.val) .selectedNotMaximal "choice" (.ok ())

/-- Decide the `score` rules, refusing with the first that fails. -/
def checkScore (levels : List String) (x : Pos) (ps : List Prob) (legend : List String) : Except Refusal Unit :=
  guardLen ps.length levels.length "probabilities" <|
  guardLen legend.length levels.length "legend" <|
  guardWith (legend = levels) .legendMismatch "legend" <|
  guardWith (SumOk levels.length ps) .sumOffOne "probabilities" <|
  guardWith (x ≤ (levels.length - 1) * scale) .scoreOutOfScale "score" <|
  guardWith (x ≤ scoreWeighted 0 ps + scoreTolerance levels.length ∧ scoreWeighted 0 ps ≤ x + scoreTolerance levels.length)
    .scoreInconsistent "score" (.ok ())

/-- Decide the `box` rules: an inverted box is `boxInverted`, an empty or zero-area one `boxEmpty`. -/
def checkBox (b : Box) : Except Refusal Unit :=
  guardWith (b.top.val ≤ b.bottom.val ∧ b.left.val ≤ b.right.val) .boxInverted "box" <|
  guardWith (BoxWF b) .boxEmpty "box" (.ok ())

/-- Decide `WellFormed`, or refuse: an answer of another kind than its question is `typeMismatch`. -/
def checkAnswer : Question → Answer → Except Refusal Unit
  | .noul .., .noul _ => .ok ()
  | .choice _ os, .choice sel ps _ => checkChoice os sel ps
  | .score _ ls, .score x _ ps lg => checkScore ls x ps lg
  | .box _, .box b _ => checkBox b
  | _, _ => .error ⟨.typeMismatch, ""⟩

/-! ## Thresholds -/

/-- Thresholds valid for a question: the same kind, and `no < yes` for a noul; `lo ≤ hi ≤ (n-1) × scale` for a score of `n` levels. -/
def Question.ThresholdsValid : Question → Thresholds → Prop
  | .noul .., .noul no yes => no.val < yes.val
  | .choice .., .choice _ _ => True
  | .score _ ls, .score lo hi _ => lo ≤ hi ∧ hi ≤ (ls.length - 1) * scale
  | .box _, .box _ => True
  | _, _ => False

instance (q : Question) (t : Thresholds) : Decidable (q.ThresholdsValid t) := by
  unfold Question.ThresholdsValid; split <;> infer_instance

/-- Decide `ThresholdsValid`, or refuse at `thresholds`: `thresholdKind` for another kind, `badThresholds` for a bad value. -/
def Question.checkThresholds (q : Question) (t : Thresholds) : Except Refusal Unit :=
  guardWith (q.kindOf = t.kindOf) .thresholdKind "thresholds" <|
  guardWith (q.ThresholdsValid t) .badThresholds "thresholds" (.ok ())

end VbmDecision
