import VbmDecision.Check
/-! # The threshold truth table (S4)

`decide` turns a checked answer and its thresholds into an `Outcome`. The gate comes first and fails closed (spec section 5.2, rules 1 to 3): an invalid question, an answer not well formed for it, a binding of another model or snapshot, thresholds of another kind or not valid are each a typed refusal, never a decision and never an abstention. Only when the gate passes does the table (rule 4) run. -/
namespace VbmDecision

/-- The binding is for the model that was requested and, if it pins a snapshot, the snapshot that answered. -/
def BindingOk (b : Binding) (c : Context) : Prop :=
  b.model = c.requested ∧ (b.snapshot = none ∨ b.snapshot = some c.snapshot)

instance (b : Binding) (c : Context) : Decidable (BindingOk b c) := by unfold BindingOk; infer_instance

/-- Rules 1 to 3 in order: the question, the answer, the model, the snapshot, the thresholds; the first that fails names the refusal. -/
def gate (b : Binding) (c : Context) (q : Question) (a : Answer) : Except Refusal Unit :=
  match q.check with
  | .error r => .error r
  | .ok () =>
    match checkAnswer q a with
    | .error r => .error r
    | .ok () =>
      guardWith (b.model = c.requested) .modelMismatch "model" <|
      guardWith (b.snapshot = none ∨ b.snapshot = some c.snapshot) .snapshotMismatch "snapshot" <|
      q.checkThresholds b.thresholds

/-- The probability of the selected option: the entry under its key (the keys are distinct in a well-formed answer). -/
def selProb (sel : String) : List (String × Prob) → Option Prob
  | [] => none
  | e :: es => if e.1 = sel then some e.2 else selProb sel es

/-- The runner-up: the largest probability among the options other than the selected one (`0`, the identity of `max`, if there is none, which a well-formed answer never has). -/
def runnerUp (sel : String) : List (String × Prob) → Nat
  | [] => 0
  | e :: es => if e.1 = sel then runnerUp sel es else max e.2.val (runnerUp sel es)

/-- The `choice` row of the table: below `minProb` abstain on probability; else below `minMargin` abstain on margin; else the selected option. -/
def choiceTable (minProb minMargin : Prob) (sel : String) (ps : List (String × Prob)) : Outcome Refusal :=
  match selProb sel ps with
  | none => .refused ⟨.unknownOption, "choice"⟩
  | some v =>
    if v.val < minProb.val then .abstain .lowProbability
    else if v.val - runnerUp sel ps < minMargin.val then .abstain .lowMargin
    else .decided (.option sel)

/-- Rule 4: the table by kind, on an answer and thresholds that the gate has passed. -/
def table : Thresholds → Answer → Outcome Refusal
  | .noul no yes, .noul p =>
    if yes.val ≤ p.val then .decided .yes
    else if p.val ≤ no.val then .decided .no
    else .abstain .uncertainBand
  | .choice mp mm, .choice sel ps _ => choiceTable mp mm sel ps
  | .score lo hi mc, .score x conf _ _ =>
    if conf.val < mc.val then .abstain .lowConfidence
    else if x < lo then .decided .below
    else if hi < x then .decided .above
    else .decided .within
  | .box mc, .box b conf =>
    if conf.val < mc.val then .abstain .lowConfidence else .decided (.found b)
  | _, _ => .refused ⟨.thresholdKind, "thresholds"⟩

/-- The truth table: total, and it fails closed (the gate refuses before the table decides). -/
def decide (b : Binding) (c : Context) (q : Question) (a : Answer) : Outcome Refusal :=
  match gate b c q a with
  | .error r => .refused r
  | .ok () => table b.thresholds a

end VbmDecision
