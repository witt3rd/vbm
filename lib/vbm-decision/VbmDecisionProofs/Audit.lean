import VbmDecision.Audit
import VbmDecisionProofs.Message
import VbmDecisionProofs.Truth
/-! # The audit record (S6): proofs

A1 `audit-roundtrip`: `AuditRecord.ofJ r.toJ = ok r` for every valid record. Each part reads back exactly: a code by its name, a probability, a position, an answer as written (so a record of a malformed answer reads back too), the thresholds, the binding, the decision and the outcome; the question goes through the S7b round trip, which is where `Valid` is used. A2 `audit-faithful`: the record of `audit` holds the answer returned, the binding passed in and the outcome of `decide` on the same arguments. A3 `audit-total-on-refusal`: a refused decision still yields a record, and the only refusals of `audit` are an absent name. -/
namespace VbmDecision
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## A1: the parts read back -/

theorem ofName_name (c : RefusalCode) : RefusalCode.ofName c.name = some c := by
  cases c <;> decide

theorem abstain_ofName (r : AbstainReason) : AbstainReason.ofName r.name = some r := by
  cases r <;> rfl

theorem posJ_roundtrip (path : String) (x : Nat) : posOf path (Pos.toJ x) = .ok x := posOf_roundtrip path x

theorem refusal_roundtrip (path : String) (r : Refusal) : Refusal.ofJ path r.toJ = .ok r := by
  obtain ⟨c, f⟩ := r
  simp [Refusal.toJ, Refusal.ofJ, ofName_name]

theorem box_roundtrip (path : String) (b : Box) : Box.ofJ path b.toJ = .ok b := by
  obtain ⟨t, bo, l, r⟩ := b
  simp [Box.toJ, Box.ofJ, probOf_toJ, bind, Except.bind, pure, Except.pure]

theorem choice_probs_roundtrip (path : String) (ps : List (String × Prob)) :
    (ps.map fun (k, p) => (k, p.toJ)).mapM (fun (k, v) => do pure (k, ← probOf (pathKey path k) v) : String × J → Except Refusal (String × Prob))
      = .ok ps := by
  have := mapM_ok (fun (kv : String × J) => (do pure (kv.1, ← probOf (pathKey path kv.1) kv.2) : Except Refusal (String × Prob)))
    (fun kp : String × Prob => (kp.1, kp.2.toJ)) id ps
    (fun kp _ => by simp [probOf_toJ, bind, Except.bind, pure, Except.pure])
  simpa using this

theorem prob_list_roundtrip (path : String) (ps : List Prob) : (ps.map Prob.toJ).mapM (probOf path) = .ok ps := by
  have := mapM_ok (probOf path) Prob.toJ id ps (fun p _ => probOf_toJ path p)
  simpa using this

theorem str_list_roundtrip (path : String) (ls : List String) : (ls.map J.str).mapM (strOf path) = .ok ls := by
  have := mapM_ok (strOf path) J.str id ls (fun s _ => strOf_str path s)
  simpa using this

theorem answer_audit_roundtrip (path : String) (a : Answer) : Answer.ofAuditJ path a.toAuditJ = .ok a := by
  cases a with
  | noul p => simp [Answer.toAuditJ, Answer.ofAuditJ, probOf_toJ, bind, Except.bind, pure, Except.pure]
  | choice s ps c =>
    simp only [Answer.toAuditJ, Answer.ofAuditJ]
    rw [choice_probs_roundtrip]
    simp [probOf_toJ, bind, Except.bind, pure, Except.pure]
  | score x c ps lg =>
    simp only [Answer.toAuditJ, Answer.ofAuditJ]
    rw [prob_list_roundtrip, str_list_roundtrip]
    simp [Pos.toJ, posOf_roundtrip, probOf_toJ, bind, Except.bind, pure, Except.pure]
  | box b c =>
    simp [Answer.toAuditJ, Answer.ofAuditJ, box_roundtrip, probOf_toJ, bind, Except.bind, pure, Except.pure]

theorem thresholds_roundtrip (path : String) (t : Thresholds) : Thresholds.ofJ path t.toJ = .ok t := by
  cases t <;> simp [Thresholds.toJ, Thresholds.ofJ, Pos.toJ, posOf_roundtrip, probOf_toJ, bind, Except.bind, pure, Except.pure]

theorem binding_roundtrip (path : String) (b : Binding) : Binding.ofJ path b.toJ = .ok b := by
  obtain ⟨m, s, t⟩ := b
  cases s <;> simp [Binding.toJ, Binding.ofJ, thresholds_roundtrip, bind, Except.bind, pure, Except.pure]

theorem decision_roundtrip (path : String) (d : Decision) : Decision.ofJ path d.toJ = .ok d := by
  cases d <;> simp [Decision.toJ, Decision.ofJ, box_roundtrip, bind, Except.bind, pure, Except.pure]

theorem outcome_roundtrip (path : String) (o : Outcome Refusal) : Outcome.ofJ path o.toJ = .ok o := by
  cases o <;> simp [Outcome.toJ, Outcome.ofJ, decision_roundtrip, abstain_ofName, refusal_roundtrip, bind, Except.bind, pure, Except.pure]

theorem auditKeys_nodup : auditKeys.Nodup := by decide

/-- The members of a record's object, abstractly. -/
abbrev recKvs (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : J) : List (String × J) :=
  [("spec_version", a1), ("at", a2), ("requested", a3), ("snapshot", a4), ("provider", a5), ("response_id", a6),
   ("question_name", a7), ("question", a8), ("answer", a9), ("binding", a10), ("outcome", a11)]

theorem recKvs_lookup (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : J) :
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).lookup "spec_version" = some a1 ∧
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).lookup "at" = some a2 ∧
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).lookup "requested" = some a3 ∧
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).lookup "snapshot" = some a4 ∧
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).lookup "provider" = some a5 ∧
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).lookup "response_id" = some a6 ∧
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).lookup "question_name" = some a7 ∧
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).lookup "question" = some a8 ∧
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).lookup "answer" = some a9 ∧
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).lookup "binding" = some a10 ∧
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).lookup "outcome" = some a11 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem recKvs_keys (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : J) :
    (recKvs a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11).map (·.1) = auditKeys := rfl

/-- A1: a valid record reads back from its canonical `J` form. -/
theorem audit_roundtrip (r : AuditRecord) (h : r.Valid) : AuditRecord.ofJ r.toJ = .ok r := by
  obtain ⟨sv, t, rq, sn, pv, ri, qn, q, a, b, o⟩ := r
  have hq : q.Valid := h.1
  have hj : (AuditRecord.toJ ⟨sv, t, rq, sn, pv, ri, qn, q, a, b, o⟩) =
      .obj (recKvs (natJ sv) (natJ t) (.str rq) (.str sn) (.str pv) (.str ri) (.str qn) q.encode a.toAuditJ b.toJ o.toJ) := rfl
  rw [hj]
  have ho : objOf "" (some auditKeys) (.obj (recKvs (natJ sv) (natJ t) (.str rq) (.str sn) (.str pv) (.str ri) (.str qn) q.encode a.toAuditJ b.toJ o.toJ))
      = .ok (recKvs (natJ sv) (natJ t) (.str rq) (.str sn) (.str pv) (.str ri) (.str qn) q.encode a.toAuditJ b.toJ o.toJ) :=
    objOf_ok' "" (some auditKeys) _ (by rw [recKvs_keys]; exact auditKeys_nodup)
      (fun al hal k hk => by cases hal; rwa [recKvs_keys] at hk)
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := recKvs_lookup (natJ sv) (natJ t) (.str rq) (.str sn) (.str pv) (.str ri) (.str qn) q.encode a.toAuditJ b.toJ o.toJ
  have hq2 : Question.decodeAt "question" q.encode = .ok q := question_roundtrip "question" q hq
  unfold AuditRecord.ofJ
  simp only [ho, field, strField, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, natOf_natJ, strOf_str, hq2,
    answer_audit_roundtrip, binding_roundtrip, outcome_roundtrip, bind, Except.bind, pure, Except.pure]

/-! ## A2 and A3 -/

/-- A2: the record of `audit` holds the question and the answer under the name, the binding passed in, the caller's time, the strings of the request and the response, and the outcome of `decide` on the same arguments. -/
theorem audit_faithful (time : Nat) (req : Request) (resp : Response) (name : String) (b : Binding) (r : AuditRecord)
    (h : audit time req resp name b = .ok r) :
    req.questions.lookup name = some r.question ∧ resp.answers.lookup name = some r.answer ∧
    r.outcome = decide b ⟨req.model, resp.model⟩ r.question r.answer ∧ r.binding = b ∧
    r.«at» = time ∧ r.requested = req.model ∧ r.snapshot = resp.model ∧ r.provider = resp.provider ∧
    r.responseId = resp.id ∧ r.questionName = name ∧ r.specVersion = 1 := by
  unfold audit at h
  cases hq : req.questions.lookup name with
  | none => rw [hq] at h; simp [refuse] at h
  | some q =>
    cases ha : resp.answers.lookup name with
    | none => rw [hq, ha] at h; simp [refuse] at h
    | some a =>
      rw [hq, ha] at h
      simp only [Except.ok.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A3: `audit` yields a record exactly when the name is a question of the request and has an answer in the response; whatever the outcome (a refusal included). -/
theorem audit_ok_iff (time : Nat) (req : Request) (resp : Response) (name : String) (b : Binding) :
    (∃ r, audit time req resp name b = .ok r) ↔
      (∃ q, req.questions.lookup name = some q) ∧ (∃ a, resp.answers.lookup name = some a) := by
  unfold audit
  constructor
  · rintro ⟨r, hr⟩
    cases hq : req.questions.lookup name with
    | none => rw [hq] at hr; simp [refuse] at hr
    | some q =>
      cases ha : resp.answers.lookup name with
      | none => rw [hq, ha] at hr; simp [refuse] at hr
      | some a => exact ⟨⟨q, rfl⟩, ⟨a, rfl⟩⟩
  · rintro ⟨⟨q, hq⟩, ⟨a, ha⟩⟩
    rw [hq, ha]
    exact ⟨_, rfl⟩

/-- A3: a refused decision still yields a record, whose outcome is the refusal. -/
theorem audit_total_on_refusal (time : Nat) (req : Request) (resp : Response) (name : String) (b : Binding) (q : Question) (a : Answer)
    (hq : req.questions.lookup name = some q) (ha : resp.answers.lookup name = some a)
    (hr : ∃ x, decide b ⟨req.model, resp.model⟩ q a = .refused x) :
    ∃ r, audit time req resp name b = .ok r ∧ ∃ x, r.outcome = .refused x := by
  obtain ⟨x, hx⟩ := hr
  refine ⟨_, by unfold audit; rw [hq, ha], x, ?_⟩
  exact hx

/-- A3: the refusals of `audit` are the absent name, and nothing else. -/
theorem audit_error_iff (time : Nat) (req : Request) (resp : Response) (name : String) (b : Binding) (e : Refusal) :
    audit time req resp name b = .error e ↔
      (req.questions.lookup name = none ∧ e = ⟨.unexpectedAnswer, pathKey "questions" name⟩) ∨
      ((∃ q, req.questions.lookup name = some q) ∧ resp.answers.lookup name = none ∧ e = ⟨.missingAnswer, pathKey "answers" name⟩) := by
  unfold audit
  cases hq : req.questions.lookup name with
  | none =>
    constructor
    · intro h; exact .inl ⟨rfl, (Except.error.inj h).symm⟩
    · rintro (⟨_, h⟩ | ⟨⟨q, hq'⟩, _⟩)
      · rw [h]; rfl
      · cases hq'
  | some q =>
    cases ha : resp.answers.lookup name with
    | none =>
      constructor
      · intro h; exact .inr ⟨⟨q, rfl⟩, rfl, (Except.error.inj h).symm⟩
      · rintro (⟨hq', _⟩ | ⟨_, _, h⟩)
        · cases hq'
        · rw [h]; rfl
    | some a =>
      constructor
      · intro h; cases h
      · rintro (⟨hq', _⟩ | ⟨_, h, _⟩)
        · cases hq'
        · cases h

/-! ## Witnesses -/

private def p (n : Nat) (h : n ≤ 1000000 := by decide) : Prob := ⟨n, h⟩
private def qNoul : Question := .noul "Is the invoice overdue?" none
private def qBox : Question := .box "Where is the total?"
private def thr : Thresholds := .noul (p 200000) (p 900000)
private def bnd : Binding := ⟨"acme/alpha-2026", none, thr⟩
private def reqW : Request := ⟨"acme/alpha-2026", .arr [.str "The invoice is overdue."], [("overdue", qNoul), ("area", qBox)]⟩
private def respW : Response :=
  ⟨"r1", "alpha-2026-11-01", "acme-cloud",
    [("overdue", .noul (p 973100)), ("area", .box ⟨p 600000, p 200000, p 100000, p 900000⟩ (p 800000))], ⟨12, 3, ⟨false, 4, -4⟩⟩⟩

-- the hypotheses of A1 can hold: a record of each outcome constructor is valid.
private def recDecided : AuditRecord := ⟨1, 1000, "acme/alpha-2026", "alpha-2026-11-01", "acme-cloud", "r1", "overdue", qNoul, .noul (p 973100), bnd, .decided .yes⟩
private def recAbstain : AuditRecord := ⟨1, 1000, "acme/alpha-2026", "alpha-2026-11-01", "acme-cloud", "r1", "overdue", qNoul, .noul (p 500000), bnd, .abstain .uncertainBand⟩
private def recRefused : AuditRecord := ⟨1, 1000, "acme/alpha-2026", "alpha-2026-11-01", "acme-cloud", "r1", "area", qBox,
  .box ⟨p 600000, p 200000, p 100000, p 900000⟩ (p 800000), ⟨"acme/alpha-2026", some "alpha-2026-11-01", .box (p 500000)⟩, .refused ⟨.boxInverted, "box"⟩⟩
example : recDecided.Valid := ⟨trivial, .inl trivial⟩
example : recAbstain.Valid := ⟨trivial, .inl trivial⟩
example : recRefused.Valid := by unfold AuditRecord.Valid; exact ⟨trivial, .inr ⟨_, rfl⟩⟩
-- A1: each reads back from its canonical form.
example : AuditRecord.ofJ recDecided.toJ = .ok recDecided := by rfl
example : AuditRecord.ofJ recAbstain.toJ = .ok recAbstain := by rfl
example : AuditRecord.ofJ recRefused.toJ = .ok recRefused := by rfl
-- the canonical form refuses what it does not list: an extra key, a repeated key, a missing key, a code that is no code.
example : AuditRecord.ofJ (.obj [("spec_version", natJ 1), ("spec_version", natJ 1)]) = .error ⟨.duplicateKey, "spec_version"⟩ := by rfl
example : AuditRecord.ofJ (.obj [("created", .null)]) = .error ⟨.unknownField, "created"⟩ := by rfl
example : AuditRecord.ofJ (.obj []) = .error ⟨.missingField, "spec_version"⟩ := by rfl
example : AuditRecord.ofJ .null = .error ⟨.wrongKind, ""⟩ := by rfl
example : Outcome.ofJ "outcome" (.obj [("refused", .obj [("code", .str "nope"), ("field", .str "")])]) = .error ⟨.unknownType, "outcome.refused.code"⟩ := by rfl

-- A2: the record of a noul decision.
example : audit 1000 reqW respW "overdue" bnd = .ok recDecided := by rfl
example : (audit 1000 reqW respW "overdue" bnd).map (·.outcome) = .ok (.decided .yes) := by rfl
-- A3: a malformed answer (an inverted box) is recorded as refused; an absent name is the only refusal of `audit`.
example : (audit 1000 reqW respW "area" ⟨"acme/alpha-2026", none, .box (p 500000)⟩).map (·.outcome) = .ok (.refused ⟨.boxInverted, "box"⟩) := by rfl
example : audit 1000 reqW respW "nope" bnd = .error ⟨.unexpectedAnswer, "questions.nope"⟩ := by rfl
example : audit 1000 reqW ⟨"r1", "s", "p", [], ⟨1, 1, ⟨false, 0, 0⟩⟩⟩ "overdue" bnd = .error ⟨.missingAnswer, "answers.overdue"⟩ := by rfl

end VbmDecision
