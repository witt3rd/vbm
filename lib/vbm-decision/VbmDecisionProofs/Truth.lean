import VbmDecision.Truth
import VbmDecisionProofs.Check
/-! # The threshold truth table (S4): proofs

T2 `decide-total`, T3 `fail-closed`, T4 `noul-characterised`, T5 `one-decision`, T6 `noul-monotone`, T7 `score-monotone`, T8 `threshold-monotone`, T9 `choice-characterised`. The gate (rules 1 to 3) succeeds iff the four conditions hold; `decide` is then the table, and each row is characterised by `simp` on its guards. -/
namespace VbmDecision

/-! ## The gate -/

theorem gate_ok_iff (b : Binding) (c : Context) (q : Question) (a : Answer) :
    gate b c q a = .ok () ↔ q.Valid ∧ WellFormed q a ∧ BindingOk b c ∧ q.ThresholdsValid b.thresholds := by
  rw [← question_check_ok_iff, ← checkAnswer_ok_iff, ← checkThresholds_ok_iff]
  unfold gate BindingOk
  cases h1 : q.check with
  | error r => simp
  | ok u =>
    cases u
    cases h2 : checkAnswer q a with
    | error r => simp
    | ok u =>
      cases u
      simp [guardWith_ok, and_assoc]

/-- Past the gate, `decide` is the table. -/
theorem decide_of_gate {b : Binding} {c : Context} {q : Question} {a : Answer} (h : gate b c q a = .ok ()) :
    decide b c q a = table b.thresholds a := by
  unfold decide; rw [h]

/-- The conditions of the gate, bundled. -/
def Good (b : Binding) (c : Context) (q : Question) (a : Answer) : Prop :=
  q.Valid ∧ WellFormed q a ∧ BindingOk b c ∧ q.ThresholdsValid b.thresholds

theorem decide_of_good {b : Binding} {c : Context} {q : Question} {a : Answer} (h : Good b c q a) :
    decide b c q a = table b.thresholds a :=
  decide_of_gate ((gate_ok_iff b c q a).2 h)

/-! ## T2: totality -/

/-- T2: `decide` returns an outcome, and it is of exactly one of the three kinds. -/
theorem decide_total (b : Binding) (c : Context) (q : Question) (a : Answer) :
    ∃ o, decide b c q a = o ∧
      ((∃ d, o = .decided d) ∨ (∃ r, o = .abstain r) ∨ (∃ r, o = .refused r)) := by
  refine ⟨decide b c q a, rfl, ?_⟩
  cases h : decide b c q a with
  | decided d => exact .inl ⟨d, rfl⟩
  | abstain r => exact .inr (.inl ⟨r, rfl⟩)
  | refused r => exact .inr (.inr ⟨r, rfl⟩)

/-- T2, exclusivity: no outcome is of two kinds. -/
theorem outcome_exclusive (o : Outcome Refusal) :
    (∀ d r, ¬ (o = .decided d ∧ o = .abstain r)) ∧ (∀ d r, ¬ (o = .decided d ∧ o = .refused r)) ∧
      (∀ r r', ¬ (o = .abstain r ∧ o = .refused r')) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro _ _ ⟨h1, h2⟩ <;> rw [h1] at h2 <;> cases h2

/-! ## T3: fail closed -/

/-- T3: the answer is not well formed for the question: refused (whatever the binding and the context). -/
theorem fail_closed_answer (b : Binding) (c : Context) (q : Question) (a : Answer) (h : ¬ WellFormed q a) :
    ∃ r, decide b c q a = .refused r := by
  have : gate b c q a ≠ .ok () := fun hg => h ((gate_ok_iff b c q a).1 hg).2.1
  unfold decide
  cases hg : gate b c q a with
  | error r => exact ⟨r, rfl⟩
  | ok u => cases u; exact absurd hg this

/-- T3: the question is not valid: refused. -/
theorem fail_closed_question (b : Binding) (c : Context) (q : Question) (a : Answer) (h : ¬ q.Valid) :
    ∃ r, decide b c q a = .refused r := by
  have : gate b c q a ≠ .ok () := fun hg => h ((gate_ok_iff b c q a).1 hg).1
  unfold decide
  cases hg : gate b c q a with
  | error r => exact ⟨r, rfl⟩
  | ok u => cases u; exact absurd hg this

/-- T3: the thresholds are not valid for the question: refused. -/
theorem fail_closed_thresholds (b : Binding) (c : Context) (q : Question) (a : Answer) (h : ¬ q.ThresholdsValid b.thresholds) :
    ∃ r, decide b c q a = .refused r := by
  have : gate b c q a ≠ .ok () := fun hg => h ((gate_ok_iff b c q a).1 hg).2.2.2
  unfold decide
  cases hg : gate b c q a with
  | error r => exact ⟨r, rfl⟩
  | ok u => cases u; exact absurd hg this

/-- T3: a binding of another model or another snapshot: refused. -/
theorem fail_closed_binding (b : Binding) (c : Context) (q : Question) (a : Answer) (h : ¬ BindingOk b c) :
    ∃ r, decide b c q a = .refused r := by
  have : gate b c q a ≠ .ok () := fun hg => h ((gate_ok_iff b c q a).1 hg).2.2.1
  unfold decide
  cases hg : gate b c q a with
  | error r => exact ⟨r, rfl⟩
  | ok u => cases u; exact absurd hg this

/-- T3, the model mismatch refusal is named. -/
theorem decide_modelMismatch (b : Binding) (c : Context) (q : Question) (a : Answer)
    (hq : q.Valid) (ha : WellFormed q a) (h : b.model ≠ c.requested) :
    decide b c q a = .refused ⟨.modelMismatch, "model"⟩ := by
  have h1 := (question_check_ok_iff q).2 hq
  have h2 := (checkAnswer_ok_iff q a).2 ha
  simp [decide, gate, h1, h2, guardWith, h]

/-- T3, the snapshot mismatch refusal is named. -/
theorem decide_snapshotMismatch (b : Binding) (c : Context) (q : Question) (a : Answer)
    (hq : q.Valid) (ha : WellFormed q a) (hm : b.model = c.requested) (s : String) (hs : b.snapshot = some s) (h : s ≠ c.snapshot) :
    decide b c q a = .refused ⟨.snapshotMismatch, "snapshot"⟩ := by
  have h1 := (question_check_ok_iff q).2 hq
  have h2 := (checkAnswer_ok_iff q a).2 ha
  simp [decide, gate, h1, h2, guardWith, hm, hs, h]

/-! ## The rows of the table -/

/-- The noul row, past the gate. -/
theorem decide_noul (b : Binding) (c : Context) (i : String) (cr : Option (String × String)) (no yes p : Prob)
    (hb : BindingOk b c) (ht : b.thresholds = .noul no yes) (hv : no.val < yes.val) :
    decide b c (.noul i cr) (.noul p) =
      if yes.val ≤ p.val then .decided .yes else if p.val ≤ no.val then .decided .no else .abstain .uncertainBand := by
  have hg : Good b c (.noul i cr) (.noul p) := by
    refine ⟨trivial, trivial, hb, ?_⟩
    rw [ht]; exact hv
  rw [decide_of_good hg, ht]; rfl

/-- T4: for valid noul thresholds, `yes` exactly when `yes ≤ p`. -/
theorem noul_yes_iff (b : Binding) (c : Context) (i : String) (cr : Option (String × String)) (no yes p : Prob)
    (hb : BindingOk b c) (ht : b.thresholds = .noul no yes) (hv : no.val < yes.val) :
    decide b c (.noul i cr) (.noul p) = .decided .yes ↔ yes.val ≤ p.val := by
  rw [decide_noul b c i cr no yes p hb ht hv]
  by_cases h1 : yes.val ≤ p.val <;> by_cases h2 : p.val ≤ no.val <;> simp [h1, h2] <;> omega

/-- T4: `no` exactly when `p ≤ no`. -/
theorem noul_no_iff (b : Binding) (c : Context) (i : String) (cr : Option (String × String)) (no yes p : Prob)
    (hb : BindingOk b c) (ht : b.thresholds = .noul no yes) (hv : no.val < yes.val) :
    decide b c (.noul i cr) (.noul p) = .decided .no ↔ p.val ≤ no.val := by
  rw [decide_noul b c i cr no yes p hb ht hv]
  by_cases h1 : yes.val ≤ p.val <;> by_cases h2 : p.val ≤ no.val <;> simp [h1, h2] <;> omega

/-- T4: an abstention on the uncertain band exactly when `no < p < yes`. -/
theorem noul_band_iff (b : Binding) (c : Context) (i : String) (cr : Option (String × String)) (no yes p : Prob)
    (hb : BindingOk b c) (ht : b.thresholds = .noul no yes) (hv : no.val < yes.val) :
    decide b c (.noul i cr) (.noul p) = .abstain .uncertainBand ↔ no.val < p.val ∧ p.val < yes.val := by
  rw [decide_noul b c i cr no yes p hb ht hv]
  by_cases h1 : yes.val ≤ p.val <;> by_cases h2 : p.val ≤ no.val <;> simp [h1, h2] <;> omega

/-- T5: the yes condition and the no condition never hold together. -/
theorem noul_no_overlap (no yes p : Prob) (hv : no.val < yes.val) : ¬ (yes.val ≤ p.val ∧ p.val ≤ no.val) := by
  omega

/-- T5: no noul input gets two decisions. -/
theorem noul_one_decision (b : Binding) (c : Context) (i : String) (cr : Option (String × String)) (no yes p : Prob)
    (hb : BindingOk b c) (ht : b.thresholds = .noul no yes) (hv : no.val < yes.val) :
    ¬ (decide b c (.noul i cr) (.noul p) = .decided .yes ∧ decide b c (.noul i cr) (.noul p) = .decided .no) := by
  intro ⟨h1, h2⟩
  rw [noul_yes_iff b c i cr no yes p hb ht hv] at h1
  rw [noul_no_iff b c i cr no yes p hb ht hv] at h2
  omega

/-- T6: raising the probability of yes keeps a `yes`. -/
theorem noul_monotone_yes (b : Binding) (c : Context) (i : String) (cr : Option (String × String)) (no yes p p' : Prob)
    (hb : BindingOk b c) (ht : b.thresholds = .noul no yes) (hv : no.val < yes.val) (hle : p.val ≤ p'.val)
    (h : decide b c (.noul i cr) (.noul p) = .decided .yes) :
    decide b c (.noul i cr) (.noul p') = .decided .yes := by
  rw [noul_yes_iff b c i cr no yes p hb ht hv] at h
  rw [noul_yes_iff b c i cr no yes p' hb ht hv]; omega

/-- T6: and a `no` at the higher probability was a `no` at the lower. -/
theorem noul_monotone_no (b : Binding) (c : Context) (i : String) (cr : Option (String × String)) (no yes p p' : Prob)
    (hb : BindingOk b c) (ht : b.thresholds = .noul no yes) (hv : no.val < yes.val) (hle : p.val ≤ p'.val)
    (h : decide b c (.noul i cr) (.noul p') = .decided .no) :
    decide b c (.noul i cr) (.noul p) = .decided .no := by
  rw [noul_no_iff b c i cr no yes p' hb ht hv] at h
  rw [noul_no_iff b c i cr no yes p hb ht hv]; omega

/-- T8: lowering the yes threshold (keeping `no` below it) keeps a `yes`. -/
theorem threshold_monotone (b b' : Binding) (c : Context) (i : String) (cr : Option (String × String)) (no yes yes' p : Prob)
    (hb : BindingOk b c) (hb' : BindingOk b' c) (ht : b.thresholds = .noul no yes) (ht' : b'.thresholds = .noul no yes')
    (hv : no.val < yes.val) (hv' : no.val < yes'.val) (hle : yes'.val ≤ yes.val)
    (h : decide b c (.noul i cr) (.noul p) = .decided .yes) :
    decide b' c (.noul i cr) (.noul p) = .decided .yes := by
  rw [noul_yes_iff b c i cr no yes p hb ht hv] at h
  rw [noul_yes_iff b' c i cr no yes' p hb' ht' hv']; omega

/-! ## The score row -/

/-- The score row, past the gate. -/
theorem decide_score (b : Binding) (c : Context) (i : String) (ls : List String) (x : Pos) (conf : Prob) (ps : List Prob) (lg : List String)
    (lo hi : Pos) (mc : Prob) (hq : (Question.score i ls).Valid) (ha : WellFormed (.score i ls) (.score x conf ps lg))
    (hb : BindingOk b c) (ht : b.thresholds = .score lo hi mc) (hv : lo ≤ hi ∧ hi ≤ (ls.length - 1) * scale) :
    decide b c (.score i ls) (.score x conf ps lg) =
      if conf.val < mc.val then .abstain .lowConfidence
      else if x < lo then .decided .below else if hi < x then .decided .above else .decided .within := by
  have hg : Good b c (.score i ls) (.score x conf ps lg) := by
    refine ⟨hq, ha, hb, ?_⟩
    rw [ht]; exact hv
  rw [decide_of_good hg, ht]; rfl

/-- T7: a larger position keeps `above`. -/
theorem score_monotone_above (b : Binding) (c : Context) (i : String) (ls : List String) (x x' : Pos) (conf : Prob) (ps : List Prob) (lg : List String)
    (lo hi : Pos) (mc : Prob) (hq : (Question.score i ls).Valid) (ha : WellFormed (.score i ls) (.score x conf ps lg))
    (ha' : WellFormed (.score i ls) (.score x' conf ps lg))
    (hb : BindingOk b c) (ht : b.thresholds = .score lo hi mc) (hv : lo ≤ hi ∧ hi ≤ (ls.length - 1) * scale) (hle : x ≤ x')
    (h : decide b c (.score i ls) (.score x conf ps lg) = .decided .above) :
    decide b c (.score i ls) (.score x' conf ps lg) = .decided .above := by
  rw [decide_score b c i ls x conf ps lg lo hi mc hq ha hb ht hv] at h
  rw [decide_score b c i ls x' conf ps lg lo hi mc hq ha' hb ht hv]
  by_cases h1 : conf.val < mc.val
  · simp [h1] at h
  · by_cases h2 : x < lo <;> by_cases h3 : hi < x <;> by_cases h4 : x' < lo <;>
      by_cases h5 : hi < x' <;> simp [h1, h2, h3, h4, h5] at h ⊢ <;> (unfold Pos at *; omega)

/-- T7: a smaller position keeps `below`. -/
theorem score_monotone_below (b : Binding) (c : Context) (i : String) (ls : List String) (x x' : Pos) (conf : Prob) (ps : List Prob) (lg : List String)
    (lo hi : Pos) (mc : Prob) (hq : (Question.score i ls).Valid) (ha : WellFormed (.score i ls) (.score x conf ps lg))
    (ha' : WellFormed (.score i ls) (.score x' conf ps lg))
    (hb : BindingOk b c) (ht : b.thresholds = .score lo hi mc) (hv : lo ≤ hi ∧ hi ≤ (ls.length - 1) * scale) (hle : x ≤ x')
    (h : decide b c (.score i ls) (.score x' conf ps lg) = .decided .below) :
    decide b c (.score i ls) (.score x conf ps lg) = .decided .below := by
  rw [decide_score b c i ls x' conf ps lg lo hi mc hq ha' hb ht hv] at h
  rw [decide_score b c i ls x conf ps lg lo hi mc hq ha hb ht hv]
  by_cases h1 : conf.val < mc.val
  · simp [h1] at h
  · by_cases h2 : x < lo <;> by_cases h3 : hi < x <;> by_cases h4 : x' < lo <;>
      by_cases h5 : hi < x' <;> simp [h1, h2, h3, h4, h5] at h ⊢ <;> (unfold Pos at *; omega)

/-! ## The choice row -/

/-- A listed key has a probability. -/
theorem selProb_isSome (sel : String) (ps : List (String × Prob)) (h : ∃ p ∈ ps, p.1 = sel) : ∃ v, selProb sel ps = some v := by
  induction ps with
  | nil => obtain ⟨p, hp, _⟩ := h; cases hp
  | cons e es ih =>
    unfold selProb
    by_cases he : e.1 = sel
    · exact ⟨e.2, by simp [he]⟩
    · simp only [he, ite_false]
      obtain ⟨p, hp, hps⟩ := h
      rcases List.mem_cons.1 hp with rfl | hp
      · exact absurd hps he
      · exact ih ⟨p, hp, hps⟩

/-- With distinct keys the selected option's probability is the maximal one. -/
theorem selProb_max (sel : String) (ps : List (String × Prob)) (hn : (ps.map (·.1)).Nodup)
    (h : ∃ p ∈ ps, p.1 = sel ∧ ∀ r ∈ ps, r.2.val ≤ p.2.val) :
    ∃ v, selProb sel ps = some v ∧ ∀ r ∈ ps, r.2.val ≤ v.val := by
  induction ps with
  | nil => obtain ⟨p, hp, _⟩ := h; cases hp
  | cons e es ih =>
    obtain ⟨p, hp, hps, hmax⟩ := h
    have hn' := List.nodup_cons.1 hn
    unfold selProb
    by_cases he : e.1 = sel
    · have hpe : p = e := by
        rcases List.mem_cons.1 hp with rfl | hp
        · rfl
        · exact absurd (List.mem_map_of_mem (f := (·.1)) hp) (by rw [hps, ← he]; exact hn'.1)
      subst hpe
      exact ⟨p.2, by simp [he], hmax⟩
    · have hpes : p ∈ es := by
        rcases List.mem_cons.1 hp with rfl | hp
        · exact absurd hps he
        · exact hp
      obtain ⟨v, hv, hvm⟩ := ih hn'.2 ⟨p, hpes, hps, fun r hr => hmax r (List.mem_cons_of_mem _ hr)⟩
      refine ⟨v, by simp [he, hv], fun r hr => ?_⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · have := hmax r (List.mem_cons_self ..)
        have hpv : p.2.val ≤ v.val := hvm p hpes
        omega
      · exact hvm r hr

/-- The runner-up is at most the selected probability. -/
theorem runnerUp_le (sel : String) (ps : List (String × Prob)) (v : Nat) (h : ∀ r ∈ ps, r.2.val ≤ v) : runnerUp sel ps ≤ v := by
  induction ps with
  | nil => simp [runnerUp]
  | cons e es ih =>
    unfold runnerUp
    have h1 := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    have h2 := h e (List.mem_cons_self ..)
    split <;> simp_all <;> omega

/-- The choice row, past the gate: the selected probability `v`, and the runner-up. -/
theorem decide_choice (b : Binding) (c : Context) (i : String) (os : List (String × Option String)) (sel : String)
    (ps : List (String × Prob)) (conf mp mm : Prob)
    (hq : (Question.choice i os).Valid) (ha : WellFormed (.choice i os) (.choice sel ps conf))
    (hb : BindingOk b c) (ht : b.thresholds = .choice mp mm) :
    ∃ v, selProb sel ps = some v ∧ runnerUp sel ps ≤ v.val ∧
      decide b c (.choice i os) (.choice sel ps conf) =
        (if v.val < mp.val then .abstain .lowProbability
         else if v.val - runnerUp sel ps < mm.val then .abstain .lowMargin
         else .decided (.option sel)) := by
  have hg : Good b c (.choice i os) (.choice sel ps conf) := by
    refine ⟨hq, ha, hb, ?_⟩
    rw [ht]; trivial
  obtain ⟨hn, -, -, -, -, hex⟩ := ha
  obtain ⟨v, hv, hvm⟩ := selProb_max sel ps hn hex
  refine ⟨v, hv, runnerUp_le sel ps v.val hvm, ?_⟩
  rw [decide_of_good hg, ht]
  simp [table, choiceTable, hv]

/-- T9: the option is decided iff both bars are cleared. -/
theorem choice_decided_iff (b : Binding) (c : Context) (i : String) (os : List (String × Option String)) (sel : String)
    (ps : List (String × Prob)) (conf mp mm v : Prob)
    (hq : (Question.choice i os).Valid) (ha : WellFormed (.choice i os) (.choice sel ps conf))
    (hb : BindingOk b c) (ht : b.thresholds = .choice mp mm) (hv : selProb sel ps = some v) :
    decide b c (.choice i os) (.choice sel ps conf) = .decided (.option sel) ↔
      mp.val ≤ v.val ∧ mm.val ≤ v.val - runnerUp sel ps := by
  obtain ⟨w, hw, -, he⟩ := decide_choice b c i os sel ps conf mp mm hq ha hb ht
  rw [hv] at hw; cases hw
  rw [he]
  by_cases h1 : v.val < mp.val <;> by_cases h2 : v.val - runnerUp sel ps < mm.val <;> simp [h1, h2] <;> omega

/-- T9: below `minProb`, the abstention is on probability. -/
theorem choice_lowProbability_iff (b : Binding) (c : Context) (i : String) (os : List (String × Option String)) (sel : String)
    (ps : List (String × Prob)) (conf mp mm v : Prob)
    (hq : (Question.choice i os).Valid) (ha : WellFormed (.choice i os) (.choice sel ps conf))
    (hb : BindingOk b c) (ht : b.thresholds = .choice mp mm) (hv : selProb sel ps = some v) :
    decide b c (.choice i os) (.choice sel ps conf) = .abstain .lowProbability ↔ v.val < mp.val := by
  obtain ⟨w, hw, -, he⟩ := decide_choice b c i os sel ps conf mp mm hq ha hb ht
  rw [hv] at hw; cases hw
  rw [he]
  by_cases h1 : v.val < mp.val <;> by_cases h2 : v.val - runnerUp sel ps < mm.val <;> simp [h1, h2] <;> omega

/-- T9: past `minProb` and below `minMargin`, the abstention is on margin. -/
theorem choice_lowMargin_iff (b : Binding) (c : Context) (i : String) (os : List (String × Option String)) (sel : String)
    (ps : List (String × Prob)) (conf mp mm v : Prob)
    (hq : (Question.choice i os).Valid) (ha : WellFormed (.choice i os) (.choice sel ps conf))
    (hb : BindingOk b c) (ht : b.thresholds = .choice mp mm) (hv : selProb sel ps = some v) :
    decide b c (.choice i os) (.choice sel ps conf) = .abstain .lowMargin ↔
      mp.val ≤ v.val ∧ v.val - runnerUp sel ps < mm.val := by
  obtain ⟨w, hw, -, he⟩ := decide_choice b c i os sel ps conf mp mm hq ha hb ht
  rw [hv] at hw; cases hw
  rw [he]
  by_cases h1 : v.val < mp.val <;> by_cases h2 : v.val - runnerUp sel ps < mm.val <;> simp [h1, h2] <;> omega

/-- T5: a choice decision names exactly the selected option. -/
theorem choice_decision_is_selected (b : Binding) (c : Context) (i : String) (os : List (String × Option String)) (sel : String)
    (ps : List (String × Prob)) (conf mp mm : Prob) (d : Decision)
    (hq : (Question.choice i os).Valid) (ha : WellFormed (.choice i os) (.choice sel ps conf))
    (hb : BindingOk b c) (ht : b.thresholds = .choice mp mm)
    (h : decide b c (.choice i os) (.choice sel ps conf) = .decided d) : d = .option sel := by
  obtain ⟨w, -, -, he⟩ := decide_choice b c i os sel ps conf mp mm hq ha hb ht
  rw [he] at h
  split at h
  · cases h
  · split at h <;> simp_all

/-! ## Witnesses -/

/-- A probability literal, clamped to one (only small literals are used). -/
private def p (n : Nat) : Prob := ⟨min n 1000000, Nat.min_le_right ..⟩

private def qn : Question := .noul "i" none
private def bn (no yes : Nat) : Binding :=
  ⟨"acme/alpha", some "alpha-1", .noul (p no) (p yes)⟩
private def cx : Context := ⟨"acme/alpha", "alpha-1"⟩

-- T2: each constructor of the outcome is returned.
example : decide (bn 300000 800000) cx qn (.noul (p 900000)) = .decided .yes := by decide +kernel
example : decide (bn 300000 800000) cx qn (.noul (p 500000)) = .abstain .uncertainBand := by decide +kernel
example : decide (bn 300000 800000) cx qn (.noul (p 900000)) ≠ .refused ⟨.modelMismatch, "model"⟩ := by decide +kernel
example : decide (bn 300000 800000) ⟨"acme/beta", "alpha-1"⟩ qn (.noul (p 900000)) = .refused ⟨.modelMismatch, "model"⟩ := by decide +kernel

-- T3: one malformed example per rule 1 to 3.
example : decide (bn 300000 800000) cx qn (.box ⟨p 0, p 1, p 0, p 1⟩ (p 0)) = .refused ⟨.typeMismatch, ""⟩ := by decide +kernel
example : decide (bn 300000 800000) cx (.choice "t" [("a", none)]) (.noul (p 0)) = .refused ⟨.tooFewOptions, "criteria"⟩ := by decide +kernel
example : decide (bn 300000 800000) ⟨"acme/alpha", "alpha-2"⟩ qn (.noul (p 900000)) = .refused ⟨.snapshotMismatch, "snapshot"⟩ := by decide +kernel
example : decide (bn 800000 800000) cx qn (.noul (p 900000)) = .refused ⟨.badThresholds, "thresholds"⟩ := by decide +kernel
example : decide ⟨"acme/alpha", none, .box (p 0)⟩ cx qn (.noul (p 900000)) = .refused ⟨.thresholdKind, "thresholds"⟩ := by decide +kernel

-- T4: no = 300000, yes = 800000.
example : decide (bn 300000 800000) cx qn (.noul (p 300000)) = .decided .no := by decide +kernel
example : decide (bn 300000 800000) cx qn (.noul (p 300001)) = .abstain .uncertainBand := by decide +kernel
example : decide (bn 300000 800000) cx qn (.noul (p 799999)) = .abstain .uncertainBand := by decide +kernel
example : decide (bn 300000 800000) cx qn (.noul (p 800000)) = .decided .yes := by decide +kernel
-- T5: an empty band, no + 1 = yes: no overlap, and both sides decide.
example : decide (bn 300000 300001) cx qn (.noul (p 300000)) = .decided .no := by decide +kernel
example : decide (bn 300000 300001) cx qn (.noul (p 300001)) = .decided .yes := by decide +kernel
-- T6: 800000 ≤ 900000, both yes.
example : decide (bn 300000 800000) cx qn (.noul (p 800000)) = .decided .yes ∧
    decide (bn 300000 800000) cx qn (.noul (p 900000)) = .decided .yes := by decide +kernel
-- T8: the yes threshold 800000 lowered to 700000.
example : decide (bn 300000 800000) cx qn (.noul (p 800000)) = .decided .yes ∧
    decide (bn 300000 700000) cx qn (.noul (p 800000)) = .decided .yes := by decide +kernel

-- T7: three levels, range [1.0, 2.0].
private def qs : Question := .score "u" ["none", "some", "high"]
private def bs : Binding := ⟨"acme/alpha", none, .score 1000000 2000000 (p 500000)⟩
private def sa (x : Nat) : Answer := .score x (p 700000) [p 0, p 500000, p 500000] ["none", "some", "high"]
example : decide bs cx qs (sa 100000) = .refused ⟨.scoreInconsistent, "score"⟩ := by decide +kernel
example : decide bs cx qs (sa 1500000) = .decided .within := by decide +kernel
example : decide bs cx qs (sa 1500000) ≠ .decided .above := by decide +kernel
example : decide bs cx qs (.score 1500000 (p 400000) [p 0, p 500000, p 500000] ["none", "some", "high"]) = .abstain .lowConfidence := by decide +kernel
example : decide ⟨"acme/alpha", none, .score 1000000 1400000 (p 500000)⟩ cx qs (sa 1500000) = .decided .above ∧
    decide ⟨"acme/alpha", none, .score 1600000 1800000 (p 500000)⟩ cx qs (sa 1500000) = .decided .below := by decide +kernel
-- the premises of T7 hold: both answers well formed, the thresholds valid.
example : WellFormed qs (sa 1500000) ∧ WellFormed qs (sa 1500300) ∧ qs.ThresholdsValid bs.thresholds ∧ BindingOk bs cx := by decide +kernel

-- T9: three options (0.6, 0.3, 0.1), minProb 0.5, minMargin 0.2 and 0.4.
private def qc : Question := .choice "t" [("a", none), ("b", none), ("c", none)]
private def ac : Answer := .choice "a" [("a", p 600000), ("b", p 300000), ("c", p 100000)] (p 600000)
private def bc (mm : Nat) : Binding := ⟨"acme/alpha", none, .choice (p 500000) (p mm)⟩
example : decide (bc 200000) cx qc ac = .decided (.option "a") := by decide +kernel
example : decide (bc 400000) cx qc ac = .abstain .lowMargin := by decide +kernel
example : decide ⟨"acme/alpha", none, .choice (p 700000) (p 0)⟩ cx qc ac = .abstain .lowProbability := by decide +kernel
example : selProb "a" [("a", p 600000), ("b", p 300000), ("c", p 100000)] = some (p 600000) := by decide +kernel
example : runnerUp "a" [("a", p 600000), ("b", p 300000), ("c", p 100000)] = 300000 := by decide +kernel
example : WellFormed qc ac ∧ qc.Valid ∧ BindingOk (bc 200000) cx := by decide +kernel

end VbmDecision
