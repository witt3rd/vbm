import VbmScoreboard.Journal
import VbmScoreboardProofs.Core
/-! # The journal of a change, proved

Every theorem about `VbmScoreboard.Journal`, each with a non-vacuity witness (`example`).

* `bankIfPassing_ok`, `bankIfPassing_error`, `bankIfPassing_unmeasured`: banking is refused unless every floor held; an unmeasured floor refuses it.
* `bankEntries_self`, `bankEntries_length`, `bankEntries_mem`: no change, no line; one line for each changed floor and no other; each line is a `banked` line from a floor's value to the new one.
* `addMetric_ok`, `addMetric_refuses_empty`, `addMetric_refuses_present`: a metric is added only with a name and only once, with its `added` entry.
* `startOf_unmentioned`, `progressOf_le`, `progressOf_no_target`: a floor the history never mentions starts at itself; progress is within 1000 and exists only for a metric with a target. -/
namespace VbmScoreboard

/-! ## bankIfPassing -/

theorem bankIfPassing_ok (ms : List Metric) (b : Baseline) (rs : List Reading) (b' : Baseline)
    (h : bankIfPassing ms b rs = .ok b') : passes (check b rs) = true ∧ b' = bank ms b rs := by
  unfold bankIfPassing at h
  by_cases hp : passes (check b rs) = true
  · simp [hp] at h; exact ⟨hp, h.symm⟩
  · simp [hp] at h

theorem bankIfPassing_error (ms : List Metric) (b : Baseline) (rs : List Reading) (vs : List Verdict)
    (h : bankIfPassing ms b rs = .error vs) : passes vs = false ∧ vs = check b rs := by
  unfold bankIfPassing at h
  by_cases hp : passes (check b rs) = true
  · simp [hp] at h
  · simp [hp] at h
    subst h
    simpa using hp

/-- A floor with no reading refuses banking. -/
theorem bankIfPassing_unmeasured (ms : List Metric) (b : Baseline) (rs : List Reading) (f : Floor)
    (hf : f ∈ b) (hn : lookup rs f.metric = none) : ∃ vs, bankIfPassing ms b rs = .error vs := by
  have := (check_unmeasured_fails b rs f hf hn).2
  exact ⟨check b rs, by simp [bankIfPassing, this]⟩

example : bankIfPassing [] [⟨"a", .higher, 5⟩] [⟨"a", 7⟩] = .ok [⟨"a", .higher, 7⟩] := rfl
example : bankIfPassing [] [⟨"a", .higher, 5⟩] [⟨"a", 4⟩] = .error [.regressed "a" 5 4] := rfl
example : bankIfPassing [] [⟨"a", .higher, 5⟩] [] = .error [.unmeasured "a"] := rfl
example : ∃ vs, bankIfPassing [] [⟨"a", .higher, 5⟩] [] = .error vs :=
  bankIfPassing_unmeasured [] _ _ ⟨"a", .higher, 5⟩ (by simp) rfl

/-! ## bankEntries -/

theorem bankEntries_self (t : Nat) : ∀ b : Baseline, bankEntries t b b = []
  | [] => rfl
  | f :: fs => by simp [bankEntries, bankEntries_self t fs]

/-- One line for each changed floor, none for the others. -/
theorem bankEntries_length (t : Nat) : ∀ b b' : Baseline, (bankEntries t b b').length =
    (List.zipWith (fun f g => if f.value = g.value then 0 else 1) b b').sum
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | f :: fs, g :: gs => by
    simp only [bankEntries, List.length_append, List.zipWith_cons_cons, List.sum_cons,
      bankEntries_length t fs gs]
    by_cases h : f.value = g.value <;> simp [h]

/-- Every line is a `banked` line from a floor's value to its new, different value. -/
theorem bankEntries_mem (t : Nat) : ∀ (b b' : Baseline) (e : Entry), e ∈ bankEntries t b b' →
    ∃ f ∈ b, ∃ g ∈ b', e = ⟨t, g.metric, some f.value, some g.value, .banked⟩ ∧ f.value ≠ g.value
  | [], [], e, he => by simp [bankEntries] at he
  | [], _ :: _, e, he => by simp [bankEntries] at he
  | _ :: _, [], e, he => by simp [bankEntries] at he
  | f :: fs, g :: gs, e, he => by
    simp only [bankEntries, List.mem_append] at he
    rcases he with he | he
    · by_cases h : f.value = g.value
      · simp [h] at he
      · simp [h] at he
        exact ⟨f, by simp, g, by simp, he, h⟩
    · obtain ⟨f', hf, g', hg, h1, h2⟩ := bankEntries_mem t fs gs e he
      exact ⟨f', List.mem_cons_of_mem _ hf, g', List.mem_cons_of_mem _ hg, h1, h2⟩

example : bankEntries 9 [⟨"a", .higher, 5⟩, ⟨"b", .lower, 3⟩] [⟨"a", .higher, 7⟩, ⟨"b", .lower, 3⟩] =
    [⟨9, "a", some 5, some 7, .banked⟩] := by decide +kernel
example : bankEntries 9 [⟨"a", .higher, 5⟩] [⟨"a", .higher, 5⟩] = [] := by decide +kernel

/-! ## addMetric -/

theorem addMetric_ok (b : Baseline) (m : String) (d : Direction) (v t : Nat) (b' : Baseline)
    (e : Entry) (h : addMetric b m d v t = .ok (b', e)) :
    m ≠ "" ∧ hasFloor b m = false ∧ b' = b ++ [⟨m, d, v⟩] ∧ e = ⟨t, m, none, some v, .added⟩ := by
  unfold addMetric at h
  by_cases h1 : m = ""
  · simp [h1] at h
  by_cases h2 : hasFloor b m = true
  · simp [h1, h2] at h
  · simp [h1, h2] at h
    exact ⟨h1, by simpa using h2, h.1.symm, h.2.symm⟩

theorem addMetric_refuses_empty (b : Baseline) (d : Direction) (v t : Nat) :
    addMetric b "" d v t = .error .emptyName := by simp [addMetric]

theorem addMetric_refuses_present (b : Baseline) (m : String) (d : Direction) (v t : Nat)
    (hm : m ≠ "") (h : hasFloor b m = true) : addMetric b m d v t = .error .alreadyThere := by
  simp [addMetric, hm, h]

example : addMetric [] "a" .higher 5 1 = .ok ([⟨"a", .higher, 5⟩], ⟨1, "a", none, some 5, .added⟩) := rfl
example : addMetric [⟨"a", .higher, 5⟩] "a" .lower 1 1 = .error .alreadyThere := rfl
example : addMetric [] "" .lower 1 1 = .error .emptyName := addMetric_refuses_empty _ _ _ _

/-! ## startOf and progressOf -/

theorem startOf_unmentioned (h : History) (f : Floor) (hn : ∀ e ∈ h, e.metric ≠ f.metric) :
    startOf h f = f.value := by
  have : h.find? (fun e => e.metric == f.metric) = none := by
    rw [List.find?_eq_none]; intro e he; simpa using hn e he
  simp [startOf, origin, this]

example : startOf [] ⟨"a", .higher, 5⟩ = 5 := by decide +kernel
example : startOf [⟨1, "a", none, some 3, .added⟩, ⟨2, "a", some 3, some 5, .banked⟩] ⟨"a", .higher, 5⟩ = 3 := by
  decide +kernel
example : startOf [⟨2, "a", some 3, some 5, .banked⟩] ⟨"a", .higher, 5⟩ = 3 := by decide +kernel

theorem progressOf_le (h : History) (ts : List Target) (f : Floor) (p : Nat)
    (hp : progressOf h ts f = some p) : p ≤ 1000 := by
  unfold progressOf at hp
  cases hf : ts.find? (fun t => t.metric == f.metric) with
  | none => simp [hf] at hp
  | some t =>
    simp [hf] at hp
    subst hp
    exact (progress_bounds _ _ _ _).2

theorem progressOf_no_target (h : History) (ts : List Target) (f : Floor)
    (hn : ∀ t ∈ ts, t.metric ≠ f.metric) : progressOf h ts f = none := by
  have : ts.find? (fun t => t.metric == f.metric) = none := by
    rw [List.find?_eq_none]; intro t ht; simpa using hn t ht
  simp [progressOf, this]

example : progressOf [⟨1, "a", none, some 10, .added⟩] [⟨"a", 20⟩] ⟨"a", .higher, 15⟩ = some 500 := by
  decide +kernel
example : progressOf [] [] ⟨"a", .higher, 15⟩ = none := progressOf_no_target _ _ _ (by simp)
example : progressOf [] [⟨"a", 20⟩] ⟨"a", .higher, 15⟩ = some 0 := by decide +kernel

end VbmScoreboard
