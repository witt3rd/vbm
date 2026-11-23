import VbmProb.Dist
/-! # `Dist`: the properties DS1 to DS3, each with its witness

DS1 (`make`: the atoms it keeps, each refusal in the stated order, and completeness), DS2 (extensionality) and DS3 (`point`: its atoms, support and size). The `mean` and `cdf` clauses of DS3 need the queries of a later slice and are recorded open in the ledger. -/
namespace VbmProb
namespace Dist

variable {α : Type} [Key α]

/-! ## The two scanners -/

/-- `firstWhere` finds nothing exactly when no element satisfies the test. -/
theorem firstWhere_eq_none_iff {β : Type} (p : β → Bool) :
    ∀ (l : List β) (n : Nat), firstWhere p l n = none ↔ ∀ x ∈ l, p x = false
  | [], n => by simp [firstWhere]
  | y :: ys, n => by
    unfold firstWhere
    by_cases hy : p y = true
    · simp [hy]
    · have hy' : p y = false := by simpa using hy
      simp only [hy', Bool.false_eq_true, ↓reduceIte]
      rw [firstWhere_eq_none_iff p ys (n + 1)]
      simp [hy']

/-- The scan for a key that does not exceed its predecessor finds nothing on a strictly increasing list. -/
theorem firstNotInc_of_pairwise : ∀ (l : List α) (n : Nat), l.Pairwise (· < ·) → firstNotInc l n = none
  | [], _, _ => by simp [firstNotInc]
  | [a], _, _ => by simp [firstNotInc]
  | a :: b :: rest, n, h => by
    have hp := List.pairwise_cons.mp h
    have hab : a < b := hp.1 b (by simp)
    unfold firstNotInc
    simp only [hab, ↓reduceIte]
    exact firstNotInc_of_pairwise (b :: rest) (n + 1) hp.2

/-- The scan finds nothing exactly when the keys are strictly increasing. -/
theorem firstNotInc_eq_none_iff (l : List α) (n : Nat) :
    firstNotInc l n = none ↔ l.Pairwise (· < ·) :=
  ⟨firstNotInc_none l n, firstNotInc_of_pairwise l n⟩

/-! ## DS1: `make` -/

/-- DS1: an accepted input is the distribution's atoms. -/
theorem make_atoms {lim : Limits} {atoms : List (α × Prob)} {d : Dist α}
    (h : make lim atoms = .ok d) : d.atoms = atoms := by
  unfold make at h
  repeat' split at h
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; rfl)
    | (simp at h; done)
    | skip

/-- DS1, first refusal: more atoms than the limit. -/
theorem make_tooManyAtoms {lim : Limits} {atoms : List (α × Prob)} (h : lim.maxAtoms < atoms.length) :
    make lim atoms = .error (.tooManyAtoms atoms.length lim.maxAtoms) := by
  simp [make, h]

/-- DS1, second refusal: the first atom whose probability has too many bits (its position, its bits, the limit). -/
theorem make_numberTooLarge {lim : Limits} {atoms : List (α × Prob)} {i : Nat} {a : α × Prob}
    (hn : ¬ lim.maxAtoms < atoms.length)
    (h : firstWhere (fun a => decide (lim.maxBits < a.2.val.bits)) atoms 0 = some (i, a)) :
    make lim atoms = .error (.numberTooLarge i a.2.val.bits lim.maxBits) := by
  simp [make, hn, h]

/-- DS1, third refusal: no atoms. -/
theorem make_emptyDist (lim : Limits) : make lim ([] : List (α × Prob)) = .error .emptyDist := by
  simp [make, firstWhere]

/-- The number conditions hold: no atom probability has too many bits. -/
abbrev BitsOk (lim : Limits) (atoms : List (α × Prob)) : Prop := ∀ a ∈ atoms, a.2.val.bits ≤ lim.maxBits

omit [Key α] in
theorem bits_scan_none {lim : Limits} {atoms : List (α × Prob)} (h : BitsOk lim atoms) :
    firstWhere (fun a => decide (lim.maxBits < a.2.val.bits)) atoms 0 = none :=
  (firstWhere_eq_none_iff _ _ _).mpr fun a ha => by simpa using h a ha

omit [Key α] in
theorem bits_of_scan_none {lim : Limits} {atoms : List (α × Prob)}
    (h : firstWhere (fun a => decide (lim.maxBits < a.2.val.bits)) atoms 0 = none) : BitsOk lim atoms :=
  fun a ha => by simpa using (firstWhere_eq_none_iff _ _ _).mp h a ha

/-- DS1, fourth refusal: the first position whose key is not above its predecessor's. -/
theorem make_keysNotIncreasing {lim : Limits} {atoms : List (α × Prob)} {i : Nat}
    (hn : ¬ lim.maxAtoms < atoms.length) (hb : BitsOk lim atoms)
    (h : firstNotInc (atoms.map (·.1)) 0 = some i) :
    make lim atoms = .error (.keysNotIncreasing i) := by
  have hne : atoms ≠ [] := by
    rintro rfl; simp [firstNotInc] at h
  have hnp : ¬ (atoms.map (·.1)).Pairwise (· < ·) := fun hp => by
    rw [firstNotInc_of_pairwise _ _ hp] at h; cases h
  simp [make, hn, bits_scan_none hb, hne, h, hnp]

/-- DS1, fifth refusal: the first atom of probability 0 (its position). -/
theorem make_zeroAtom {lim : Limits} {atoms : List (α × Prob)} {i : Nat} {a : α × Prob}
    (hn : ¬ lim.maxAtoms < atoms.length) (hb : BitsOk lim atoms) (hne : atoms ≠ [])
    (hk : (atoms.map (·.1)).Pairwise (· < ·))
    (h : firstWhere (fun a => !decide (0 < a.2.val)) atoms 0 = some (i, a)) :
    make lim atoms = .error (.zeroAtom i) := by
  have hnp : ¬ ∀ a ∈ atoms, 0 < a.2.val := fun hp => by
    rw [(firstWhere_eq_none_iff _ _ _).mpr fun a ha => by simp [hp a ha]] at h; cases h
  have hnc : ¬ ((atoms.map (·.1)).Pairwise (· < ·) ∧ (∀ a ∈ atoms, 0 < a.2.val) ∧ (atoms.map (·.2.val)).sum = 1) :=
    fun h => hnp h.2.1
  unfold make
  simp only [hn, ↓reduceIte, bits_scan_none hb, hne, hnc, dite_false, firstNotInc_of_pairwise _ _ hk, h]

/-- DS1, sixth refusal: the exact sum is not 1. -/
theorem make_atomSumNotOne {lim : Limits} {atoms : List (α × Prob)}
    (hn : ¬ lim.maxAtoms < atoms.length) (hb : BitsOk lim atoms) (hne : atoms ≠ [])
    (hk : (atoms.map (·.1)).Pairwise (· < ·)) (hp : ∀ a ∈ atoms, 0 < a.2.val)
    (hs : (atoms.map (·.2.val)).sum ≠ 1) :
    make lim atoms = .error (.atomSumNotOne (atoms.map (·.2.val)).sum) := by
  have hz : firstWhere (fun a => !decide (0 < a.2.val)) atoms 0 = none :=
    (firstWhere_eq_none_iff _ _ _).mpr fun a ha => by simp [hp a ha]
  have hnc : ¬ ((atoms.map (·.1)).Pairwise (· < ·) ∧ (∀ a ∈ atoms, 0 < a.2.val) ∧ (atoms.map (·.2.val)).sum = 1) :=
    fun h => hs h.2.2
  unfold make
  simp only [hn, ↓reduceIte, bits_scan_none hb, hne, hnc, dite_false, firstNotInc_of_pairwise _ _ hk, hz]

/-- DS1, completeness: if no refusal applies, `make` accepts, and the accepted input is exactly the one that
satisfies the six conditions. -/
theorem make_ok_iff (lim : Limits) (atoms : List (α × Prob)) :
    (∃ d, make lim atoms = .ok d) ↔
      ¬ lim.maxAtoms < atoms.length ∧ BitsOk lim atoms ∧ atoms ≠ [] ∧
      (atoms.map (·.1)).Pairwise (· < ·) ∧ (∀ a ∈ atoms, 0 < a.2.val) ∧ (atoms.map (·.2.val)).sum = 1 := by
  constructor
  · rintro ⟨d, h⟩
    have ha := make_atoms h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro hn; rw [make_tooManyAtoms hn] at h; simp at h
    · refine Classical.byContradiction fun hb => ?_
      have : firstWhere (fun a => decide (lim.maxBits < a.2.val.bits)) atoms 0 ≠ none :=
        fun hn => hb (bits_of_scan_none hn)
      obtain ⟨⟨i, a⟩, hs⟩ := Option.ne_none_iff_exists'.mp this
      by_cases hn : lim.maxAtoms < atoms.length
      · rw [make_tooManyAtoms hn] at h; simp at h
      · rw [make_numberTooLarge hn hs] at h; simp at h
    · rintro rfl
      rw [make_emptyDist] at h; simp at h
    · rw [← ha]; exact d.sorted
    · rw [← ha]; exact d.positive
    · rw [← ha]; exact d.total
  · rintro ⟨hn, hb, hne, hk, hp, hs⟩
    unfold make
    simp only [hn, ↓reduceIte, bits_scan_none hb, hne]
    split
    · exact ⟨_, rfl⟩
    · next hc => exact absurd ⟨hk, hp, hs⟩ hc

/-! ## DS2: extensionality -/

/-- DS2: `Dist.ext` (restated beside the properties: equal atom lists give equal distributions). -/
theorem ext_iff {a b : Dist α} : a = b ↔ a.atoms = b.atoms :=
  ⟨fun h => by rw [h], ext⟩

/-- Two accepted constructions from the same atoms are the same distribution. -/
theorem make_unique {lim lim' : Limits} {atoms : List (α × Prob)} {d d' : Dist α}
    (h : make lim atoms = .ok d) (h' : make lim' atoms = .ok d') : d = d' :=
  ext ((make_atoms h).trans (make_atoms h').symm)

/-! ## DS3: `point` -/

/-- DS3: `point a` has the one atom `(a, 1)`. -/
theorem point_atoms (a : α) : (point a).atoms = [(a, Prob.one)] := rfl

/-- DS3: the support of `point a` is `[a]`. -/
theorem point_support (a : α) : (point a).support = [a] := rfl

/-- DS3: `point a` has one atom. -/
theorem point_size (a : α) : (point a).size = 1 := rfl

/-- A distribution has at least one atom (the total is 1, the empty sum is 0). -/
theorem size_pos (d : Dist α) : 0 < d.size := by
  unfold size
  cases h : d.atoms with
  | nil => have := d.total; rw [h] at this; revert this; simp
  | cons x xs => simp

/-- `make` of the single atom `(a, 1)` is `point a`. -/
theorem make_point {lim : Limits} {a : α} {d : Dist α} (h : make lim [(a, Prob.one)] = .ok d) : d = point a :=
  ext (make_atoms h)

/-! ## Non-vacuity witnesses -/

/-- A literal probability, its bounds decided. -/
def pr (q : Rat) (h0 : 0 ≤ q := by decide +kernel) (h1 : q ≤ 1 := by decide +kernel) : Prob := ⟨q, h0, h1⟩

-- DS1: the atoms 1/4, 1/2, 1/4 at keys 100, 200, 300 are accepted.
example : ∃ d : Dist Int, make Limits.default [(100, pr (1/4)), (200, pr (1/2)), (300, pr (1/4))] = .ok d ∧
    d.atoms = [(100, pr (1/4)), (200, pr (1/2)), (300, pr (1/4))] := by
  obtain ⟨d, hd⟩ := (make_ok_iff Limits.default [((100 : Int), pr (1/4)), (200, pr (1/2)), (300, pr (1/4))]).mpr
    ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  exact ⟨d, hd, make_atoms hd⟩

-- DS1: one case per refusal.
example : make { Limits.default with maxAtoms := 2 } [((100 : Int), pr (1/4)), (200, pr (1/2)), (300, pr (1/4))] =
    .error (.tooManyAtoms 3 2) := make_tooManyAtoms (by decide +kernel)
example : make { Limits.default with maxBits := 4 } [((1 : Int), pr (1/2)), (2, pr (1/1000))] =
    .error (.numberTooLarge 1 11 4) := by
  have := 
make_numberTooLarge (lim := { Limits.default with maxBits := 4 }) (atoms := [((1 : Int), pr (1/2)), (2, pr (1/1000))]) (i := 1) (a := ((2 : Int), pr (1/1000)))
    (by decide +kernel) (by
      have h1 : (pr (1/2)).val.bits = 3 := by decide +kernel
      have h2 : (pr (1/1000)).val.bits = 11 := by decide +kernel
      simp [firstWhere, h1, h2])
  rw [this]; have h2 : (pr (1/1000)).val.bits = 11 := by decide +kernel
  simp [h2]
example : make Limits.default ([] : List (Int × Prob)) = .error .emptyDist := make_emptyDist _
example : make Limits.default [((1 : Int), pr (1/2)), (1, pr (1/2))] = .error (.keysNotIncreasing 1) :=
  make_keysNotIncreasing (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : make Limits.default [((2 : Int), pr (1/2)), (1, pr (1/2))] = .error (.keysNotIncreasing 1) :=
  make_keysNotIncreasing (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : make Limits.default [((1 : Int), pr 0), (2, pr 1)] = .error (.zeroAtom 0) :=
  make_zeroAtom (atoms := [((1 : Int), pr 0), (2, pr 1)]) (i := 0) (a := ((1 : Int), pr 0)) (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)
    (by simp [firstWhere, pr])
example : make Limits.default [((1 : Int), pr (1/2))] = .error (.atomSumNotOne (1/2)) := by
  have := make_atomSumNotOne (lim := Limits.default) (atoms := [((1 : Int), pr (1/2))])
    (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [this]; simp [pr]; decide +kernel

-- DS2: two constructions of the same atoms are equal; `make` of `(7, 1)` is `point 7`.
example : (⟨[((7 : Int), Prob.one)], (point 7).sorted, (point 7).positive, (point 7).total⟩ : Dist Int) = point 7 :=
  ext rfl
example (d : Dist Int) (h : make Limits.default [((7 : Int), Prob.one)] = .ok d) : d = point 7 := make_point h

-- DS3: `point 7` over `Int`.
example : (point (7 : Int)).atoms = [(7, Prob.one)] ∧ (point (7 : Int)).size = 1 := ⟨rfl, rfl⟩

end Dist
end VbmProb
