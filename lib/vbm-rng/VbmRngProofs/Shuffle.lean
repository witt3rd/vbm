import VbmRng.Shuffle
import VbmRngProofs.Below
/-! # The shuffle's proofs (S7): S1-S4 and the shuffle vectors

S1: every swap is a permutation, so the result is a permutation of the input. S2: the loop never looks at an element, so it commutes with `map`. S3: each draw consumes between one and `fuel` words and there is one per position `L - 1, ..., 1`. S4: a refusing draw is the result. The uniformity of the permutation (S5) is not claimed here. -/
namespace VbmRng

theorem swapIfInBounds_perm {α : Type} (a : Array α) (i j : Nat) : Array.Perm (a.swapIfInBounds i j) a := by
  rw [Array.swapIfInBounds_def]
  split
  · split
    · exact Array.swap_perm _ _
    · exact Array.Perm.refl _
  · exact Array.Perm.refl _

theorem shuffleGo_perm {α : Type} (fuel : Nat) : ∀ (i : Nat) (a : Array α) (st : Stream) (b : Array α) (st' : Stream),
    shuffleGo fuel i a st = .ok (b, st') → Array.Perm b a
  | 0, a, st, b, st', h => by
    simp only [shuffleGo, Except.ok.injEq, Prod.mk.injEq] at h
    exact Array.Perm.of_eq h.1.symm
  | i + 1, a, st, b, st', h => by
    unfold shuffleGo at h
    cases hd : uniformBelowWith fuel (i + 2) st with
    | error e => rw [hd] at h; simp at h
    | ok r =>
      rw [hd] at h
      exact (shuffleGo_perm fuel i _ r.2 b st' h).trans (swapIfInBounds_perm a _ _)

/-- **S1 (permutation).** -/
theorem shuffleWith_perm {α : Type} {fuel : Nat} {xs ys : List α} {st st' : Stream}
    (h : shuffleWith fuel xs st = .ok (ys, st')) : List.Perm ys xs := by
  unfold shuffleWith at h
  cases hg : shuffleGo fuel (xs.length - 1) xs.toArray st with
  | error e => rw [hg] at h; simp at h
  | ok r =>
    rw [hg] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    have := Array.perm_iff_toList_perm.mp (shuffleGo_perm fuel _ _ _ _ _ hg)
    simpa [← h.1] using this

theorem shuffle_perm {α : Type} {xs ys : List α} {st st' : Stream}
    (h : shuffle xs st = .ok (ys, st')) : List.Perm ys xs := shuffleWith_perm h

/-- **S3 (length).** -/
theorem shuffleWith_length {α : Type} {fuel : Nat} {xs ys : List α} {st st' : Stream}
    (h : shuffleWith fuel xs st = .ok (ys, st')) : ys.length = xs.length :=
  (shuffleWith_perm h).length_eq

theorem advance_zero (st : Stream) : st.advance 0 = st := by
  simp [Stream.advance]

theorem toUInt64_add (a b : Nat) : (a + b).toUInt64 = a.toUInt64 + b.toUInt64 := by
  simp only [Nat.toUInt64_eq, UInt64.ofNat_add]

theorem shuffleGo_advance {α : Type} (fuel : Nat) : ∀ (i : Nat) (a : Array α) (st : Stream) (b : Array α) (st' : Stream),
    shuffleGo fuel i a st = .ok (b, st') → ∃ k, i ≤ k ∧ k ≤ fuel * i ∧ st' = st.advance k.toUInt64
  | 0, a, st, b, st', h => by
    simp only [shuffleGo, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨0, by omega, by omega, by rw [← h.2]; exact (advance_zero st).symm⟩
  | i + 1, a, st, b, st', h => by
    unfold shuffleGo at h
    cases hd : uniformBelowWith fuel (i + 2) st with
    | error e => rw [hd] at h; simp at h
    | ok r =>
      rw [hd] at h
      obtain ⟨k1, h1, h2, h3⟩ := uniformBelowWith_advance hd
      obtain ⟨k2, h4, h5, h6⟩ := shuffleGo_advance fuel i _ r.2 b st' h
      refine ⟨k1 + k2, by omega, ?_, ?_⟩
      · have : fuel * (i + 1) = fuel * i + fuel := by rw [Nat.mul_succ]
        omega
      · rw [h6, h3, Stream.advance_advance, toUInt64_add]

/-- **S3 (consumption).** On success the stream advanced by `k` words with `k ≥ L - 1` (and `k ≤ fuel * (L - 1)`); for the empty list and singletons nothing is consumed. -/
theorem shuffleWith_advance {α : Type} {fuel : Nat} {xs ys : List α} {st st' : Stream}
    (h : shuffleWith fuel xs st = .ok (ys, st')) :
    ∃ k, xs.length - 1 ≤ k ∧ k ≤ fuel * (xs.length - 1) ∧ st' = st.advance k.toUInt64 := by
  unfold shuffleWith at h
  cases hg : shuffleGo fuel (xs.length - 1) xs.toArray st with
  | error e => rw [hg] at h; simp at h
  | ok r =>
    rw [hg] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨k, h1, h2, h3⟩ := shuffleGo_advance fuel _ _ _ _ _ hg
    exact ⟨k, h1, h2, by rw [← h.2]; exact h3⟩

theorem shuffleWith_small {α : Type} {fuel : Nat} {xs : List α} (hl : xs.length ≤ 1) (st : Stream) :
    shuffleWith fuel xs st = .ok (xs, st) := by
  have : xs.length - 1 = 0 := by omega
  simp [shuffleWith, this, shuffleGo]

theorem shuffle_advance {α : Type} {xs ys : List α} {st st' : Stream}
    (h : shuffle xs st = .ok (ys, st')) :
    ∃ k, xs.length - 1 ≤ k ∧ k ≤ rejectionFuel * (xs.length - 1) ∧ st' = st.advance k.toUInt64 :=
  shuffleWith_advance h

/-- **S4 (refusal propagates), the first draw.** -/
theorem shuffleWith_refuses {α : Type} {fuel : Nat} {xs : List α} {st : Stream} {e : Refusal}
    (hl : 2 ≤ xs.length) (h : uniformBelowWith fuel xs.length st = .error e) :
    shuffleWith fuel xs st = .error e := by
  have h1 : xs.length - 1 = (xs.length - 2) + 1 := by omega
  have h2 : xs.length = xs.length - 2 + 2 := by omega
  rw [h2] at h
  unfold shuffleWith
  rw [h1]
  simp only [shuffleGo, h]

theorem shuffleGo_error {α : Type} (fuel : Nat) : ∀ (i : Nat) (a : Array α) (st : Stream) (e : Refusal),
    shuffleGo fuel i a st = .error e → ∃ i' st'', i' < i ∧ uniformBelowWith fuel (i' + 2) st'' = .error e
  | 0, a, st, e, h => by simp [shuffleGo] at h
  | i + 1, a, st, e, h => by
    unfold shuffleGo at h
    cases hd : uniformBelowWith fuel (i + 2) st with
    | error e' =>
      rw [hd] at h
      simp only [Except.error.injEq] at h
      subst h
      exact ⟨i, st, by omega, hd⟩
    | ok r =>
      rw [hd] at h
      obtain ⟨i', st'', h1, h2⟩ := shuffleGo_error fuel i _ r.2 e h
      exact ⟨i', st'', by omega, h2⟩

/-- **S4 (no partial list).** A refusal of the shuffle is the refusal of some draw. -/
theorem shuffleWith_error {α : Type} {fuel : Nat} {xs : List α} {st : Stream} {e : Refusal}
    (h : shuffleWith fuel xs st = .error e) :
    ∃ i st'', i + 2 ≤ xs.length ∧ uniformBelowWith fuel (i + 2) st'' = .error e := by
  unfold shuffleWith at h
  cases hg : shuffleGo fuel (xs.length - 1) xs.toArray st with
  | error e' =>
    rw [hg] at h
    simp only [Except.error.injEq] at h
    subst h
    obtain ⟨i', st'', h1, h2⟩ := shuffleGo_error fuel _ _ _ _ hg
    exact ⟨i', st'', by omega, h2⟩
  | ok r => rw [hg] at h; simp at h

/-! ### S2: a function of the stream and the list's length only -/

/-- Map a function over the list of a draw. -/
def mapDraw {α β : Type} (f : α → β) : DrawWith Stream (List α) → DrawWith Stream (List β)
  | .ok (ys, st) => .ok (ys.map f, st)
  | .error e => .error e

theorem swapIfInBounds_map {α β : Type} (f : α → β) (a : Array α) (i j : Nat) :
    (a.map f).swapIfInBounds i j = (a.swapIfInBounds i j).map f := by
  rw [Array.swapIfInBounds_def, Array.swapIfInBounds_def]
  simp only [Array.size_map]
  split
  · split
    · apply Array.ext
      · simp
      · intro k h1 h2
        simp only [Array.getElem_map, Array.getElem_swap]
        split <;> try split
        all_goals rfl
    · simp
  · simp

theorem shuffleGo_map {α β : Type} (f : α → β) (fuel : Nat) : ∀ (i : Nat) (a : Array α) (st : Stream),
    shuffleGo fuel i (a.map f) st = (match shuffleGo fuel i a st with
      | .ok (b, st') => .ok (b.map f, st')
      | .error e => .error e)
  | 0, a, st => by simp [shuffleGo]
  | i + 1, a, st => by
    unfold shuffleGo
    cases hd : uniformBelowWith fuel (i + 2) st with
    | error e => simp
    | ok r =>
      simp only
      rw [swapIfInBounds_map]
      exact shuffleGo_map f fuel i _ r.2

/-- **S2 (the elements are only moved).** The same stream gives the same permutation for the mapped list. -/
theorem shuffleWith_map {α β : Type} (f : α → β) (fuel : Nat) (xs : List α) (st : Stream) :
    shuffleWith fuel (xs.map f) st = mapDraw f (shuffleWith fuel xs st) := by
  unfold shuffleWith
  have : (xs.map f).length = xs.length := List.length_map ..
  rw [this, show (xs.map f).toArray = xs.toArray.map f by simp, shuffleGo_map]
  cases shuffleGo fuel (xs.length - 1) xs.toArray st with
  | error e => rfl
  | ok r => simp [mapDraw]

theorem shuffle_map {α β : Type} (f : α → β) (xs : List α) (st : Stream) :
    shuffle (xs.map f) st = mapDraw f (shuffle xs st) := shuffleWith_map f _ xs st

/-- **S2 (a function of its inputs).** -/
theorem shuffleWith_det {α : Type} {f f' : Nat} {xs xs' : List α} {st st' : Stream} (hf : f = f') (hx : xs = xs') (hs : st = st') :
    shuffleWith f xs st = shuffleWith f' xs' st' := by subst hf; subst hx; subst hs; rfl

/-! ### Vectors and non-vacuity witnesses -/

/-- The list and the position of a successful shuffle (for the vectors). -/
def shuffleVals {α : Type} (r : DrawWith Stream (List α)) : Option (List α × UInt64) :=
  match r with
  | .ok (ys, st) => some (ys, st.pos)
  | .error _ => none

/-- The refusal of a refused shuffle (for the vectors). -/
def shuffleErr {α : Type} (r : DrawWith Stream (List α)) : Option Refusal :=
  match r with
  | .ok _ => none
  | .error e => some e

example : shuffleVals (shuffle (List.range 10) (Stream.ofSeed 1)) = some ([2, 1, 4, 3, 7, 5, 8, 9, 6, 0], 9) := by decide +kernel
example : shuffleVals (shuffle (List.range 10) (Stream.ofSeed 0)) = some ([9, 7, 4, 3, 5, 0, 2, 1, 6, 8], 9) := by decide +kernel
example : shuffleVals (shuffle (List.range 10) (Stream.ofSeed 0x0123456789ABCDEF)) = some ([8, 0, 7, 4, 5, 6, 1, 3, 9, 2], 9) := by decide +kernel
example : shuffleVals (shuffle ['a', 'b', 'c', 'd', 'e'] (Stream.ofSeed 2)) = some (['d', 'b', 'a', 'c', 'e'], 4) := by decide +kernel
example : shuffleVals (shuffle (List.range 5) (Stream.ofSeed 2)) = some ([3, 1, 0, 2, 4], 4) := by decide +kernel
example : shuffleVals (shuffle ([] : List Nat) (Stream.ofSeed 1)) = some ([], 0) := by decide +kernel
example : shuffleVals (shuffle [7] (Stream.ofSeed 1)) = some ([7], 0) := by decide +kernel

-- Non-vacuity: a concrete success (S1, S2, S3 hypotheses hold), and the refusal (S4).
theorem shuffle_ten : shuffle (List.range 10) (Stream.ofSeed 1) =
    .ok ([2, 1, 4, 3, 7, 5, 8, 9, 6, 0], (Stream.ofSeed 1).advance 9) := by rfl
example : List.Perm [2, 1, 4, 3, 7, 5, 8, 9, 6, 0] (List.range 10) := shuffle_perm shuffle_ten
example : [2, 1, 4, 3, 7, 5, 8, 9, 6, 0].length = (List.range 10).length := shuffleWith_length shuffle_ten
example : ∃ k, (List.range 10).length - 1 ≤ k ∧ k ≤ rejectionFuel * ((List.range 10).length - 1) ∧
    (Stream.ofSeed 1).advance 9 = (Stream.ofSeed 1).advance k.toUInt64 := shuffle_advance shuffle_ten
example : shuffle ((List.range 5).map (fun n => n + 10)) (Stream.ofSeed 2) = mapDraw (fun n => n + 10) (shuffle (List.range 5) (Stream.ofSeed 2)) :=
  shuffle_map _ _ _
example : shuffle ([] : List Nat) (Stream.ofSeed 1) = .ok ([], Stream.ofSeed 1) := shuffleWith_small (by decide) _
example : shuffleWith 0 [1, 2] (Stream.ofSeed 1) = .error .fuelExhausted := by rfl
example : shuffleWith 0 [1, 2] (Stream.ofSeed 1) = .error .fuelExhausted :=
  shuffleWith_refuses (by decide) (uniformBelowWith_zero_fuel (by decide) (by decide) _)
example : ∃ i st'', i + 2 ≤ [1, 2].length ∧ uniformBelowWith 0 (i + 2) st'' = .error .fuelExhausted :=
  shuffleWith_error (show shuffleWith 0 [1, 2] (Stream.ofSeed 1) = .error .fuelExhausted by rfl)

end VbmRng
