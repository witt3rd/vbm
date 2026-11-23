import VbmProb.Dist
/-! # Queries on a distribution: `mass`, `expect`, `mean`, `cdf`

The probability of an event, the expectation of a rational-valued function, the mean over a rational carrier, and the cumulative distribution (`docs/spec.md`, "Queries"). All sums are exact `Rat` sums over the atom list in order. The properties (DS6, DS7, DS10) are proved in `VbmProbProofs.Dist.Query`. -/
namespace VbmProb
namespace Dist

variable {α : Type} [Key α]

/-- The sum of the probabilities of the atoms whose key satisfies `e`, in order. -/
def massVal (e : α → Bool) : List (α × Prob) → Rat
  | [] => 0
  | a :: l => if e a.1 then a.2.val + massVal e l else massVal e l

omit [Key α] in
/-- The sum of probabilities is not below 0. -/
theorem massVal_nonneg (e : α → Bool) : ∀ l : List (α × Prob), 0 ≤ massVal e l
  | [] => Rat.le_refl
  | a :: l => by
    unfold massVal
    have ih := massVal_nonneg e l
    split
    · exact Rat.add_nonneg a.2.nonneg ih
    · exact ih

omit [Key α] in
/-- The sum over some of the atoms is at most the sum over all of them. -/
theorem massVal_le_sum (e : α → Bool) : ∀ l : List (α × Prob), massVal e l ≤ (l.map (·.2.val)).sum
  | [] => Rat.le_refl
  | a :: l => by
    unfold massVal
    have ih := massVal_le_sum e l
    simp only [List.map_cons, List.sum_cons]
    split
    · exact Rat.add_le_add_left.mpr ih
    · exact Rat.le_trans ih (by
        have := Rat.add_le_add_right (a := 0) (b := a.2.val) (c := (l.map (·.2.val)).sum)
        rw [Rat.zero_add] at this
        exact this.mpr a.2.nonneg)

/-- The probability of the event `e`: the sum of the probabilities of the atoms whose key satisfies it. -/
def mass (d : Dist α) (e : α → Bool) : Prob :=
  ⟨massVal e d.atoms, massVal_nonneg e d.atoms, by
    have := massVal_le_sum e d.atoms
    rwa [d.total] at this⟩

/-- The expectation of `f`: the sum of `f aᵢ · pᵢ` over the atoms. -/
def expect (d : Dist α) (f : α → Rat) : Rat :=
  (d.atoms.map (fun a => f a.1 * a.2.val)).sum

/-- The mean of a distribution over rational keys. -/
def mean (d : Dist Rat) : Rat := d.expect id

/-- The cumulative distribution at `x`: the mass of the keys not above `x`. -/
def cdf (d : Dist α) (x : α) : Prob := d.mass (fun a => !decide (x < a))

end Dist
end VbmProb
