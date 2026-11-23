import VbmProb.Prob
import VbmProb.Limits
/-! # Finite distributions: `Dist`, `make`, `point`

A finite distribution over an ordered carrier (`docs/spec.md`, "Distribution"): the atoms have strictly increasing keys, every probability is positive (a zero atom is not stored), and the probabilities sum to exactly 1. Two distributions are equal exactly when their atom lists are (`Dist.ext`). `make` checks external atoms in the stated order and refuses with the first offence; the properties (DS1 to DS3) are proved in `VbmProbProofs.Dist`. -/
namespace VbmProb

/-- A finite distribution: atoms with strictly increasing keys, positive probabilities, summing to exactly 1. -/
structure Dist (α : Type) [Key α] where
  /-- The atoms in key order. -/
  atoms : List (α × Prob)
  /-- The keys are strictly increasing, hence distinct. -/
  sorted : (atoms.map (·.1)).Pairwise (· < ·)
  /-- No atom has probability 0. -/
  positive : ∀ a ∈ atoms, 0 < a.2.val
  /-- The probabilities sum to exactly 1. -/
  total : (atoms.map (·.2.val)).sum = 1

namespace Dist

variable {α : Type} [Key α]

/-- Two distributions with the same atoms are equal (the three laws are proofs). -/
theorem ext {a b : Dist α} (h : a.atoms = b.atoms) : a = b := by
  cases a; cases b; cases h; rfl

/-- The keys of the atoms, in order. -/
def support (d : Dist α) : List α := d.atoms.map (·.1)

/-- The number of atoms. -/
def size (d : Dist α) : Nat := d.atoms.length

/-- The distribution with the one atom `(a, 1)`. -/
def point (a : α) : Dist α where
  atoms := [(a, Prob.one)]
  sorted := by simp
  positive := by simp [Prob.one]; decide +kernel
  total := by simp [Prob.one]; decide +kernel

/-- The first element satisfying `p`, with its 0-based position (counted from `n`). -/
def firstWhere {β : Type} (p : β → Bool) : List β → Nat → Option (Nat × β)
  | [], _ => none
  | x :: xs, n => if p x then some (n, x) else firstWhere p xs (n + 1)

/-- The first position (counted from `n`) of a key that is not above its predecessor, if any. -/
def firstNotInc : List α → Nat → Option Nat
  | a :: b :: rest, n => if a < b then firstNotInc (b :: rest) (n + 1) else some (n + 1)
  | _, _ => none

/-- If no key fails to exceed its predecessor, the keys are strictly increasing. -/
theorem firstNotInc_none : ∀ (l : List α) (n : Nat), firstNotInc l n = none → l.Pairwise (· < ·)
  | [], _, _ => .nil
  | [a], _, _ => by simp
  | a :: b :: rest, n, h => by
    unfold firstNotInc at h
    by_cases hab : a < b
    · simp only [hab, ↓reduceIte] at h
      have ih := firstNotInc_none (b :: rest) (n + 1) h
      refine List.pairwise_cons.mpr ⟨?_, ih⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hab
      · exact Key.lt_trans hab ((List.pairwise_cons.mp ih).1 x hx)
    · simp [hab] at h

/-- A distribution from external atoms, checked in this order: `tooManyAtoms`, `numberTooLarge i`, `emptyDist`,
`keysNotIncreasing i`, `zeroAtom i`, `atomSumNotOne s`; otherwise the distribution with exactly those atoms. -/
def make (lim : Limits) (atoms : List (α × Prob)) : Except Refusal (Dist α) :=
  if lim.maxAtoms < atoms.length then .error (.tooManyAtoms atoms.length lim.maxAtoms)
  else match firstWhere (fun a => decide (lim.maxBits < a.2.val.bits)) atoms 0 with
  | some (i, a) => .error (.numberTooLarge i a.2.val.bits lim.maxBits)
  | none =>
    if atoms = [] then .error .emptyDist
    else if h : (atoms.map (·.1)).Pairwise (· < ·) ∧ (∀ a ∈ atoms, 0 < a.2.val) ∧ (atoms.map (·.2.val)).sum = 1 then
      .ok ⟨atoms, h.1, h.2.1, h.2.2⟩
    else match firstNotInc (atoms.map (·.1)) 0 with
    | some i => .error (.keysNotIncreasing i)
    | none =>
      match firstWhere (fun a => !decide (0 < a.2.val)) atoms 0 with
      | some (i, _) => .error (.zeroAtom i)
      | none => .error (.atomSumNotOne (atoms.map (·.2.val)).sum)

end Dist
end VbmProb
