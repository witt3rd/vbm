import VbmProb.Dist.Query
import VbmProb.Dist.Normalize
/-! # Pushing a distribution forward: `map`, `mapMono`, `shift`

The pushforward of a distribution along a function (`docs/spec.md`, `Dist.map`): the atoms `(f aᵢ, pᵢ)` are put through `canon` (sorted by image, equal images merged by adding their probabilities) and kept as a distribution; `mapMono` is the same for a strictly increasing `f`, with no sort and no merge; `shift` adds a constant to every key. The properties (DS15, DS16) are proved in `VbmProbProofs.Dist.Map`. -/
namespace VbmProb
namespace Dist

variable {α β : Type} [Key α] [Key β]

/-- A distribution has at least one atom (the total is 1, not 0). -/
theorem atoms_ne_nil (d : Dist α) : d.atoms ≠ [] := by
  intro h
  have := d.total
  rw [h] at this
  simp at this

/-- The atoms of `d` with the keys sent through `f`, as weights (neither sorted nor merged yet). -/
def pushW (f : α → β) (d : Dist α) : List (β × Rat) := d.atoms.map (fun a => (f a.1, a.2.val))

/-- The pushforward of `d` along `f`: the images with their probabilities added up (`canon`), exact and total.
The fallback branch is never taken (`map_atoms` in `VbmProbProofs.Dist.Map` proves the division step succeeds). -/
def map (f : α → β) (d : Dist α) : Dist β :=
  match normCore (pushW f d) with
  | .ok r => r
  | .error _ => point (f (d.atoms.head (atoms_ne_nil d)).1)

/-- The pushforward along a strictly increasing `f`: the same probabilities at the images, no sort, no merge. -/
def mapMono (f : α → β) (h : ∀ a b : α, a < b → f a < f b) (d : Dist α) : Dist β where
  atoms := d.atoms.map (fun a => (f a.1, a.2))
  sorted := by
    have hs := d.sorted
    rw [List.map_map, List.pairwise_map]
    rw [List.pairwise_map] at hs
    exact hs.imp (fun {a b} hab => h _ _ hab)
  positive := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact d.positive b hb
  total := by
    have := d.total
    rw [List.map_map]
    exact this

end Dist

/-- A carrier of keys with an addition that keeps the order (`a < b → a + c < b + c`) and the usual laws. -/
class AddKey (γ : Type) [Key γ] extends Add γ, Zero γ where
  /-- Adding the same amount to both sides keeps `<`. -/
  add_lt_add_right : ∀ {a b : γ}, a < b → ∀ c : γ, a + c < b + c
  /-- Adding zero changes nothing. -/
  add_zero : ∀ a : γ, a + 0 = a
  /-- Addition is associative. -/
  add_assoc : ∀ a b c : γ, a + b + c = a + (b + c)
  /-- Addition is commutative. -/
  add_comm : ∀ a b : γ, a + b = b + a

instance : AddKey Int where
  add := Int.add
  zero := 0
  add_lt_add_right := fun h c => Int.add_lt_add_right h c
  add_zero := Int.add_zero
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm

instance : AddKey Rat where
  add := Rat.add
  zero := 0
  add_lt_add_right := fun h _ => Rat.add_lt_add_right.mpr h
  add_zero := Rat.add_zero
  add_assoc := Rat.add_assoc
  add_comm := Rat.add_comm

namespace Dist

/-- Every key moved by `c`: the pushforward along `· + c`, which is strictly increasing. -/
def shift {γ : Type} [Key γ] [AddKey γ] (c : γ) (d : Dist γ) : Dist γ :=
  mapMono (fun a => a + c) (fun _ _ h => AddKey.add_lt_add_right h c) d

end Dist
end VbmProb
