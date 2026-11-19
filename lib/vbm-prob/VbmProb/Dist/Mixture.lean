import VbmProb.Dist.Query
import VbmProb.Dist.Normalize
/-! # Mixing two distributions: `mixture`

The convex combination of two distributions (`docs/spec.md`, `Dist.mixture`): weight `1 - lam` on `a` and `lam` on `b`. The two atom lists are merged by key into rows holding the probability each side gives that key (0 when the key is absent from a side); the merge is structural recursion on a fuel equal to the total number of atoms, so it is evaluated by the kernel. Each row's weight is `(1 - lam)·pa + lam·pb`; rows of weight 0 are dropped. The refusals come in the stated order: `numberTooLarge` for the weight, then `tooManyAtoms` for the union of the supports. The properties (DS11 to DS14) are proved in `VbmProbProofs.Dist.Mixture`. -/
namespace VbmProb
namespace Dist

/-- The sorted merge of two atom lists with strictly increasing keys, by fuel: a row is a key with the probability
each list gives it (0 when the key is absent from a list). -/
def mergeRows {α : Type} [Key α] : Nat → List (α × Prob) → List (α × Prob) → List (α × (Rat × Rat))
  | 0, _, _ => []
  | _ + 1, [], bs => bs.map (fun b => (b.1, (0, b.2.val)))
  | _ + 1, a :: as, [] => (a :: as).map (fun a => (a.1, (a.2.val, 0)))
  | n + 1, a :: as, b :: bs =>
    if a.1 < b.1 then (a.1, (a.2.val, 0)) :: mergeRows n as (b :: bs)
    else if b.1 < a.1 then (b.1, (0, b.2.val)) :: mergeRows n (a :: as) bs
    else (a.1, (a.2.val, b.2.val)) :: mergeRows n as bs

/-- The rows of the union of the supports of `a` and `b`, in key order. -/
def rows {α : Type} [Key α] (a b : Dist α) : List (α × (Rat × Rat)) :=
  mergeRows (a.atoms.length + b.atoms.length) a.atoms b.atoms

/-- The number of keys in the union of the supports. -/
def unionSize {α : Type} [Key α] (a b : Dist α) : Nat := (rows a b).length

/-- The weight of a row: `(1 - lam)` on the first probability plus `lam` on the second. -/
def mixWeight (lam : Prob) (r : Rat × Rat) : Rat := (1 - lam.val) * r.1 + lam.val * r.2

/-- The weighted rows with the zero weights dropped. -/
def mixKept {α : Type} (lam : Prob) (rs : List (α × (Rat × Rat))) : List (α × Rat) :=
  (rs.map (fun r => (r.1, mixWeight lam r.2))).filter (fun a => decide (0 < a.2))

/-- The weights as atoms (every kept weight lies in (0, 1], proved in `VbmProbProofs.Dist.Mixture`). -/
def mixAtoms {α : Type} (kept : List (α × Rat)) : List (α × Prob) :=
  kept.map (fun a => (a.1, probOf a.2))

/-- The mixture without the limit checks (it never refuses: the atoms always satisfy the three laws). -/
def mixCore {α : Type} [Key α] (lam : Prob) (a b : Dist α) : Except Refusal (Dist α) :=
  ofAtoms (mixAtoms (mixKept lam (rows a b)))

/-- The convex combination, weight `1 - lam` on `a` and `lam` on `b`: refuses `numberTooLarge` when `lam` has more
bits than the limit, `tooManyAtoms` when the union of the supports has more keys than the limit; else the atom at each
key `k` is `(1 - lam)·a(k) + lam·b(k)`, and a zero weight is absent. -/
def mixture {α : Type} [Key α] (lim : Limits) (lam : Prob) (a b : Dist α) : Except Refusal (Dist α) :=
  if lim.maxBits < lam.val.bits then .error (.numberTooLarge 0 lam.val.bits lim.maxBits)
  else if lim.maxAtoms < unionSize a b then .error (.tooManyAtoms (unionSize a b) lim.maxAtoms)
  else mixCore lam a b

end Dist
end VbmProb
