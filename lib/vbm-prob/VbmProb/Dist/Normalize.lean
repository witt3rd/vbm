import VbmProb.Dist
import VbmProb.Dist.Canon
/-! # Normalising weights: `normalize`

A distribution from non-negative weights in any order and with repeated keys (`docs/spec.md`, `Dist.normalize`). The refusals come in the stated order (`tooManyAtoms`, `numberTooLarge i`, `negativeWeight i`); then the weights are put through `canon` (sorted by key, equal keys merged), zero weights are dropped, and each remaining atom gets `w / W`, exactly. The property DS5 is proved in `VbmProbProofs.Dist.Normalize`. -/
namespace VbmProb
namespace Dist

/-- A rational as a probability when it lies in [0, 1] (the other case is never met by `normalize`, which proves it). -/
def probOf (q : Rat) : Prob := if h : 0 ≤ q ∧ q ≤ 1 then ⟨q, h.1, h.2⟩ else Prob.zero

/-- The canonical weights with the zero weights dropped. -/
def normWeights {α : Type} [Key α] (ws : List (α × Rat)) : List (α × Rat) :=
  (canon ws).filter (fun a => decide (0 < a.2))

/-- The atoms of the normalised weights: each weight over the total. -/
def normAtoms {α : Type} (kept : List (α × Rat)) : List (α × Prob) :=
  kept.map (fun a => (a.1, probOf (a.2 / (kept.map (·.2)).sum)))

/-- The distribution with exactly these atoms when they satisfy the three laws (always, for the atoms `normalize` builds). -/
def ofAtoms {α : Type} [Key α] (atoms : List (α × Prob)) : Except Refusal (Dist α) :=
  if h : (atoms.map (·.1)).Pairwise (· < ·) ∧ (∀ a ∈ atoms, 0 < a.2.val) ∧ (atoms.map (·.2.val)).sum = 1 then
    .ok ⟨atoms, h.1, h.2.1, h.2.2⟩
  else .error (.atomSumNotOne (atoms.map (·.2.val)).sum)

/-- The division of the canonical weights by their total: `zeroTotalWeight` when nothing remains. -/
def normCore {α : Type} [Key α] (ws : List (α × Rat)) : Except Refusal (Dist α) :=
  if normWeights ws = [] then .error .zeroTotalWeight else ofAtoms (normAtoms (normWeights ws))

/-- A distribution from non-negative weights: refuses `tooManyAtoms`, `numberTooLarge i`, `negativeWeight i`
(the first offender) and `zeroTotalWeight`; otherwise each key gets its merged weight over the total, exactly. -/
def normalize {α : Type} [Key α] (lim : Limits) (ws : List (α × Rat)) : Except Refusal (Dist α) :=
  if lim.maxAtoms < ws.length then .error (.tooManyAtoms ws.length lim.maxAtoms)
  else match firstWhere (fun a => decide (lim.maxBits < a.2.bits)) ws 0 with
  | some (i, a) => .error (.numberTooLarge i a.2.bits lim.maxBits)
  | none =>
    match firstWhere (fun a => decide (a.2 < 0)) ws 0 with
    | some (i, _) => .error (.negativeWeight i)
    | none => normCore ws

end Dist
end VbmProb
