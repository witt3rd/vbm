import VbmProb.Scaled
import VbmProb.Apportion
import VbmProb.Dist.Normalize
/-! # Distributions at a fixed-point scale: `Dist.toScaled`, `Dist.ofScaled`

`toScaled` turns a distribution into whole numbers of units that sum to the scale: the `Rat` probabilities are brought to a common denominator `D` (the least common multiple of the denominators), the numerators `pᵢ·D` are naturals that sum to `D`, and `Apportion.units` (largest remainder) shares the scale among them; the keys are kept, in order, and weights of 0 are kept. `ofScaled` reads such weights back, exactly: they must sum to the scale and have strictly increasing keys; the probability at a key is `w / n` (`docs/spec.md`, "Distribution"). The properties FX13 and FX14 are proved in `VbmProbProofs.Dist.Scaled`. -/
namespace VbmProb
namespace Dist

variable {α : Type} [Key α]

/-- A common denominator of the probabilities: the least common multiple of their denominators. -/
def commonDen (atoms : List (α × Prob)) : Nat := (atoms.map (fun a => a.2.val.den)).foldr Nat.lcm 1

/-- The probabilities over their common denominator `D`: the natural numerators `pᵢ·D`. -/
def scaledWeights (d : Dist α) : List Nat :=
  d.atoms.map (fun a => a.2.val.num.toNat * (commonDen d.atoms / a.2.val.den))

/-- The keys of `d`, in order, each with its whole number of units at the scale (largest remainder; some can be 0). -/
def toScaled (sc : Scale) (d : Dist α) : List (α × Nat) :=
  d.support.zip (Apportion.units sc.n (scaledWeights d))

/-- A distribution from weights in units of a scale: refuses `scaledSumNotScale s n` when they do not sum to
the scale, then `keysNotIncreasing i`, then the refusals of `normalize` (the limits); the probability at a key is `w / n`, and keys of weight 0 are absent. -/
def ofScaled (lim : Limits) (sc : Scale) (ws : List (α × Nat)) : Except Refusal (Dist α) :=
  if (ws.map (·.2)).sum ≠ sc.n then .error (.scaledSumNotScale (ws.map (·.2)).sum sc.n)
  else match firstNotInc (ws.map (·.1)) 0 with
  | some i => .error (.keysNotIncreasing i)
  | none => normalize lim (ws.map (fun a => (a.1, (a.2 : Rat))))

end Dist
end VbmProb
