import VbmProb.Dist.Query
import VbmProb.Dist.Normalize
/-! # Conditioning on an event: `condition`

The distribution of the keys given that an event holds (`docs/spec.md`, `Dist.condition`): `nullEvent` if the event has probability 0, otherwise the atoms satisfying the event, each probability divided by the mass of the event (exactly). The division is `normCore` of the kept atoms, whose total is that mass. The property DS17 is proved in `VbmProbProofs.Dist.Condition`. -/
namespace VbmProb
namespace Dist

variable {α : Type} [Key α]

/-- The atoms satisfying `e`, as weights (their sum is the mass of the event). -/
def eventW (d : Dist α) (e : α → Bool) : List (α × Rat) :=
  (d.atoms.filter (fun a => e a.1)).map (fun a => (a.1, a.2.val))

/-- The distribution given the event `e`: refuses `nullEvent` when `e` has probability 0, else the atoms
satisfying `e`, each probability over the mass of `e`. -/
def condition (d : Dist α) (e : α → Bool) : Except Refusal (Dist α) :=
  if (d.mass e).val = 0 then .error .nullEvent else normCore (eventW d e)

end Dist
end VbmProb
