import VbmProb.Dist.Query
/-! # The quantile of a distribution

`quantile d q` is the smallest key `k` of the support with `q ≤ cdf d k`, for a level `q` in (0, 1] (`docs/spec.md`, "Queries"); a level outside that range is refused with a typed value. The properties (DS8, DS9) are proved in `VbmProbProofs.Dist.Quantile`. -/
namespace VbmProb
namespace Dist

variable {α : Type} [Key α]

/-- The quantile at level `q`: `levelNotPositive q` for `q ≤ 0`, `levelAboveOne q` for `q > 1`, else the smallest key of the support whose cdf reaches `q`.
The last case of the search is never taken for a level in (0, 1] (the greatest key has cdf 1; `quantile_ok`), so the refusal there is not a default. -/
def quantile (d : Dist α) (q : Rat) : Except Refusal α :=
  if q ≤ 0 then .error (.levelNotPositive q)
  else if 1 < q then .error (.levelAboveOne q)
  else match d.support.find? (fun k => decide (q ≤ (d.cdf k).val)) with
    | some k => .ok k
    | none => .error (.levelAboveOne q)

end Dist
end VbmProb
