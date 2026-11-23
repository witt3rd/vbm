import VbmForecast.Rep
/-! # S6: comparison, bootstrap, minimum sample and verdict

Two forecasters scored on the same events (`docs/spec.md`, sections 5 and 6). The comparison consumes per-event losses, so it is independent of every rule. The paired differences, the bootstrap resample sums (driven by draws that are an INPUT, a plain `List Nat`: no generator is imported), the exact order-statistic interval `ci`, the minimum-sample rule and the verdict. A NEGATIVE difference means A has the lower loss. -/
namespace VbmForecast

/-- The verdict: a conclusion, or a typed "not answerable from this evidence" below the minimum sample. -/
inductive Verdict where
  | better
  | worse
  | inconclusive
  | refused (tooFew minEvents : Nat)
  deriving DecidableEq, Repr

/-- The paired differences `a_i - b_i`; unequal lengths are `lengthMismatch`, an empty sample `empty`. -/
def pairedDiffs (a b : List Int) : Except Refusal (List Int) :=
  if a.length ≠ b.length then .error (.lengthMismatch a.length b.length)
  else if a.length = 0 then .error .empty
  else .ok (List.zipWith (· - ·) a b)

/-- The sum of the differences. -/
def diffSum (d : List Int) : Int := sumInt d

/-- The mean difference `{num := diffSum d, den := n}`; `empty` has no mean. -/
def diffMean (d : List Int) : Except Refusal Ratio :=
  if h : 0 < d.length then .ok ⟨diffSum d, d.length, h⟩ else .error .empty

/-- The sum of `d` over the indices of one resample (an index outside `d` counts as zero; the draws are checked below `n`). -/
def resampleSum (d : List Int) (idx : List Nat) : Int := sumInt (idx.map fun i => d.getD i 0)

/-- The `R` consecutive blocks of `n` draws: block `r` is `draws[r*n .. r*n + n)`. -/
def chunks (n : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | r + 1, ds => ds.take n :: chunks n r (ds.drop n)

/-- `R > 0` (else `empty`) and `R ≤ maxResamples` (else `tooMany`). -/
def checkResamples (lim : Limits) (R : Nat) : Except Refusal Unit :=
  if R = 0 then .error .empty
  else if lim.maxResamples < R then .error (.tooMany limitResamples R lim.maxResamples)
  else .ok ()

/-- The `R` resample sums, all over the denominator `n`: refuses `empty`, `tooMany`, `lengthMismatch draws.length (R*n)`, `badDraws`. A function of `(d, draws)` only. -/
def bootstrapSums (lim : Limits) (d : List Int) (R : Nat) (draws : List Nat) : Except Refusal (List Int) := do
  checkSample lim d.length
  checkResamples lim R
  checkAligned draws.length (R * d.length)
  checkDraws d.length draws
  pure ((chunks d.length R draws).map (resampleSum d))

/-- The sums in ascending order (a `mergeSort`, a permutation of the input). -/
def sortInts (xs : List Int) : List Int := xs.mergeSort (fun a b => decide (a ≤ b))

/-- The interval `(sorted[k], sorted[B-1-k])` over `n`, `k = B * t / s`: exact order statistics. Needs `0 < t`, `2t < s` (`badLevel`), `B > 0` and `n > 0` (`empty`). -/
def ci (sums : List Int) (n t s : Nat) : Except Refusal (Ratio × Ratio) :=
  if ¬ (0 < t ∧ 2 * t < s) then .error (.badLevel t s)
  else if sums.length = 0 then .error .empty
  else if h : 0 < n then
    .ok (⟨(sortInts sums).getD (sums.length * t / s) 0, n, h⟩,
         ⟨(sortInts sums).getD (sums.length - 1 - sums.length * t / s) 0, n, h⟩)
  else .error .empty

/-- The verdict from `n`, the observed sum and the interval `(L, U)` over the denominator `n`: the minimum sample is checked FIRST. -/
def verdict (lim : Limits) (n : Nat) (obsSum : Int) (c : Ratio × Ratio) : Verdict :=
  if n < lim.minEvents then .refused n lim.minEvents
  else if c.2.num < 0 ∧ obsSum < 0 then .better
  else if 0 < c.1.num ∧ 0 < obsSum then .worse
  else .inconclusive

/-- The whole comparison: (verdict, observed mean, interval). Below the minimum sample the draws are never looked at and there is no interval (`none`), not a made-up one. -/
def compareForecasters (lim : Limits) (s t R : Nat) (a b : List Int) (draws : List Nat) :
    Except Refusal (Verdict × Ratio × Option (Ratio × Ratio)) :=
  match pairedDiffs a b with
  | .error r => .error r
  | .ok d =>
    match diffMean d with
    | .error r => .error r
    | .ok m =>
      if d.length < lim.minEvents then .ok (.refused d.length lim.minEvents, m, none)
      else
        match bootstrapSums lim d R draws with
        | .error r => .error r
        | .ok sums =>
          match ci sums d.length t s with
          | .error r => .error r
          | .ok c => .ok (verdict lim d.length (diffSum d) c, m, some c)

end VbmForecast
