import VbmForecast.Rep
/-! # S2: the Brier score, binary and categorical

Exact fixed-point Brier scores over a scale `s` (`docs/spec.md`, section 3.1): the score of one event, the validated entry points, the total over a sample, the mean as an unreduced `Ratio`, and the expectation under a true distribution (the quantity whose minimum is the propriety statement). Units `1 / s^2`. Every claim is exact: no epsilon. -/
namespace VbmForecast

/-- The Brier score of one binary event: `(p - y*s)^2` with `y = 1` if `hit`, else `0`. Units `1/s^2`. -/
def brierBinary (s : Scale) (e : BinaryEvent) : Int :=
  (e.p - (if e.hit then (s : Int) else 0)) * (e.p - (if e.hit then (s : Int) else 0))

/-- The categorical sum from outcome position `j`: `Σ (p_i - [i = o]*s)^2`. -/
def brierCatFrom (s : Scale) (o : Nat) : Nat → List Int → Int
  | _, [] => 0
  | j, p :: ps => (p - (if j = o then (s : Int) else 0)) * (p - (if j = o then (s : Int) else 0)) + brierCatFrom s o (j + 1) ps

/-- The Brier score of a categorical forecast `ps` and the realised outcome `o`: `Σ_j (p_j - [j = o]*s)^2`. -/
def brierCategorical (s : Scale) (ps : List Int) (o : Nat) : Int := brierCatFrom s o 0 ps

/-- Validated binary score: the scale and the probability range are checked first. -/
def brierBinaryV (s : Scale) (e : BinaryEvent) : Except Refusal Int := do
  validateBinary s e
  pure (brierBinary s e)

/-- Validated categorical score: scale, outcome count and limit, range, normalisation within `tol`, outcome in support. -/
def brierCategoricalV (s : Scale) (lim : Limits) (e : CategoricalEvent) : Except Refusal Int := do
  validateCategorical s lim e
  pure (brierCategorical s e.ps e.outcome)

/-- The total binary Brier score: the sum of the per-event scores. -/
def brierTotal (s : Scale) (es : List BinaryEvent) : Int := sumInt (es.map (brierBinary s))

/-- The total categorical Brier score: the sum of the per-event scores. -/
def brierCatTotal (s : Scale) (es : List CategoricalEvent) : Int :=
  sumInt (es.map fun e => brierCategorical s e.ps e.outcome)

/-- The mean binary Brier score as the unreduced ratio `total / (n * s^2)`; `badScale` for `s = 0`, `empty` for no events. -/
def brierMean (s : Scale) (es : List BinaryEvent) : Except Refusal Ratio :=
  if hs : 0 < s then
    if hn : 0 < es.length then
      .ok ⟨brierTotal s es, es.length * (s * s), Nat.mul_pos hn (Nat.mul_pos hs hs)⟩
    else .error .empty
  else .error .badScale

/-- Expected binary Brier score when the event has true probability `q / s` and `p / s` is reported (scale `s^3`). -/
def expBrierBinary (s : Scale) (q p : Int) : Int :=
  q * brierBinary s ⟨p, true⟩ + ((s : Int) - q) * brierBinary s ⟨p, false⟩

/-- The expectation `Σ_o q_o * brierCategorical p o` from outcome position `o`. -/
def expCatFrom (s : Scale) (ps : List Int) : Nat → List Int → Int
  | _, [] => 0
  | o, q :: qs => q * brierCategorical s ps o + expCatFrom s ps (o + 1) qs

/-- Expected categorical Brier score under true weights `qs` when `ps` is reported (scale `s^3`). -/
def expBrierCat (s : Scale) (qs ps : List Int) : Int := expCatFrom s ps 0 qs

/-- `Σ_j (p_j - q_j)^2` over aligned lists. -/
def sqDist : List Int → List Int → Int
  | p :: ps, q :: qs => (p - q) * (p - q) + sqDist ps qs
  | _, _ => 0

end VbmForecast
