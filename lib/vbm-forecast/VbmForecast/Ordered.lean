import VbmForecast.Rep
/-! # S3: ordered rules (ranked probability, pinball, interval)

Exact fixed-point scores over a scale `s` (`docs/spec.md`, section 3.4). The ranked probability score is stated through its binary threshold events (`obs ≤ vals_j` against the cumulative `F_j`); the interval score is stated directly and the proofs show it is twice the sum of two pinball scores. RPS and Brier units are `1/s^2`; pinball and interval units are `1/s` times the observation unit. Every claim is exact: no epsilon. -/
namespace VbmForecast

/-- Running sums of `ps` from the accumulator `acc`: `acc + p₀, acc + p₀ + p₁, ...`. -/
def cumFrom (acc : Int) : List Int → List Int
  | [] => []
  | p :: ps => (acc + p) :: cumFrom (acc + p) ps

/-- The thresholds `(vals_j, F_j)` for `j = 0 .. m-2` (the last cumulative is the whole mass and is not a threshold). -/
def rpsThr (vals ps : List Int) : List (Int × Int) := (vals.zip (cumFrom 0 ps)).dropLast

/-- The binary threshold events of an ordered event: forecast `F_j` of the event `obs ≤ vals_j`, which happened iff `obs ≤ vals_j`. -/
def rpsEvents (e : OrderedEvent) : List BinaryEvent :=
  (rpsThr e.vals e.ps).map fun t => ⟨t.2, decide (e.obs ≤ t.1)⟩

/-- The ranked probability score `Σ_{j=0}^{m-2} (F_j - [obs ≤ vals_j] * s)^2`. Units `1/s^2`; unnormalised. -/
def rps (s : Scale) (e : OrderedEvent) : Int :=
  sumInt ((rpsEvents e).map fun b => (b.p - if b.hit then (s : Int) else 0) * (b.p - if b.hit then (s : Int) else 0))

/-- Validated RPS: scale, alignment, outcome count, increasing support, range, normalisation within `tol`. -/
def rpsV (s : Scale) (lim : Limits) (e : OrderedEvent) : Except Refusal Int := do
  validateOrdered s lim e
  pure (rps s e)

/-- The total RPS: the sum of the per-event scores. -/
def rpsTotal (s : Scale) (es : List OrderedEvent) : Int := sumInt (es.map (rps s))

/-- The pinball score: `level * (obs - q)` if `obs ≥ q`, else `(s - level) * (q - obs)`. -/
def pinball (s : Scale) (e : QuantileEvent) : Int :=
  if e.q ≤ e.obs then (e.level : Int) * (e.obs - e.q) else ((s : Int) - (e.level : Int)) * (e.q - e.obs)

/-- Validated pinball: scale and level `0 < level < s`; `obs` is any `Int` and cannot refuse. -/
def pinballV (s : Scale) (e : QuantileEvent) : Except Refusal Int := do
  validateQuantile s e
  pure (pinball s e)

/-- The total pinball score at the levels of the events. -/
def pinballTotal (s : Scale) (es : List QuantileEvent) : Int := sumInt (es.map (pinball s))

/-- The expected pinball score of the report `r` under the true finite distribution with values `vals` and masses `qs` (scale `s`, so the expectation is at scale `s^2`). -/
def expPinball (s level : Nat) (vals qs : List Int) (r : Int) : Int :=
  sumInt ((vals.zip qs).map fun vq => vq.2 * pinball s ⟨level, r, vq.1⟩)

/-- The interval score `2t(hi - lo) + 2s(lo - obs)` below, `+ 2s(obs - hi)` above, `2t(hi - lo)` inside. -/
def intervalScore (s : Scale) (e : IntervalEvent) : Int :=
  if e.obs < e.lo then 2 * (e.tail : Int) * (e.hi - e.lo) + 2 * (s : Int) * (e.lo - e.obs)
  else if e.hi < e.obs then 2 * (e.tail : Int) * (e.hi - e.lo) + 2 * (s : Int) * (e.obs - e.hi)
  else 2 * (e.tail : Int) * (e.hi - e.lo)

/-- Validated interval score: scale, tail, not crossed. -/
def intervalScoreV (s : Scale) (e : IntervalEvent) : Except Refusal Int := do
  validateInterval s e
  pure (intervalScore s e)

/-- The total interval score (one tail `t` per event; totals across different tails are not meaningful). -/
def intervalTotal (s : Scale) (es : List IntervalEvent) : Int := sumInt (es.map (intervalScore s))

end VbmForecast
