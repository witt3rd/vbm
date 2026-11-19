# vbm-forecast: specification

Status: written BEFORE any Lean (hub guideline: spec first). Every slice below is written from this file alone. Where a fact is not given and not derivable it is marked `[open question]` and listed in the last section; nothing is invented silently.

## What it is
Forecast verification: given PROBABILISTIC forecasts (probabilities, or discrete distributions) and what actually happened, how good were they, are they calibrated, and is one forecaster better than another. It is general; nothing in it names a product. It is the instrument for any claim that a forecast has EDGE or is TRUSTWORTHY, so it is exact, deterministic, and its properties are proved.

Standard of the experiment phase: exact integer arithmetic, or a STATED EPSILON with a PROVED error bound; no floating point anywhere in the specification or the code; randomness is an INPUT (a list of draws, produced from a seed outside the core); time is an input. Pure data and total functions over `Init` (`VbmForecast` imports `Init` and itself only). No input or output, no network, no storage, no model call.

Conventions used throughout:
- Every score here is a LOSS: lower is better. A "better" forecaster has the lower total loss.
- "Event" means one (forecast, outcome) pair. "Sample" means a list of events. The order of a sample is irrelevant to every score and table (a property below), but not to the bootstrap draws.
- `s` is the probability scale (next section). All integer quantities below are `Int` (or `Nat` where a count).

## 1. Representation (decision, with its justification)

**Decision: fixed-point integers with an explicit scale `s : Nat`, `s > 0`, passed to every function; derived statistics are unreduced exact ratios.** Rationals were considered and rejected as the carrier of the inputs.

- A probability is an `Int` numerator `p` standing for `p / s`. It is valid iff `0 ≤ p ≤ s`. The raw input type is `Int`, so that "below zero" is representable and refused (a `Nat` would make the refusal unsayable).
- Why fixed point: a sum of squares of probabilities at a common scale is an exact integer (`s^2` units); every identity the proofs need (for example the propriety identity below) is a polynomial identity over `Int` closed by `omega`, `decide` and `ring`-style normalisation, with no gcd, no normalisation lemma and no `Rat` from outside `Init`. Comparison of two scores is integer comparison. Why not rationals: normalisation (gcd) adds proof weight and no exactness; the common denominator is already known (`s`).
- The cost, stated: a probability such as one third is not representable; the caller rounds at the boundary, and that rounding is the caller's (a trusted step, marked in `docs/trust-ledger.md` if a wire layer is ever added). A suggested boundary scale is one million; the library proves everything for every `s > 0`, so the scale is never a hidden constant.
- Score scales (what the integer returned means):
  - Brier, RPS: units of `1 / s^2`.
  - Pinball, interval: units of `1 / s` times the observation's own unit (the observation and quantiles are `Int` in one caller-chosen unit; the library never interprets the unit).
  - Log score: units of `2^-F` (nats are NOT used; base 2, bits), see section 3.
- `Ratio` (derived statistics only): `structure Ratio where num : Int; den : Nat; den_pos : 0 < den`. NOT reduced. Equality, order and difference are by cross-multiplication: `Ratio.le a b := a.num * b.den ≤ b.num * a.den`; `Ratio.eqv` likewise. Every function that returns a `Ratio` states its `num` and `den` literally (the spec below), so no reduction is ever needed to know the value.
- Totality: every public function is total. Invalid input is a typed value (`Except Refusal α`), never a default and never a panic.

### Types
```
abbrev Scale := Nat                       -- s, must be > 0 (checked: Refusal.badScale)
structure Ratio where num : Int; den : Nat; den_pos : 0 < den

-- Raw inputs (unchecked, from a boundary):
abbrev RawProb := Int                     -- numerator over s
structure BinaryEvent  where p : RawProb; hit : Bool             -- p = forecast probability of the event; hit = it happened
structure CategoricalEvent where ps : List RawProb; outcome : Nat -- ps.length = k outcomes, outcome < k
structure OrderedEvent where vals : List Int; ps : List RawProb; obs : Int
                              -- vals strictly increasing (the support), ps aligned with vals; obs = observed value
structure QuantileEvent where level : Nat; q : Int; obs : Int      -- level = tau numerator over s, 0 < level < s
structure IntervalEvent where tail : Nat; lo : Int; hi : Int; obs : Int  -- central interval, tail mass tail/s on EACH side

structure Limits where
  maxEvents : Nat; maxOutcomes : Nat; maxBins : Nat; maxResamples : Nat
  minEvents : Nat; logBits : Nat; tol : Nat   -- see "Named limits"
```

## 2. Typed refusals (every way the library refuses)
One inductive, `Refusal`, each constructor a value carrying its evidence; every checker returns `Except Refusal _`. A refusal is never turned into a number.

| constructor | when |
|---|---|
| `badScale` | `s = 0` |
| `probOutOfRange (i : Nat) (p : Int)` | a probability `p` at position `i` has `p < 0` or `p > s` |
| `notNormalised (sum : Int)` | a categorical or ordered forecast has `|sum ps - s| > tol` (`tol` is the stated epsilon, in units of `1/s`; `tol = 0` means exact) |
| `outcomeNotInSupport (outcome : Nat) (k : Nat)` | `outcome ≥ k` (categorical), or an ordered observation that is required to be a support value is not one (only for the categorical-on-ordered reading; for pinball and interval, `obs` is any `Int` and cannot refuse) |
| `tooFewOutcomes (k : Nat)` | `k < 2` |
| `empty` | an empty sample, an empty forecast, an empty edge list |
| `lengthMismatch (a b : Nat)` | two lists that must be aligned differ in length (`vals` vs `ps`; the two forecasters' samples; scores vs draws counts) |
| `supportNotIncreasing` | `vals` is not strictly increasing |
| `badLevel (level s : Nat)` | a quantile level or interval tail outside its open range: pinball needs `0 < level < s`; interval needs `0 < tail` and `2 * tail < s` |
| `crossedInterval (lo hi : Int)` | an interval with `hi < lo` |
| `badEdges` | reliability edges not of the form `0 = e0 < e1 < ... < eB = s` (at least two edges), or a forecast probability is outside `[0, s]` |
| `tooMany (what : Nat) (n limit : Nat)` | a named limit exceeded (the field says which) |
| `badDraws (i : Nat) (d : Nat)` | a bootstrap draw `d` at position `i` is `≥ n` |
| `zeroProbability` | ONLY from the numeric log-score value (section 3), when the probability of the realised outcome is zero (the loss is infinite). The exact log comparison does not refuse on it (it is decided, section 3) |

The minimum-sample case is NOT a refusal of a function: it is the verdict constructor `refused (tooFew n min)` (section 6), because the caller asked a question and the typed answer is "not answerable from this evidence".

## 3. Proper scoring rules

A scoring rule `S(forecast, outcome)` is PROPER when the expected score under a true distribution `q` is minimised by reporting `q`, and STRICTLY proper when only `q` minimises it. "Expected" is taken over the finite outcome set with the true probabilities `q` (also fixed-point at the same scale), so the expectation is an integer at scale `s^3` and the propriety statements are integer identities.

### 3.1 Brier score (exact)
- `brierBinary (s) (e : BinaryEvent) : Int` = `(p - y*s)^2` where `y = 1` if `hit` else `0`. Units `1/s^2`. Range `[0, s^2]`.
- `brierCategorical (s) (ps : List Int) (o : Nat) : Int` = `Σ_j (p_j - [j = o]*s)^2`. Units `1/s^2`. Range `[0, 2*s^2]` (for a valid, normalised forecast).
- Validated entry points: `brierBinaryV : Scale → BinaryEvent → Except Refusal Int`, `brierCategoricalV : Scale → Limits → CategoricalEvent → Except Refusal Int` (checks scale, range, normalisation within `tol`, `k ≥ 2`, `k ≤ maxOutcomes`, outcome in support).
- `brierTotal (s) (es : List BinaryEvent) : Int` = sum of per-event scores; the mean is the `Ratio` `{num := total, den := n * s^2}`.
- EXACT: every Brier claim is exact (no epsilon).

Propriety (binary). Let the true probability be `q` (`0 ≤ q ≤ s`), the reported `p` (`0 ≤ p ≤ s`). The expected score is `E(p; q) = q*(s - p)^2 + (s - q)*p^2` (scale `s^3`). Identity: `E(p; q) - E(q; q) = s * (p - q)^2`. Hence `E(p;q) ≥ E(q;q)` for all `p`, and for `s > 0` equality holds iff `p = q`: STRICT propriety, exact.

Categorical propriety: `Σ_o q_o * brierCategorical(p, o) - Σ_o q_o * brierCategorical(q, o) = s * Σ_j (p_j - q_j)^2` when `Σ q = s`; strict. (Binary is the case `k = 2`.)

### 3.2 Logarithmic score (decision: exact where a comparison suffices; enclosure otherwise)
The log score of a forecast is `-log2 (p_o / s)` where `p_o` is the probability given to the realised outcome. Two different needs, two different tools:

**(A) COMPARISON: no logarithm, exact.** For two forecasters on the same `n` events with realised-outcome probabilities `a_1..a_n` and `b_1..b_n` (integers over the same `s`), forecaster A has the strictly lower total log loss iff `Π a_i > Π b_i` (integers; `s^n` cancels). Define
`logCompare (as bs : List Nat) : Ordering` = `compare (Π as) (Π bs)` after the length check; the result is `gt` iff A is better. Zero probability needs no special case: a product containing a zero is zero, and the forecaster that gave zero to an event that happened loses (two zero products are `eq`, which is the right answer in that the log loss of both is infinite). Cost: the product has `n` factors of `log2 s` bits; `maxEvents` bounds it. EXACT, no epsilon. Every VERDICT based on the log score uses this comparison, never the enclosure.

**(B) NUMERIC VALUE: a stated epsilon, a proved bound.** `log2Enclosure (num den : Nat) (F : Nat) : Except Refusal (Int × Int)` returns `(lo, hi)` with `lo ≤ 2^F * log2(num/den) ≤ hi`, for `0 < num ≤ den`; `hi - lo ≤ 2` (so the epsilon is `2 * 2^-F` bits, i.e. `2^(1-F)`). `F ≤ logBits` (a named limit). The statement is made WITHOUT a logarithm function, because the library has none (`Init` has no real numbers): `lo ≤ 2^F * log2 x` is DEFINED as the exact rational inequality `2^lo ≤ x^(2^F)` if `lo ≥ 0` and `x^(2^F) ≥ 2^lo` read over the rationals for negative `lo` (cross-multiplied into `Nat`s); this is exactly the claim by monotonicity of `t ↦ 2^t`, and is the relation the proofs establish. Algorithm (the contract the proofs follow, the slice may choose any algorithm satisfying the relation and the width bound): range-reduce `x` into `[1/2, 1)` by counting powers of two, then produce `F` fractional bits by repeated squaring of the mantissa, truncating the mantissa DOWN to a stated width `W` bits after every squaring (so every intermediate is a lower or an upper bound by construction, and the truncation error shrinks by a factor of two per bit). `W` is a parameter; the slice states and proves the smallest `W` (as a function of `F`) for which the width bound `hi - lo ≤ 2` holds `[open question: that constant]`. The log LOSS enclosure of an event is `(-hi, -lo)`; a total over `n` events is the sum of enclosures with width `≤ 2n` units of `2^-F` (EXACT bookkeeping, within-epsilon values). `zeroProbability` when `num = 0`.

Which claims are exact and which are within epsilon (log score):
- EXACT: comparison of two forecasters (A); additivity as a product; permutation invariance; the verdict.
- WITHIN EPSILON (proved enclosure): the numeric bits of a loss or a total loss (B).
- Propriety of the log score: STATED, not proved in the first release (it needs Gibbs' inequality, which needs the logarithm). The proved substitute is the exact one: for a true distribution `q` and a report `p`, `Π_j (q_j)^{q_j} ≥ Π_j p_j^{q_j}` over the integers (weighted AM-GM in product form) `[open question: provable without a real-number library? if not, it stays a stated claim in the ledger with status open]`.

### 3.3 Spherical score
NOT specified. It adds a square root (a second approximation with its own bound) and no claim in this library needs it: Brier gives the exact quadratic rule, the log score gives the local rule. Revisit only on a demonstrated need.

### 3.4 Discrete distributions over ordered values
Forecast: `vals : List Int` strictly increasing (`m ≥ 2` values), `ps` aligned, normalised within `tol`. Observation `obs : Int`.

- **Ranked probability score** `rps (s) (e : OrderedEvent) : Int` = `Σ_{j=0}^{m-2} (F_j - [obs ≤ vals_j]*s)^2` where `F_j = Σ_{i ≤ j} ps_i`. Units `1/s^2`, EXACT, unnormalised (no division by `m - 1`; the caller divides by presenting a `Ratio`). It is the sum of binary Brier scores of the threshold events `obs ≤ vals_j`; hence it is proper, strictly proper when the cumulative probabilities of the true distribution are matched: the proof is a reduction to binary propriety (a proved property, section 7).
- **Pinball (quantile) score** `pinball (s) (e : QuantileEvent) : Int` = `level * (obs - q)` if `obs ≥ q`, else `(s - level) * (q - obs)`. Units `1/s` times the observation unit. EXACT. Proper for the `level/s`-quantile: the expected score under a true finite distribution is minimised by any `level/s`-quantile of it (the statement is about a finite distribution given as `(vals, qs)` and the minimisation over all `Int` reports `q`). Status: STATED in the first release; PROVED for finite distributions if the slice completes it (a convex piecewise-linear argument over the support), else it stays `open` in the ledger.
- **Interval score** (central interval, tail mass `t/s` each side, so the interval nominally covers `1 - 2t/s`): `intervalScore (s) (e : IntervalEvent) : Int` = `2*t*(hi - lo) + 2*s*(lo - obs)` if `obs < lo`, `2*t*(hi - lo) + 2*s*(obs - hi)` if `obs > hi`, `2*t*(hi - lo)` otherwise. Units `1/s` times the observation unit, scaled by the nominal level `α = 2t/s`: it is `s * α * IS` where `IS = (hi - lo) + (2/α)*(lo - obs)⁺ + (2/α)*(obs - hi)⁺` is the usual interval score (Gneiting-Raftery form). Scores at different `t` are not additive across `t`; a total is only taken at one `t`. EXACT.
  Identity (proved, section 7): `intervalScore = 2 * (pinball (level := t) lo + pinball (level := s - t) hi)`. So the interval score is proper because the pinball is.

## 4. Calibration

All counts are exact `Nat`; all rates are `Ratio`.

- **Bins.** `edges : List Nat` with `0 = e_0 < e_1 < ... < e_B = s`, `2 ≤ length`, `B ≤ maxBins`. The edges are a parameter. Bin `j` is `[e_j, e_{j+1})`, the last bin also contains `s`. `binOf (edges) (p) : Option Nat` is total on `[0, s]` and every probability in `[0, s]` lies in exactly one bin (a proved property).
- **Reliability table** `reliability (s) (edges) (es : List BinaryEvent) : Except Refusal (List Row)` with
  `structure Row where lo : Nat; hi : Nat; n : Nat; hits : Nat; sumP : Nat` (`sumP` = sum of the forecast numerators in the bin).
  Derived, per non-empty row: observed frequency `{num := hits, den := n}`; mean forecast `{num := sumP, den := n * s}`. Empty rows are present with `n = 0` and have no derived values (no division by zero: the `Ratio` is only built for `n > 0`).
- **Calibration error** (expected calibration error, absolute form) `calibrationError : Ratio` = `{num := Σ_j |hits_j * s - sumP_j|, den := N * s}` where `N` is the number of events. EXACT. The squared form (the reliability component of the Brier score) needs a common denominator and is NOT specified in this release `[open question 4]`; the absolute form suffices for every property below.
- **Calibration in the large** `citl : Ratio × Ratio × Ratio` = (mean forecast `{num := Σ p, den := N * s}`, observed frequency `{num := H, den := N}`, gap `{num := H*s - Σ p, den := N * s}`), `H` = total hits. EXACT. Zero gap iff `H * s = Σ p`.
- A sample is PERFECTLY CALIBRATED (at the given bins) iff in every non-empty bin `hits_j * s = sumP_j`.

## 5. Comparison of two forecasters on the same events

Score-agnostic: the comparison consumes per-event losses (`Int`, at one scale, produced by section 3), so it is independent of every rule.

- `pairedDiffs (a b : List Int) : Except Refusal (List Int)` = `a_i - b_i`. Refuses `empty`, `lengthMismatch`. Convention: a NEGATIVE difference means A has the lower loss (A better on that event).
- `diffSum (d) : Int` and `diffMean (d) : Ratio` = `{num := diffSum d, den := n}` (exact; the score scale is kept by the caller).
- **Paired bootstrap of the mean difference.** The resampling is driven by DRAWS that are an INPUT: `draws : List Nat`, of length `R * n` (`R` resamples, `n` events), each `< n`. Resample `r` (`0 ≤ r < R`) uses `draws[r*n .. r*n + n)` as indices into `d`; its sum is `Σ_{i<n} d[draws[r*n + i]]` and its mean is that sum over `n`.
  - `bootstrapSums (d : List Int) (R : Nat) (draws : List Nat) : Except Refusal (List Int)` returns the `R` resample sums (all with denominator `n`, so they are ordered as integers, exactly). Refuses `empty`, `tooMany` (`R > maxResamples` or `n > maxEvents`), `lengthMismatch (draws.length) (R*n)`, `badDraws`.
  - **It is a function of (data, draws), and so of (data, seed)** when the draws come from a seed (below). No hidden state, no clock.
  - `ci (sums : List Int) (n : Nat) (t s : Nat) : Except Refusal (Ratio × Ratio)`: sort `sums` ascending (a `mergeSort` on `Int`, a proved permutation); with `B = length`, `k = B * t / s` (floor); the interval is `(sorted[k], sorted[B - 1 - k])` as `Ratio`s over `n`. Needs `0 < t`, `2*t < s` (`badLevel`), `B > 0`. They are exact order statistics of the resampled means; `k ≤ B - 1 - k` is guaranteed by `2t < s` (proved), so the interval is never crossed.
- **How the draws are consumed while the deterministic-random library is young.** This library does NOT import it: the core takes the draws as a plain list, which is also the right boundary (the generator and the bootstrap are separately verifiable). The contract with the family's counter-based generator (which has `uniformBelow`) is: draw number `c = r*n + i` is `uniformBelow n` evaluated at counter `c` under the seed, so the draws are a pure function of `(seed, n, R)`. That adapter is a SEPARATE, later slice (a sibling or a thin module that may import the generator once it is vendored by pin, per the vendoring rule); until then, vectors pass literal draw lists, and a worker needs no generator to build or test the bootstrap. `[open question: the generator's exact signature and the name of the counter argument; the adapter slice reads it from the pinned copy]`.
- `R` is a named limit, never a default: `R > 0` and `R ≤ maxResamples`.

## 6. Minimum sample and the verdict
Harm prevented: a claim of edge from a handful of cases. No verdict is issued from fewer than `minEvents` events.

```
inductive Verdict
  | better | worse | inconclusive
  | refused (tooFew : Nat) (minEvents : Nat)    -- n and the minimum
```
`verdict (lim : Limits) (n : Nat) (obsSum : Int) (ci : Ratio × Ratio) : Verdict`, with `ci = (L, U)` over denominator `n` (so compared with `0` through their numerators):
1. if `n < lim.minEvents` then `refused n lim.minEvents` (checked FIRST, before any interval is looked at);
2. else if `U.num < 0` and `obsSum < 0` then `better` (the whole interval is below zero, and the observed difference agrees in sign: A has the lower loss);
3. else if `L.num > 0` and `obsSum > 0` then `worse`;
4. else `inconclusive`.
`compareForecasters` composes `pairedDiffs`, `bootstrapSums`, `ci`, `verdict`; it returns `Except Refusal (Verdict × Ratio × (Ratio × Ratio))` (verdict, observed mean, interval). The minimum-sample check also precedes the draws check, so a sample that is too small is `refused (tooFew)` whatever the draws are.
For the log score the verdict is instead `logVerdict`: `better`/`worse` from `logCompare` (exact, no interval) and the same minimum-sample rule; `inconclusive` only on `eq`.

## 7. Named limits (each with the harm it prevents; the only limits that exist protect the machine or the money)
All are fields of `Limits`; none is hidden inside a function. Defaults below are proposals for the boundary and are `[open question: owner to confirm]`; the proofs hold for every value.

| limit | proposed default | harm it prevents |
|---|---|---|
| `maxEvents` | 1,000,000 | a product (log comparison) or a list so large that a call exhausts memory or time |
| `maxOutcomes` | 1,024 | a categorical forecast so wide that one score exhausts memory or time |
| `maxBins` | 1,024 | a reliability table with more rows than events could ever fill |
| `maxResamples` | 10,000 | a bootstrap whose cost is `R * n` multiplications, unbounded |
| `minEvents` | 30 | a verdict of edge from a handful of cases (the claim the library exists to stop) |
| `logBits` | 24 | a log enclosure whose intermediate numbers grow without bound (`F` is the number of squarings) |
| `tol` | 0 (exact) | a forecast whose probabilities do not sum to one being scored as if they did, within a stated epsilon in `1/s` |

`minEvents ≥ 1` is required (`minEvents = 0` would disable the rule; a dedicated refusal `badLimit` is proposed, `[open question 6]`).

## 8. Properties to prove
Each has one sentence and the non-vacuity witness it needs (a small literal example in the same file, by `decide`/`rfl`, showing the hypothesis can hold). Status in the ledger: `proved` unless marked STATED.

Scores
1. **Brier bounded, zero exactly for perfect.** For valid `p`, `0 ≤ brierBinary ≤ s^2`; `brierBinary = 0` iff `p = s` and `hit`, or `p = 0` and not `hit`; categorical `0 ≤ · ≤ 2*s^2` and `= 0` iff the forecast is one-hot at the outcome. Witness: `s = 10`: `p = 10, hit` gives 0; `p = 7, hit` gives 9 (hand: `(10-7)^2`); `p = 0, hit` gives `100 = s^2` (the bound is attained).
2. **Strict propriety, Brier, binary.** `E(p;q) - E(q;q) = s*(p-q)^2` for all `p, q`; so `E(p;q) ≥ E(q;q)` for valid `p, q`, with equality iff `p = q` (`s > 0`). Witness: `s = 10, q = 7, p = 5`: `E = 250`, `E(q;q) = 210`, difference `40 = 10 * 4`.
3. **Categorical Brier propriety** (the `k`-outcome identity of 3.1). Witness: `s = 10`, `k = 3`, `q = (5,3,2)`, `p = (4,4,2)`.
4. **Additive over events.** Every total is the sum of its per-event scores; `total (xs ++ ys) = total xs + total ys` (Brier, RPS, pinball, interval, log-as-product). Witness: two literal samples with the totals added by hand.
5. **Permutation invariance.** If `xs ~ ys` (`List.Perm`) then `total xs = total ys`, and the reliability table's rows are equal. (The bootstrap is NOT invariant, by construction: its draws index positions; stated so as to prevent a false claim.) Witness: `[a,b,c] ~ [c,a,b]` with distinct scores.
6. **Reliability counts.** The `n` of the rows sum to the number of events; the `hits` sum to the number of `hit` events; the `sumP` sum to `Σ p`; every valid `p` falls in exactly one bin. Witness: the vector of section 10.
7. **Calibration error zero for a perfectly calibrated sample**, and conversely `calibrationError.num = 0` iff perfectly calibrated (the sum of absolute values is zero iff every term is zero). Witness: `s = 10`, edges `[0,10]`, forecasts `5,5` with outcomes hit, miss: `hits*s = 10 = sumP`: error `0`. And a counter-witness with nonzero error.
8. **RPS reduces to Brier thresholds** (the identity of 3.4) hence proper; **interval score = 2 * (pinball lo + pinball hi)** (identity). Witness: section 10 vectors.
9. **Pinball properness** (STATED unless the slice proves it): an `level/s`-quantile minimises the expected pinball over a finite distribution. Witness: `s = 10`, level 9, distribution on `{1,2,3}` with masses `(3,3,4)`.
10. **Log comparison is exact and consistent**: `logCompare` is antisymmetric, transitive (it is `compare` on products), and `gt` iff the total log loss of A is strictly lower in the enclosure sense: if `logCompare as bs = gt`, then every enclosure of A's total loss lies strictly below the exact value of B's loss whenever the enclosure widths are small enough `[the precise statement is given by the slice; a STATED-only claim if it needs a logarithm]`. Witness: realised-outcome probabilities `(5,8)` against `(6,4)` at `s = 10`: products 40 and 24.
11. **Log enclosure is sound and has width ≤ 2.** `lo ≤ 2^F log2(x) ≤ hi` (in the exact power relation of 3.2) and `hi - lo ≤ 2`, for every `x` in `(0, 1]` and `F ≤ logBits`. Witness: `x = 1/2` encloses `-2^F`; `x = 1` gives `(0,0)`.
12. **Bootstrap is a function of (data, seed).** `bootstrapSums d R draws` depends only on `d` and `draws`; equal inputs give equal outputs; with an adapter `draws = gen seed n R` the result is a function of `(d, seed)`; the result depends on `d` only through its values at the drawn indices. Witness: the vector of section 10 run twice.
13. **Interval contains the observed mean when the resamples are all identical.** If every resample sum equals `x`, then `ci = (x/n, x/n)`; in particular if all differences equal `c`, every resample sum is `n*c`, the interval is `[c, c]` and it contains the observed mean `c`. Witness: `d = [2,2,2]`, any valid draws.
14. **ci is well-formed.** The sorted list is a permutation of the sums; `sorted[k] ≤ sorted[B-1-k]`; both lie between the minimum and the maximum resample. Witness: section 10 vector.
15. **Verdict refused below the minimum sample.** `n < minEvents → verdict = refused n minEvents`, whatever the interval and the sum. Witness: `n = 3`, `minEvents = 30`.
16. **Verdict monotone in the evidence.** (a) If the interval `I ⊆ J` (nested) and `verdict J ∈ {better, worse}` with the same `n`, `obsSum` and `minEvents` not refused, then `verdict I = verdict J` (a tighter interval cannot lose a conclusion); (b) raising `minEvents` can only turn a verdict into `refused`, never change `better ↔ worse`; (c) `better` implies `U < 0` and `obsSum < 0`, `worse` implies `L > 0` and `obsSum > 0` (never both). Witness: `n = 40, obsSum = -12, J = (-5, -1) ⊇ I = (-4, -2)`, `minEvents = 30`: both `better`.
17. **Validation is total and sound.** Every validator returns `ok` only when its stated conditions hold, and returns the named `Refusal` for each violated one (one theorem per constructor: a non-vacuity witness each). Witness: for each refusal, a literal input that triggers it.

## 9. Trust
Nothing in `VbmForecast` is trusted: it is data and total functions, and every property above is a theorem. What is TRUSTED, and nothing else, lies at a boundary that this library does not contain: (a) the rounding of caller probabilities to `s`-fixed-point; (b) the generator that turns a seed into `draws` (verified in its own library; its output is only a list here); (c) the choice of the observation unit. A wire layer, if ever added, is a sibling library and appears in `docs/trust-ledger.md`.

## 10. Vectors (known answers, by hand; the vectors slice re-derives each with the reference and checks the code against them)
All at `s = 10` unless stated. Units as in section 1.

| id | input | result |
|---|---|---|
| V1 | binary `p = 7`, hit | `brierBinary = 9` (i.e. `9/100`) |
| V2 | binary `p = 7`, miss | `49` |
| V3 | categorical `ps = (5,3,2)`, outcome 0 | `25 + 9 + 4 = 38` |
| V4 | propriety `q = 7`: `E(5;7) = 7*25 + 3*25 = 250`, `E(7;7) = 7*9 + 3*49 = 210` | difference `40 = 10 * (5-7)^2` |
| V5 | RPS `vals = (1,2,3)`, `ps = (5,3,2)`, `obs = 2`: `F = (5, 8)`, indicators `(0, 1)` | `25 + 4 = 29` |
| V6 | pinball `level = 9`, `q = 5`; `obs = 8`; `obs = 3` | `9*3 = 27`; `1*2 = 2` |
| V7 | interval `t = 1`, `lo = 2`, `hi = 6`, `obs = 9`: `2*1*4 + 2*10*3` | `68`; and `2*(pinball 1 lo=2 obs=9 + pinball 9 hi=6 obs=9) = 2*(7 + 27) = 68` |
| V8 | log comparison, realised probabilities A `(5,8)`, B `(6,4)` | products `40 > 24`: A better; `log2Enclosure 1 2 F` contains `-2^F` |
| V9 | reliability, edges `[0,5,10]`, forecasts/outcomes `(2,0) (3,1) (4,0) (7,1) (8,1) (9,0) (10,1)` | row 0 `[0,5)`: `n=3, hits=1, sumP=9`; row 1 `[5,10]`: `n=4, hits=3, sumP=34`; `N = 7` |
| V10 | calibration error of V9 | `(|1*10 - 9| + |3*10 - 34|) / (7*10) = 5/70` (`= 1/14`) |
| V11 | calibration in the large of V9 | mean forecast `43/70`, observed `4/7 = 40/70`, gap `-3/70` |
| V12 | bootstrap `d = [2, -1, 3]`, `R = 4`, `draws = [0,0,0, 1,1,1, 2,2,2, 0,1,2]` | sums `[6, -3, 9, 4]`; sorted `[-3, 4, 6, 9]`; with `t = 2, s = 10`: `k = 0`, `ci = (-3/3, 9/3) = (-1, 3)`; observed mean `4/3` lies inside |
| V13 | verdict of V12 with `minEvents = 30` | `refused 3 30` |
| V14 | verdict of V12 with `minEvents = 3`, `obsSum = 4` | `inconclusive` (`L < 0`) |

## Slices
Each slice is about 150 production lines of Lean with its proofs and its non-vacuity witnesses, lands behind no flag of its own (a library with no caller: nothing is exposed until a consumer imports it), and updates ONLY its own two files plus the two append-only shared files named at the end. Modules share no file, so slices at the same level run in PARALLEL.

**Level 0 (first, alone)**
- **S1. Representation, refusals, limits and validation.** `VbmForecast/Rep.lean` (`Scale`, `Ratio` with `le`/`eqv`/`add`, `Refusal`, `Limits`, the input structures, the validators: probability range, normalisation within `tol`, support, edges, levels) and `VbmForecastProofs/Rep.lean` (property 17, `Ratio` order is a total preorder, and the witnesses). Nothing else imports anything but this.

**Level 1 (all depend only on S1; run in parallel, five workers)**
- **S2. Brier, binary and categorical.** `VbmForecast/Brier.lean`, `VbmForecastProofs/Brier.lean`: properties 1, 2, 3, 4 (Brier part), 5 (Brier part), vectors V1-V4 as `example`s.
- **S3. Ordered rules: RPS, pinball, interval.** `VbmForecast/Ordered.lean`, `VbmForecastProofs/Ordered.lean`: properties 4/5 (their totals), 8, 9 (proved or recorded `open`), V5-V7. Depends on S1 and on the Brier PROPERTY only through its own copy of the threshold identity (it states `rps` via binary thresholds itself), so it does not need S2 to land first; if the steward wants the reduction proof to cite `brierBinary`, run S3 after S2.
- **S4. Logarithmic score.** `VbmForecast/LogScore.lean`, `VbmForecastProofs/LogScore.lean`: `logCompare`, `logVerdict` (after S6's `Verdict`; or define its own result as `Ordering` and let S6 map it), `log2Enclosure`, properties 10, 11, V8. Two sub-slices if over budget: S4a the exact comparison (about 40 lines), S4b the enclosure (about 110 lines).
- **S5. Calibration.** `VbmForecast/Calibration.lean`, `VbmForecastProofs/Calibration.lean`: `binOf`, `reliability`, `calibrationError`, `citl`, properties 5 (table part), 6, 7, V9-V11.
- **S6. Comparison, bootstrap, minimum sample, verdict.** `VbmForecast/Compare.lean`, `VbmForecastProofs/Compare.lean`: `pairedDiffs`, `diffSum`, `diffMean`, `bootstrapSums`, `ci`, `Verdict`, `verdict`, `compareForecasters`; properties 12-16, V12-V14. The draws are a plain `List Nat`; no generator is imported. Two sub-slices if over budget: S6a differences and the bootstrap sums, S6b `ci` and the verdict.

**Level 2 (after the level it names)**
- **S7. Vectors.** `vectors/` (known answers of section 10 as `example`s over the real functions, the directory Tier 1 already scans) plus one `scripts/test_vectors.sh` that ends with `ran: vectors: N cases` (N > 0, declared with `par` in Tier 1). Depends on S2-S6. It RE-DERIVES each answer independently (a tiny reference in the test, not the library) and compares; a disagreement is a bug in one of them, found before the push.
- **S8. Generator adapter (later; a separate decision).** When the family's deterministic random library is vendored by pin: a thin module `draws (seed) (n R) : List Nat` calling `uniformBelow n` at counter `r*n + i`, with the one theorem that `bootstrapSums d R (draws seed n R)` is a function of `(d, seed)`. Until it lands, the bootstrap runs on literal draws (section 5). This is the only slice that touches `vendor/` and `.land/pins.lock`.

Shared files, append-only (the lander's rebase resolves them; keep edits to one line each): `VbmForecast.lean` and `VbmForecastProofs.lean` (one `import` line per slice) and `VbmForecastProofs/Ledger.lean` with `docs/proof-ledger.md` (one claim per property above; the ledger status is `proved`, or `open`/`limit` for a STATED one, never a silent omission). Each slice also adds one line per proved claim to the ledger so the ratchet moves up.

Order for parallel workers: S1; then S2, S3, S4, S5, S6 together; then S7; S8 when the generator is pinned.

## Open questions
1. The proposed values of the named limits, above all `minEvents` (the number at which a verdict may be issued): owner to confirm. The proofs hold for every value.
2. The width constant and mantissa width `W` of `log2Enclosure` (the proved `hi - lo ≤ 2` is the target; the slice states the `W(F)` that proves it).
3. Whether the propriety of the log score and of the pinball (both STATED) can be proved without a real-number library; if not they stay `open` in the ledger.
4. The squared (reliability-component) form of the calibration error: wanted? It needs a common denominator and is left out until asked.
5. The generator's exact signature (the counter argument and `uniformBelow`'s type), read by slice S8 from the pinned copy.
6. A dedicated refusal for an invalid limit (`minEvents = 0`): a constructor `badLimit` is proposed; confirm.
7. Whether the verdict should also be offered at a significance given as an input (here the interval's tail `t/s` is the only knob, taken from the caller).
