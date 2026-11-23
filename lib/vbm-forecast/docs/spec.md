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

## 11. Time: stamps, calendars, revisions, cuts and splits (the evaluation protocol)

Status: written BEFORE any Lean, as the others are. Every slice of this section (T1 to T13, below) is written from this section alone; the decisions D1 to D10 were settled in a public thread with the two first consumers (a pre-registered held-out test, and a walk-forward guard that had been incubating in a consumer) and are recorded here as decisions, with the reason in one line each. They are not reopened here; the questions that are genuinely open are in 11.17.

**Why it is here.** Forecast verification asks "how good were the forecasts"; the held-out discipline asks the question that comes first: "was the forecast made from what could be known at the time, and was it scored on something it did not see". Two products need the same protocol; by the family's placement rule (core first, then the family; the rule of two) it belongs in this library, as the evaluation protocol of forecast verification. It extends the library; it changes no existing function and no existing name.

Conventions of this section (they differ from sections 1 to 10 only where stated):
- An INSTANT is a `Nat`: an abstract index on ONE clock (the base clock) that the CALLER chooses and onto which the caller maps its dates. The library never parses, formats or compares a date; it compares `Nat`s. "Earlier" is `<`, "no later" is `≤`.
- An ITEM is a `Stamped α` (D1). The word "event" is NOT used in this section: it keeps its meaning of section 1 (a (forecast, outcome) pair, and `Event` is untouched). The legacy function names `orderEvents*` below are kept verbatim only so that the port target (D7, D8) is recognisable; they order stamped items. `[open question 10]`
- Exact integers only (instants, periods and counts are `Nat`); no floating point; every function is total; a refusal is a typed value (`Except Refusal _`, or the named leak values of D7 and D9) and is never turned into a default. No input, output, network or clock: "now" is an input. `VbmForecast` imports `Init` and itself only (Tier 1 scans it).
- `Ordered es` means `List.Pairwise (fun a b => a.at ≤ b.at) es` (non-decreasing stamps). `Nodup` is core `List.Nodup`; `Perm` is `List.Perm`; `<+` is `List.Sublist`; `<+:` is `List.IsPrefix`.
- Every predicate is a `Prop` with a `Decidable` instance, and has a `Bool` twin (`beforeB`, `knowableB`, `Ordered` via `orderedB`) used by `decide`-style witnesses. `List.mergeSort` of core is not evaluated by `decide`: witnesses that sort use `simp` (or `native`-free `rfl` on small literals if it works), never `decide`.

### 11.1 The premise

**a stamp is the source's publication date, not ours**

Everything below is a statement about stamps. A theorem about stamps proves something about leakage in the WORLD only if each stamp is the instant at which the value became knowable to anyone, which is the date the SOURCE published it (an artefact outside the split), and not a date we chose, computed or assigned afterwards. This premise is the caller's; the library cannot check it. It makes it visible (the `origin` field, D2) and never hides it (11.10, `What this does NOT prove`).

### 11.2 D1: one clock, the known-at stamp

```
structure Stamped (α : Type) where      -- constructor `mk` is PRIVATE to Time/Stamp.lean (see below)
  at     : Nat        -- the instant at which the value BECAME KNOWABLE
  origin : Origin     -- D2
  value  : α          -- the payload

def Stamped.ofInstant (pub : Option Nat) (origin : Origin) (v : α) : Except Refusal (Stamped α) :=
  match pub with
  | none   => .error .publishedAbsent
  | some t => .ok { at := t, origin := origin, value := v }
def Stamped.map (f : α → β) (s : Stamped α) : Stamped β := { s with value := f s.value }
```
- **Decision.** A `Stamped α` has exactly one stamp `at : Nat` and a payload. The stamp is when the value BECAME KNOWABLE, never the period it describes (the period travels in the payload, D3). The stamp field is UNCONDITIONAL: there is no stamp-less `Stamped` and no `Option` stamp. A value without a stamp is a different type (the consumer's own, for example a `Fact`); the only way from it to a `Stamped` is a constructor that returns `Except Refusal` (`Stamped.ofInstant`, `Stamped.ofPeriod`; the `pub : Option Nat` argument is how "the consumer has no date" is sayable at the boundary and refused).
- **Reason.** A conditional field is how a refusal gets skipped; a mandatory stamp makes the refusal unbuildable.
- The structure constructor `Stamped.mk` is `private` to `VbmForecast/Time/Stamp.lean` (`structure Stamped (α) where private mk :: ...`; the fields stay readable), so no other module can build a `Stamped` except through `ofInstant` (and `ofPeriod`, which calls it). `Stamped.map` keeps the stamp and the origin. If the pinned Lean cannot express a private constructor on a structure, slice T1 falls back to the convention "no anonymous constructor and no `Stamped.mk` outside `Time/Stamp.lean`" and records that in its ledger line `[open question 11]`.
- One `Stamped` REPLACES the two parallel types of the incubating consumer (a pair `{at, value}` used by its point-in-time guard, and a pair `{stamp, payload}` used by its walk-forward splits).
- Deriving: `Stamped`, `Origin`, `Observation` derive `DecidableEq` (when `α` has it), `Repr`, `BEq` and `Inhabited` only where Lean derives them without a `sorry`-like axiom.
- Properties: `ofInstant_ok_iff : ofInstant pub o v = .ok s ↔ pub = some s.at ∧ s.origin = o ∧ s.value = v`; `ofInstant_none : ofInstant none o v = .error .publishedAbsent`; `map_at`, `map_origin`, `map_value` (`map` keeps stamp and origin). Witness: `ofInstant (some 7) .published 3` is `ok` with `at = 7`; `ofInstant none .published 3` is the refusal.

### 11.3 D2: the origin of a stamp is typed

```
inductive Origin
  | published     -- the source's own publication instant
  | collected     -- the instant at which WE obtained it: later than or equal to the truth, so conservative
```
- **Decision.** Exactly two constructors. There is NO constructor for a REFERENT date (the period the value describes). A referent used as a stamp is anti-conservative (it makes a value look known before it was) and is therefore UNREPRESENTABLE: there is no way to say it.
- **Reason.** The premise of 11.1 is non-circular only if the stamp's origin is outside the split; a typed origin makes the premise a visible field of every item instead of a hope.
- A check can REPORT which origins a split relied on:
  ```
  structure OriginsUsed where published : Bool; collected : Bool
  def originsUsed (sp : Split α) : OriginsUsed      -- over sp.train ++ sp.test
  ```
  `originsUsed_published : (originsUsed sp).published = true ↔ ∃ s ∈ sp.train ++ sp.test, s.origin = .published`, and likewise for `collected`. (`Split` is defined in D8; this function lives in `Time/Check.lean`.) Witness: a split of three items, two `published` and one `collected`, reports both `true`; a split of `published` items only reports `collected = false`.
- Whether a `collected` stamp may be mixed with `published` stamps in one split is NOT decided here: the library reports it, the consumer decides `[open question 3]`.

### 11.4 D3: the referent travels in the payload

```
structure Observation (α : Type) where
  referent : Nat        -- a PERIOD index on a named calendar (D4): what the value describes
  value    : α
```
- **Decision.** The cut tests KNOWABILITY (the stamp). A JOIN tests what the value DESCRIBES ("what did we know in year Y about year X"). So the library offers a standard payload pair `Observation α` and states the as-of join (below) over `Stamped (Observation α)`. A consumer is free to carry its own payload (any `α`): nothing in D5 to D9 requires `Observation`.
- **Reason.** The library never drops the referent: a stamp alone cannot answer "about which period".
- The as-of join (module `Time/Join.lean`), over `es : List (Stamped (Observation α))`:
  ```
  def asOfJoin       (t r : Nat) (es : List (Stamped (Observation α))) : Option (Stamped (Observation α)) :=
    (es.filter (fun s => s.value.referent = r ∧ s.at ≤ t)).getLast?        -- latest in LIST order, known at t, about period r
  def asOfJoinBefore (t r : Nat) (es : ...) : Option (Stamped (Observation α)) :=
    (es.filter (fun s => s.value.referent = r ∧ s.at < t)).getLast?        -- the strict twin
  ```
  Theorems: `asOfJoin_referent` (a result has `value.referent = r`); `asOfJoin_knowable` (a result has `at ≤ t`); `asOfJoin_mem` (a result is an element of `es`); `asOfJoin_none_iff : asOfJoin t r es = none ↔ ∀ s ∈ es, s.value.referent = r → t < s.at`; `asOfJoin_append_gt : t < new.at → asOfJoin t r (es ++ [new]) = asOfJoin t r es` (a later publication does not change what was known then); `asOfJoin_nil`; `asOfJoin_eq_asOf` (the join equals `Vintages.asOf` of the versions of referent `r`, D5); `asOfJoinBefore_*` the strict twins (`_lt` instead of `_knowable`; `_append_ge : t ≤ new.at → unchanged`). Witness (instants, referents are years): items in list order `(at 10, referent 2018, value 100)`, `(at 15, referent 2017, value 90)`, `(at 20, referent 2018, value 110)` (a revision of 2018); `asOfJoin 12 2018 = the first`, `asOfJoin 25 2018 = the third`, `asOfJoin 12 2017 = none`, `asOfJoin 15 2017 = the second`, `asOfJoinBefore 10 2018 = none`, `asOfJoinBefore 11 2018 = the first`.

### 11.5 D4: calendars are named, not a bare unit

```
structure Calendar where
  name      : String
  periodEnd : Nat → Nat       -- period index p ↦ the LAST instant (on the base clock) of period p

def Calendar.WellFormed (c : Calendar) : Prop := ∀ p, c.periodEnd p < c.periodEnd (p + 1)    -- strictly increasing
def Calendar.wfUpTo (c : Calendar) (n : Nat) : Bool := (List.range n).all (fun p => c.periodEnd p < c.periodEnd (p + 1))   -- a decidable check on a finite prefix

structure PeriodRef where  calendarName : String;  index : Nat      -- "period `index` of the calendar called `calendarName`"

def Stamped.ofPeriod (c : Calendar) (pub : Option PeriodRef) (origin : Origin) (v : α) : Except Refusal (Stamped α) :=
  match pub with
  | none   => .error .publishedAbsent
  | some r => if r.calendarName = c.name then Stamped.ofInstant (some (c.periodEnd r.index)) origin v
              else .error (.notExpressible c.name)
```
- **Decision.** "The last instant of a period" is conservative only if the period's end is KNOWN, and it is not 31 December for fiscal years, offset quarters or 52/53-week retail years. So a calendar is DATA the caller names: its `periodEnd` maps a period index to the last base-clock instant of that period. `Stamped.ofPeriod` stamps at `c.periodEnd p`: a coarse source is known no earlier than the end of its period, so the coarse stamp can make the protocol see LESS, never more.
- **Reason.** A bare unit ("month", "year") hides the end-of-period assumption inside the library; a named calendar puts it in the caller's data, where it is auditable.
- A period `p` covers the instants `periodEnd (p-1) + 1 .. periodEnd p` (period 0 starts at instant 0). Periods are therefore CONTIGUOUS in this release `[open question 1]`.
- TWO DISTINCT REFUSALS, with different owners:
  - `Refusal.publishedAbsent`: the consumer supplied no publication date (`pub = none`; also `ofInstant none _ _`, for any origin). The owner is the consumer's data.
  - `Refusal.notExpressible (calendarName : String)`: a publication date WAS supplied but cannot be placed in the named calendar at its granularity (here: the date is given in the units of a calendar other than `c`, `r.calendarName ≠ c.name`; the payload names the TARGET calendar `c.name`). The owner is the mapping from the source's dates to the calendar. This release offers no conversion between calendars; the refusal is the typed way to say so `[open question 1]`.
- Properties (for `c`, `r`, `o`, `v`): `ofPeriod_ok_iff : ofPeriod c (some r) o v = .ok s ↔ r.calendarName = c.name ∧ s.at = c.periodEnd r.index ∧ s.origin = o ∧ s.value = v`; `ofPeriod_none : ofPeriod c none o v = .error .publishedAbsent`; `ofPeriod_wrong_calendar : r.calendarName ≠ c.name → ofPeriod c (some r) o v = .error (.notExpressible c.name)`; `wfUpTo_iff : c.wfUpTo n = true ↔ ∀ p < n, c.periodEnd p < c.periodEnd (p+1)`; `wf_iff_wfUpTo : c.WellFormed ↔ ∀ n, c.wfUpTo n = true`; `periodEnd_mono : c.WellFormed → p ≤ q → c.periodEnd p ≤ c.periodEnd q` (and `periodEnd_lt : p < q → <`); `ofPeriod_conservative : c.WellFormed → p ≤ q → Knowable t (the stamp of period q) → Knowable t (the stamp of period p)` (an earlier period is never knowable later than a later one: the coarse stamp cannot show a later period earlier than an earlier one); `ofPeriod_after_period : (the stamp of period p).at ≥ every instant d of period p`.
- Witnesses, with concrete `periodEnd` functions. The base clock is the DAY index, day 0 being 1 January of year 0; the witnesses use a TOY year of 365 days (no leap years): a caller with leap years supplies another `periodEnd`, and its correctness is the caller's. They are witnesses of well-formedness and of the arithmetic, not a calendar library.
  | calendar | `periodEnd p` | `p = 0` | `p = 1` | `p = 2` |
  |---|---|---|---|---|
  | `calendarMonth` (toy: every month 31 days) | `31 * (p + 1) - 1` | 30 | 61 | 92 |
  | `censusYear` (a calendar year, ending 31 December) | `365 * (p + 1) - 1` | 364 | 729 | 1094 |
  | `fiscalJune` (a fiscal year ending 30 June, a NON-December end; year `p` ends on 30 June of year `p`) | `365 * p + 180` | 180 | 545 | 910 |
  All three are well-formed (`wfUpTo 3 = true`, and the structural statement by `omega`). `ofPeriod fiscalJune (some ⟨"fiscalJune", 2⟩) .published v` is `ok` with `at = 910`; `ofPeriod fiscalJune (some ⟨"censusYear", 2⟩) .published v` is `error (notExpressible "fiscalJune")`; `ofPeriod fiscalJune none .published v` is `error publishedAbsent`. A non-well-formed counter-witness: `periodEnd p = 10` (constant) has `wfUpTo 2 = false`, so `WellFormed` is not vacuously true. A 52/53-week retail calendar (years of 364 or 371 days) is a `periodEnd` the caller supplies from a table; it is not given here `[open question 1]`.
- The constructors do NOT check `c.WellFormed` (it is a statement about the whole function; the caller proves or checks it with `wfUpTo` over the periods it uses). The theorems that need it carry it as a hypothesis, and the witness above shows it can hold.

### 11.6 D6 (stated before D5, which uses it): two predicates, in two modules

```
-- Time/Before.lean   (imports Time/Stamp only)
def Before   (t : Nat) (s : Stamped α) : Prop := s.at < t        -- STRICTLY before t
-- Time/Guard.lean    (imports Time/Before)
def Knowable (t : Nat) (s : Stamped α) : Prop := s.at ≤ t        -- at or before t
```
- **Decision.** `Before t s` (items with stamp STRICTLY before `t`) and `Knowable t s` (stamp at or before `t`) are separate predicates in separate MODULES, so a consumer that wants the strict one imports only `Time/Before` (a pre-registered cut is strict: "everything dated before it is in; everything dated on or after it is out").
- **Reason.** The two cuts differ by exactly the items stamped AT `t`; naming both, separately, keeps that choice explicit and stops one from being used for the other.
- The relation is stated in `Time/Guard.lean`, in the arithmetic-free form, true for ANY discrete stamp with no granularity hypothesis and no successor: `before_iff_knowable_ne : Before t s ↔ Knowable t s ∧ s.at ≠ t`. Also `before_knowable : Before t s → Knowable t s`; `before_irrefl_at : ¬ Before s.at s`; `knowable_refl : Knowable s.at s`; `before_mono : t ≤ t' → Before t s → Before t' s`; `knowable_mono` likewise.
- DO NOT state `Before t = Knowable (t - 1)`. It is not a statement about stamps: it says that `t - 1` is the instant just before `t` on the caller's clock, which holds only for contiguous unit stamps and is false for coarser clocks (month indices), and on `Nat` it is false even at `t = 0` (the stamp `0` is `Knowable 0` and not `Before 0`, and `0 - 1 = 0`). The public thread corrected it; the relation above is the only one the library states.
- Witness: stamps `4, 5, 6`, `t = 5`: `Before` holds for `4` only; `Knowable` holds for `4` and `5`; the stamp `5` is `Knowable` and `at = t`, hence not `Before`, as `before_iff_knowable_ne` says.

### 11.7 D5: a revision is a new stamped value (vintages)

```
structure Vintages (κ α : Type) where       -- ONE key's versions, in the order they were published
  key      : κ
  versions : List (Stamped α)
def Vintages.Ordered (v : Vintages κ α) : Prop := List.Pairwise (fun a b => a.at ≤ b.at) v.versions     -- decidable
def Vintages.empty (k : κ) : Vintages κ α := { key := k, versions := [] }
def Vintages.append (v : Vintages κ α) (new : Stamped α) : Except Refusal (Vintages κ α) :=
  match v.versions.getLast? with
  | some last => if new.at < last.at then .error (.vintageOutOfOrder last.at new.at) else .ok { v with versions := v.versions ++ [new] }
  | none      => .ok { v with versions := [new] }
def Vintages.asOf       (t : Nat) (v : Vintages κ α) : Option (Stamped α) := (v.versions.filter (fun s => decide (s.at ≤ t))).getLast?
def Vintages.asOfBefore (t : Nat) (v : Vintages κ α) : Option (Stamped α) := (v.versions.filter (fun s => decide (s.at < t))).getLast?
```
- **Decision.** The data model is APPEND-ONLY. A value published in one year and revised in a later one existed at BOTH instants; mutating the old value in place would make the later number visible at the earlier instant (anti-conservative, exactly what the rule exists to prevent). So a revision APPENDS a new `Stamped` whose stamp is the FIRST publication at which that value existed; nothing ever edits an element (there is no update function, and `Vintages` offers none). `asOf t` is the latest version whose stamp is at or before `t`, or `none`; `asOfBefore t` the strict twin. Two versions with the same stamp: the later in list order wins (both existed at that instant, and the revision is the later publication) `[open question 6]`.
- **Reason.** What was known then must stay known then.
- A refusal is a new constructor: `Refusal.vintageOutOfOrder (last new : Nat)` (an appended version stamped before the last one: a history is non-decreasing in stamp).
- THEOREMS TO STATE (a hypothesis is named; each has its witness below):
  - `asOf_stamp_le : asOf t v = some s → s.at ≤ t` (`asOf` never returns a version stamped after `t`; no ordering hypothesis); `asOf_mem : asOf t v = some s → s ∈ v.versions`; `asOf_nil : (Vintages.empty k).asOf t = none` (the empty list gives `none`); `asOf_eq_none_iff : asOf t v = none ↔ ∀ s ∈ v.versions, t < s.at`.
  - `asOf_mono : v.Ordered → t ≤ t' → asOf t v = some s → ∃ s', asOf t' v = some s' ∧ s.at ≤ s'.at ∧ (s' = s ∨ s' comes after s in v.versions)` (a later `t` returns that version or a later one).
  - `asOf_append_gt : t < new.at → asOf t { v with versions := v.versions ++ [new] } = asOf t v` (THE KEY PROPERTY: appending a revision stamped after `t` does not change `asOf t`: what was known then stays known then; no ordering hypothesis). Corollary for the checked `append`: `append_ok_iff : v.append new = .ok v' ↔ v'.versions = v.versions ++ [new] ∧ v'.key = v.key ∧ (∀ l, v.versions.getLast? = some l → l.at ≤ new.at)`; `append_ordered : v.Ordered → v.append new = .ok v' → v'.Ordered`; `append_error_iff`; `asOf_append_ok_gt` (the key property through `append`).
  - the strict twins: `asOfBefore_stamp_lt : asOfBefore t v = some s → s.at < t`; `asOfBefore_nil`; `asOfBefore_mono`; `asOfBefore_append_ge : t ≤ new.at → asOfBefore t (append) = asOfBefore t v`; `asOfBefore_eq_asOf_of_ne` (if no version is stamped exactly `t`, `asOfBefore t = asOf t`); `asOfBefore_le_asOf` (the strict result, if any, is at or before the non-strict one in the list).
- Witness (instants; key `"k"`; versions `v1 = (at 10, value 1)`, `v2 = (at 20, value 2)`, `v3 = (at 30, value 3)`, all `published`): `asOf 5 = none`; `asOf 10 = v1`; `asOf 19 = v1`; `asOf 20 = v2`; `asOf 100 = v3`; `asOfBefore 10 = none`; `asOfBefore 11 = v1`; `asOfBefore 20 = v1`; `asOfBefore 21 = v2`. Append a revision `(at 40, value 4)`: `asOf 35` is still `v3` (the key property), `asOf 40` is the revision. Append `(at 25, value 9)` after `v3`: `error (vintageOutOfOrder 30 25)`. The hypothesis `Ordered` holds for `[v1, v2, v3]`; `[v2, v1]` is the counter-witness (not `Ordered`).
- Whether `Vintages` is keyed or a plain `List (Stamped α)` is NOT decided beyond this definition `[open question 2]`; every theorem above is a statement about `versions` and does not use `key`.

### 11.8 D7: the guard and the scored call (port of the incubating point-in-time module)

```
structure Leak where  index : Nat;  stamp : Nat           -- the FIRST leaking index in the list, and the stamp found there
def knowableAt (t : Nat) (es : List (Stamped α)) : List (Stamped α) := es.filter (fun s => decide (s.at ≤ t))
def firstLeakFrom (t i : Nat) : List (Stamped α) → Option Leak       -- scan from list index i
  | []      => none
  | s :: r  => if s.at ≤ t then firstLeakFrom t (i + 1) r else some { index := i, stamp := s.at }
def firstLeak (t : Nat) (es : List (Stamped α)) : Option Leak := firstLeakFrom t 0 es
structure Guarded (t : Nat) (α : Type) where
  items     : List (Stamped α)
  knowable  : ∀ s ∈ items, Knowable t s
def guard (t : Nat) (es : List (Stamped α)) : Except Leak (Guarded t α)       -- `error l` with l = firstLeak, else `ok` carrying the proof
structure ScoredCall (α : Type) where     -- a prediction made at instant `t` from `inputs`, all of them known at `t`
  t       : Nat
  inputs  : List (Stamped α)
  knowable : ∀ s ∈ inputs, Knowable t s
def ScoredCall.make (t : Nat) (es : List (Stamped α)) : Except Leak (ScoredCall α)     -- `guard` and repackage
def ScoredCall.score (f : List (Stamped α) → β) (c : ScoredCall α) : β := f c.inputs
```
- **Decision.** The guard and the scored call are ported from the incubating consumer, generalised from its `{at, value}` pair to `Stamped` with origin. Scoring takes the proof-carrying `ScoredCall`, so scoring with leaked information has no well-typed term (a `ScoredCall` cannot be built except by `make`, whose `error` is the `Leak` naming the first offender). The leak is its own type, not a `Refusal`: it carries the evidence (an index and a stamp), as section 2 requires of a refusal.
- **Reason.** The cheapest proof is the one the type checker holds: a leak is an unbuildable term, not a test that has to be remembered.
- THE PORT TARGET (each statement carried over, with `Stamped`-with-`at` replaced by the new `Stamped`; none of the statements mentions `origin`). If the incubating source is at hand, its statement text is the authority modulo that replacement; the one-line statements below are the minimum a worker can build from this section alone. Modules: `Time/Guard.lean` for `Knowable`, `knowableAt`, `Leak`, `firstLeak*`, `Guarded`, `guard`; `Time/Scored.lean` for `ScoredCall`.
  | name | statement |
  |---|---|
  | `firstLeakFrom_none_iff` | `firstLeakFrom t i es = none ↔ ∀ s ∈ es, Knowable t s` |
  | `firstLeakFrom_some` | `firstLeakFrom t i es = some l → i ≤ l.index ∧` the element at list position `l.index - i` exists, is not `Knowable t`, has `at = l.stamp`, and every element before it is `Knowable t` |
  | `guard_isOk_iff` | `(guard t es).isOk = true ↔ ∀ s ∈ es, Knowable t s` (equivalently `firstLeak t es = none`) |
  | `guard_ok_items` | `guard t es = .ok g → g.items = es` |
  | `guard_error_first` | `guard t es = .error l → firstLeak t es = some l` |
  | `guard_refuses_iff` | `guard t es` is an `error` `↔ ∃ s ∈ es, ¬ Knowable t s` |
  | `mem_knowableAt` | `s ∈ knowableAt t es ↔ s ∈ es ∧ Knowable t s` |
  | `knowableAt_knowable` | `s ∈ knowableAt t es → Knowable t s` |
  | `knowableAt_sublist` | `knowableAt t es <+ es` |
  | `knowableAt_mono` | `t ≤ t' → knowableAt t es <+ knowableAt t' es` |
  | `knowableAt_idem` | `knowableAt t (knowableAt t es) = knowableAt t es` |
  | `knowableAt_of_knowable` | `(∀ s ∈ es, Knowable t s) → knowableAt t es = es` |
  | `guard_knowableAt` | `guard t (knowableAt t es)` is `ok` (filtering by the cut always passes the guard) |
  | `inputs_le` | `∀ c : ScoredCall α, ∀ s ∈ c.inputs, s.at ≤ c.t` |
  | `make_ok_iff` | `(ScoredCall.make t es).isOk = true ↔ ∀ s ∈ es, Knowable t s` |
  | `make_ok_spec` | `ScoredCall.make t es = .ok c → c.t = t ∧ c.inputs = es` |
  | `score_knowableAt` | `ScoredCall.make t (knowableAt t es)` is `ok c`, with `c.inputs = knowableAt t es` and `c.score f = f (knowableAt t es)` |
  Non-vacuity witnesses (each conditional statement has one): stamps `[3, 5, 9]` at `t = 5`: `firstLeak 5 = some ⟨2, 9⟩`; `guard 5` is `error ⟨2, 9⟩`; `knowableAt 5 = [3, 5]`; `guard 5 (knowableAt 5 …)` is `ok`; `ScoredCall.make 5` of `[3, 5]` is `ok` with `inputs_le` holding, of `[3, 5, 9]` the `error`; an empty list passes every guard.
- The shape of `ScoredCall` (what is scored, whether `score` takes the function as above) is the port's: the statements above, and no more, are the contract `[open question 9]`.

### 11.9 D8: splits (port of the incubating walk-forward module, plus the single cut)

```
structure Split (α : Type) where  train : List (Stamped α);  test : List (Stamped α)

def orderEvents (es : List (Stamped α)) : List (Stamped α) := es.mergeSort (fun a b => decide (a.at ≤ b.at))     -- STABLE: equal stamps keep their input order
def cutBefore (t : Nat) (es : List (Stamped α)) : Split α := { train := es.filter (fun s => decide (s.at < t)), test := es.filter (fun s => !decide (s.at < t)) }
def cutAt     (t : Nat) (es : List (Stamped α)) : Split α := { train := es.filter (fun s => decide (s.at ≤ t)), test := es.filter (fun s => !decide (s.at ≤ t)) }
def cut (strict : Bool) (t) (es) : Split α := if strict then cutBefore t es else cutAt t es    -- only a convenience: the caller chooses by NAME, `cutBefore` and `cutAt` are the API

def splitCount (n minTrain horizon step : Nat) : Nat :=
  if minTrain = 0 ∨ horizon = 0 ∨ step = 0 ∨ n < minTrain + horizon then 0
  else (n - minTrain - horizon) / step + 1
def expanding (minTrain horizon step : Nat) (es : List (Stamped α)) : List (Split α)
```
- **Decision.** Over `Stamped α`: `orderEvents` is a stable sort by stamp (core `List.mergeSort`; `decide` cannot evaluate it: witnesses use `simp`). `cutBefore` (train = items `Before t`, test = the rest) and `cutAt` (train = items `Knowable t`, test = the rest) are TWO FUNCTIONS: the caller chooses by name; the pre-registered use is `cutBefore`. Both keep the input order and neither sorts (a caller that wants a sorted split sorts first). `expanding minTrain horizon step es` is the expanding-window walk-forward over the input AS GIVEN (in list order; it does not sort: a caller passes `orderEvents es`, and `no_leakage_sorted` states exactly that). The THREE PARAMETERS ARE INPUTS: the library chooses no number. `splitCount n minTrain horizon step` says EXACTLY how many out-of-sample blocks a history of `n` items yields, so a caller sees how small the sample is BEFORE concluding anything from it.
- **Reason.** One cut or many, the same stamps, the same guarantees; nothing the sample size depends on is hidden in the library.
- Definition of record of `expanding` (the closed form; a worker may implement it with the helpers `blocksFrom` and `expandingGo` and must prove `expanding_eq`):
  `expanding m h st es = (List.range (splitCount es.length m h st)).map (fun k => { train := es.take (m + k*st), test := (es.drop (m + k*st)).take h })`.
  Block `k` trains on the first `m + k*st` items and tests on the next `h`. DEGENERATE parameters (`m = 0`, `h = 0`, `st = 0`) and SHORT histories (`n < m + h`) give the typed empty result `[]` (`splitCount = 0`); no refusal is raised, because `[]` with `splitCount = 0` IS the answer the caller must read. Helper contract (the incubating names, kept so the port is recognisable): `blocksFrom es h st fuel pos` returns the blocks starting at train length `pos`: `blocksFrom … 0 pos = []`; `blocksFrom … (fuel+1) pos = if pos + h ≤ es.length then ⟨es.take pos, (es.drop pos).take h⟩ :: blocksFrom … fuel (pos + st) else []`; `expandingGo` is the guarded entry (the degenerate check, then `blocksFrom` with `fuel = es.length` and `pos = m`).
- PORT TARGET theorem names (each carried over; `n = es.length`, `m, h, st` the three parameters, `k` a block index, `ES k` the k-th split):
  | name | statement |
  |---|---|
  | `orderEvents_perm` | `orderEvents es ~ es` |
  | `orderEvents_ordered` | `Ordered (orderEvents es)` |
  | `orderEvents_length` | `(orderEvents es).length = es.length` |
  | `orderEvents_nodup` | `es.Nodup → (orderEvents es).Nodup` |
  | `cut_train_append_test` | `Ordered es → (cutBefore t es).train ++ (cutBefore t es).test = es`, and the same for `cutAt` |
  | `blocksFrom_zero`, `blocksFrom_succ` | the two defining equations above |
  | `blocksFrom_le` | `(blocksFrom es h st fuel pos).length ≤ fuel` |
  | `expandingGo_eq` | the guarded entry equals the closed form when the parameters are not degenerate |
  | `expanding_eq` | the closed form above |
  | `length_expanding` | `(expanding m h st es).length = splitCount es.length m h st` |
  | `splitCount_formula` | `0 < m → 0 < h → 0 < st → m + h ≤ n → splitCount n m h st = (n - m - h) / st + 1` |
  | `splitCount_short` | `n < m + h → splitCount n m h st = 0` |
  | `expanding_minTrain_too_large` | `n < m → expanding m h st es = []` |
  | `expanding_short` | `n < m + h → expanding m h st es = []` (and the same for each degenerate parameter) |
  | `mem_expanding` | `sp ∈ expanding m h st es ↔ ∃ k < splitCount n m h st, sp = ES k` |
  | `train_mem`, `test_mem` | every item of `sp.train` / `sp.test` of every `sp ∈ expanding …` is in `es` |
  | `no_leakage` | `Ordered es → sp ∈ expanding m h st es → ∀ a ∈ sp.train, ∀ b ∈ sp.test, a.at ≤ b.at` |
  | `no_leakage_sorted` | the same for `expanding m h st (orderEvents es)`, for ANY `es` |
  | `test_not_in_train` | `es.Nodup → sp ∈ expanding … → ∀ b ∈ sp.test, b ∉ sp.train` |
  | `train_test_nodup` | `es.Nodup → sp ∈ expanding … → (sp.train ++ sp.test).Nodup` |
  | `train_grows` | for `k < k' < splitCount`: `(ES k).train <+: (ES k').train` and strictly shorter (`st > 0`) |
  | `test_blocks_in_order` | `Ordered es →` for `k < k'`, every item of `(ES k).test` has `at ≤` every item of `(ES k').test` |
  | `test_blocks_disjoint` | `es.Nodup → h ≤ st →` for `k ≠ k'`, `(ES k).test` and `(ES k').test` share no item |
  | `test_blocks_step_eq_horizon` | `st = h →` the test blocks, concatenated in order, are exactly `(es.drop m).take (splitCount n m h h * h)`: they tile, with no gap and no overlap |
  | the sample witnesses | below |
  If the incubating source states one of these differently (for instance `test_blocks_step_eq_horizon`), the port keeps its statement and records the difference in the ledger line; the lines above are the minimum.
- NEW for the strict cut (three theorems; `Before` from `Time/Before`): `cutBefore_train_before : ∀ s ∈ (cutBefore t es).train, Before t s`; `cutBefore_test_not_before : ∀ s ∈ (cutBefore t es).test, ¬ Before t s` (that is, stamped at or after `t`); `cutBefore_partition : (cutBefore t es).train ++ (cutBefore t es).test ~ es` (for ANY input: together they are exactly the input, as a permutation). Their twins for `cutAt` use `Knowable` (`cutAt_train_knowable`, `cutAt_test_not_knowable`, `cutAt_partition`). Also `cutBefore_train_sublist`, `cutBefore_test_sublist` (each keeps the input order).
- Sample witnesses (stamps equal to the values, all `published`; this is the WITNESS DATA for `decide`-free `simp` proofs):
  - `orderEvents` of stamps `[5, 1, 9, 3]` is `[1, 3, 5, 9]`; stability: items `(at 2, "a")`, `(at 1, "b")`, `(at 2, "c")` sort to `b, a, c` (equal stamps keep order).
  - `cutBefore 5 [2, 5, 5, 8]`: train `[2]`, test `[5, 5, 8]`. `cutAt 5 [2, 5, 5, 8]`: train `[2, 5, 5]`, test `[8]`. `cutBefore 0` of any list has an empty train.
  - `expanding 3 2 1 [1..7]` (n = 7): `splitCount = (7-3-2)/1+1 = 3`: block 0 train `[1,2,3]` test `[4,5]`; block 1 train `[1..4]` test `[5,6]`; block 2 train `[1..5]` test `[6,7]`. `expanding 3 2 2 [1..7]`: `splitCount = 2`: train `[1,2,3]` test `[4,5]`; train `[1..5]` test `[6,7]` (test blocks disjoint: `h ≤ st` holds). `expanding 2 2 2 [1..6]` has `st = h`: tests `[3,4]`, `[5,6]` tile `(drop 2).take 4`.
  - `expanding 3 2 1 [1..5]` (n = m + h exactly): `splitCount = 1`. `expanding 3 2 1 [1..4]` (`n < m + h`): `[]`. `expanding 5 1 1 [1..4]` (`n < m`): `[]`. `expanding 0 2 1 _`, `expanding 3 0 1 _`, `expanding 3 2 0 _`: `[]` (each degenerate parameter). The hypothesis `0 < m → 0 < h → 0 < st → m + h ≤ n` of `splitCount_formula` holds at `(7,3,2,1)`.

### 11.10 D9: the leakage check is a check with a falsifier, not a theorem about data

```
structure LeakPair where  trainIndex : Nat;  testIndex : Nat;  trainStamp : Nat;  testStamp : Nat
def checkSplit       (sp : Split α) : Except LeakPair Unit      -- ok iff ∀ a ∈ sp.train, ∀ b ∈ sp.test, a.at ≤ b.at
def checkSplitStrict (sp : Split α) : Except LeakPair Unit      -- ok iff ∀ a ∈ sp.train, ∀ b ∈ sp.test, a.at < b.at   (the variant for `cutBefore`)
def checkSplits      (sps : List (Split α)) : Except (Nat × LeakPair) Unit     -- the first block (its index) that fails `checkSplit`
```
- **Decision.** Nothing in a dataset entails that every train item was knowable when each test item was made: that is a property of HOW THE COLLECTION WAS MADE (11.1). So the check EVALUATES the property (`tr.at ≤ te.at`, or `<` in the strict variant) over every (train, test) pair and, on failure, returns the FIRST leaking pair, naming the train index, the test index and both stamps: the same discipline as the guard (D7). Pairs are scanned train index first, then test index (lexicographic); an index is a position in `sp.train` / `sp.test`.
- **Reason.** A theorem about data cannot be written; a check that CAN FAIL, with evidence, is the honest form, and the falsifier is part of the statement.
- THEOREMS (`checkSplitStrict_*` are the twins with `<` for `≤`):
  - `checkSplit_ok_iff : checkSplit sp = .ok () ↔ ∀ a ∈ sp.train, ∀ b ∈ sp.test, a.at ≤ b.at` (ok exactly when no pair leaks).
  - `checkSplit_error_first : checkSplit sp = .error p → (p is a leaking pair: `sp.train[p.trainIndex]` and `sp.test[p.testIndex]` exist, carry the stamps `p.trainStamp` and `p.testStamp`, and `¬ p.trainStamp ≤ p.testStamp`) ∧ (no pair with a smaller `trainIndex`, or the same `trainIndex` and a smaller `testIndex`, leaks)`.
  - `checkSplits_ok_iff` and `checkSplits_error_first` likewise (first block, then first pair).
  - THE PROVABLE PART (a statement about the functions and the stamps, not about the world): `checkSplit_cutBefore`, `checkSplitStrict_cutBefore`, `checkSplit_cutAt`, `checkSplitStrict_cutAt` (for ANY input list, ordered or not: train is `< t` (or `≤ t`) and test is `≥ t` (or `> t`)); `checkSplits_expanding : Ordered es → checkSplits (expanding m h st es) = .ok ()`; `checkSplits_expanding_sorted : checkSplits (expanding m h st (orderEvents es)) = .ok ()` for ANY `es`.
  - THE FALSIFIER witnesses (the check can fail): stamps `[5, 1, 9, 3]` UNSORTED, `expanding 2 1 1`: `splitCount = 2`; block 0 (train `[5,1]`, test `[9]`) passes; block 1 (train `[5,1,9]`, test `[3]`) leaks: `checkSplits` is `error (1, ⟨0, 0, 5, 3⟩)`. The same data through `orderEvents` (`[1,3,5,9]`) gives blocks `([1,3],[5])`, `([1,3,5],[9])` and the check is `ok`. `expanding 1 1 1 [4, 4, 4]` (`splitCount = 2`): block 0 has train `[4]` and test `[4]`; `checkSplit` is `ok` (`4 ≤ 4`) and `checkSplitStrict` is `error ⟨0, 0, 4, 4⟩` (equal stamps: the strict variant refuses where the non-strict one passes). `cutBefore 5 [2, 5, 5, 8]` (train `[2]`, test `[5, 5, 8]`) passes `checkSplitStrict` and `checkSplit`; `cutAt 5 [2, 5, 5, 8]` (train `[2, 5, 5]`, test `[8]`) passes both; `cutAt` cannot pass `checkSplitStrict` when an item stamped exactly `t` is in train and another is in test at `t`, which a single cut at `t` never produces (the test side of `cutAt` is `> t`).
  - `originsUsed` (D2) lives in the same module.
- **What this does NOT prove.** A passing check says the STAMPS are consistent with the split. It says NOTHING about leakage in the world unless the stamps are the source's publication dates (11.1): that premise is the caller's, written down, and the `origin` field makes it visible (`published` versus `collected`; a `collected` stamp is later than or equal to the truth, so it can only hide information, never add it). It also does not check: that two stamps came from the same clock; that a calendar is well-formed (D4: the caller's hypothesis); that `Observation.referent` is on the calendar the caller thinks it is; that a revision was stamped at its FIRST publication (D5: the caller's hypothesis, which `vintageOutOfOrder` only partly guards: it catches an out-of-order append, not a wrong stamp); that the scored forecast was committed before the outcome was opened (D10).

### 11.11 D10: what stays out

Not in this section, each with its owner:
- The SEALED OUTCOME (commit the prediction before the outcome is opened): the job of the append-only hash-chained log (`vbm-journal`), a separate item. This section proves nothing about commitment order.
- The RESOLUTION (the smallest share a frame can distinguish from noise at its `n`, recorded with the prediction, naming its `n`): a separate item, stated by the statistician. `splitCount` is the only count this section offers; it is not a power analysis.
- Also out: a conversion between calendars; parsing or formatting of dates; time zones; a clock. The library never reads "now".
- No new named limit: every function of this section is linear (`orderEvents` is `n log n`) in its input list, and the caller bounds the list (`maxEvents`, section 7, is available for that and is not enforced here) `[open question 12]`.

### 11.12 Refusals and values added

| constructor | in | when |
|---|---|---|
| `Refusal.publishedAbsent` | `Refusal` (`Rep.lean`) | no publication instant was supplied (`pub = none`), D1, D4 |
| `Refusal.notExpressible (calendarName : String)` | `Refusal` | a date was supplied in another calendar's units than the named one, D4 |
| `Refusal.vintageOutOfOrder (last new : Nat)` | `Refusal` | an appended version is stamped before the last one, D5 |
| `Leak` | `Time/Guard.lean` | not a `Refusal`: the evidence of the guard, D7 |
| `LeakPair` | `Time/Check.lean` | not a `Refusal`: the evidence of the check, D9 |
Property 17 of section 8 (validation is total and sound, one theorem and one witness per constructor) extends to the three new constructors; the slice that adds them updates `VbmForecastProofs/Rep.lean` for them.

### 11.13 Module plan and import order

`VbmForecast` modules (each imports `Init` and the modules named, nothing else):
| file | holds | imports |
|---|---|---|
| `VbmForecast/Rep.lean` | (existing) `Refusal` gains the three constructors of 11.12 | (none) |
| `VbmForecast/Time/Stamp.lean` | `Origin`, `Stamped`, `Observation`, `ofInstant`, `map` | `Rep` |
| `VbmForecast/Time/Calendar.lean` | `Calendar`, `PeriodRef`, `WellFormed`, `wfUpTo`, `Stamped.ofPeriod`, the three example calendars | `Time.Stamp` |
| `VbmForecast/Time/Before.lean` | `Before` | `Time.Stamp` |
| `VbmForecast/Time/Guard.lean` | `Knowable`, the relation, `knowableAt`, `Leak`, `firstLeak*`, `Guarded`, `guard` | `Time.Before` |
| `VbmForecast/Time/Scored.lean` | `ScoredCall`, `make`, `score` | `Time.Guard` |
| `VbmForecast/Time/Vintages.lean` | `Vintages`, `append`, `asOf`, `asOfBefore` | `Time.Guard` |
| `VbmForecast/Time/Join.lean` | `asOfJoin`, `asOfJoinBefore` | `Time.Vintages` |
| `VbmForecast/Time/Split.lean` | `Split`, `orderEvents`, `cutBefore`, `cutAt`, `cut`, `Ordered` | `Time.Guard` |
| `VbmForecast/Time/Expanding.lean` | `splitCount`, `blocksFrom`, `expandingGo`, `expanding` | `Time.Split` |
| `VbmForecast/Time/Check.lean` | `LeakPair`, `checkSplit*`, `checkSplits`, `OriginsUsed`, `originsUsed` | `Time.Expanding` |
| `VbmForecast.lean` | one `import` line per module | |
The proof files `VbmForecastProofs/Time/Stamp.lean`, `Calendar.lean`, `Before.lean`, `Guard.lean`, `Scored.lean`, `Vintages.lean`, `Join.lean`, `Split.lean`, `Expanding.lean`, `ExpandingProps.lean`, `Check.lean` mirror them one to one (`ExpandingProps` holds the structural theorems of `Expanding`, and imports `Time/Expanding` proofs). They may import `Std` and `Lean`, are never linked, and each imports the proof file of the module it extends plus the code module it proves about. A consumer that wants only the strict cut imports `VbmForecast.Time.Before` (and `Stamp`, which it needs for `Stamped`): it never loads `Guard`, `Knowable` or the guard.
Import order (the DAG, dependencies first): `Rep` → `Stamp` → {`Calendar`, `Before`} ; `Before` → `Guard` → {`Scored`, `Vintages`, `Split`} ; `Vintages` → `Join` ; `Split` → `Expanding` → `Check`. Level 0 is `Stamp`; level 1 is `Calendar` and `Before`; level 2 is `Guard`; level 3 is `Scored`, `Vintages`, `Split`; level 4 is `Join` and `Expanding`; level 5 is `Check`.

### 11.14 Vectors (the requirement)

Known answers, by hand, for this section: the witnesses of 11.2 to 11.10 are its vectors (calendars: 11.5 table; `asOf` and `asOfBefore`: 11.7; the join: 11.4; the guard: 11.8; `cut*` and `expanding`: 11.9; the check and its falsifier: 11.10). The vectors slice (T12) re-derives each with an independent reference (integer shell arithmetic, as the existing vectors do), compares it with the library's printed line, and ends with `ran: time-vectors: N cases` (N > 0). Two requirements beyond the existing ones:
1. **PINNED TO THE HASH OF THE SPECIFICATION FILES.** The generated vector file carries a first line `-- spec-sha256: HEX`, where `HEX` is the SHA-256 of the concatenation, in this order, of: the text of this section 11 (from the heading `## 11.` to the end of `docs/spec.md`) and the files `VbmForecast/Time/*.lean` in sorted path order. The gate recomputes the hash and FAILS, naming the regeneration command, when the specification moved and the vectors were not regenerated. The gate is shown able to fail (a mutated pin is refused: a negative self-test, as for the other gates).
2. **IT PRINTS ITS COVERAGE.** The vectors print one `coverage KIND NAME COUNT` line per item reached, and the gate fails if any REQUIRED item has `COUNT = 0`: a differential test that never reaches a branch is silent about it, and silence reads as agreement. Required: predicates (`Before` true and false at the boundary stamp, `Knowable` true and false at the boundary); `Origin` (both constructors); calendars (`calendarMonth`, `censusYear`, `fiscalJune`, each stamped, and one not well-formed); refusals (`publishedAbsent`, `notExpressible`, `vintageOutOfOrder`); `asOf`/`asOfBefore` (`none`, an earlier version, the latest version, an equal-stamp pair); the join (a hit, a miss, a revision); the guard (`ok`, `error` first leak not at index 0); splits (`cutBefore`, `cutAt`, `expanding` with `splitCount` 0 by each of its five reasons, `1`, and `≥ 2`, `step = horizon`, `step > horizon`); the check (`ok`, a leak naming the pair, strict versus non-strict disagreement, `checkSplits` naming a block `> 0`).

### 11.15 Slice plan (time)

Each slice is about 150 production lines of Lean with its proofs and non-vacuity witnesses, on DISJOINT files, in dependency order; none lands behind a flag of its own (new exported names, no caller). Each adds one ledger line per proved claim (`VbmForecastProofs/Ledger.lean`, `docs/proof-ledger.md`) and one `import` line to `VbmForecast.lean` / `VbmForecastProofs.lean` (the shared append-only files of the Slices section). A conditional theorem is accompanied, in the same proof file, by a concrete example that meets its hypothesis (`example` by `decide`, `rfl` or `simp`). Slices at the same level run in PARALLEL.

| slice | level | files (code, proofs) | statements and witnesses |
|---|---|---|---|
| **T1** stamp | 0 | `Rep.lean` (three constructors), `Time/Stamp.lean`; `Proofs/Rep.lean` (property 17 for them), `Proofs/Time/Stamp.lean` | D1, D2, D3 types; `ofInstant_ok_iff`, `ofInstant_none`, `map_*`; the refusal witnesses; the private constructor (or the recorded fallback) |
| **T2** calendar | 1 | `Time/Calendar.lean`, `Proofs/Time/Calendar.lean` | D4: `wfUpTo_iff`, `wf_iff_wfUpTo`, `periodEnd_mono`, `ofPeriod_*`, `ofPeriod_conservative` (hypothesis `WellFormed`, witnessed by `fiscalJune`; counter-witness the constant calendar); witnesses of the 11.5 table |
| **T3** before | 1 | `Time/Before.lean`, `Proofs/Time/Before.lean` | `Before`, `before_mono`, `before_irrefl_at`, the boundary witness; the module imports `Stamp` only (Tier 1 import scan) |
| **T4** guard | 2 | `Time/Guard.lean`, `Proofs/Time/Guard.lean` | `Knowable`, `before_iff_knowable_ne`, `knowableAt`, `Leak`, `firstLeak*`, `Guarded`, `guard`; the D7 theorems from `firstLeakFrom_none_iff` to `guard_knowableAt` (14 statements); witnesses `[3,5,9]` at `5`. If over budget, T4a `Knowable` + `knowableAt` theorems and T4b `firstLeak`/`guard` theorems (same files, sequenced) |
| **T5** scored call | 3 | `Time/Scored.lean`, `Proofs/Time/Scored.lean` | `ScoredCall`, `make`, `score`; `inputs_le`, `make_ok_iff`, `make_ok_spec`, `score_knowableAt`; witnesses |
| **T6** vintages | 3 | `Time/Vintages.lean`, `Proofs/Time/Vintages.lean` | D5 theorems (the key property `asOf_append_gt` first); witness `v1,v2,v3`; counter-witness for `Ordered` |
| **T7** splits and cuts | 3 | `Time/Split.lean`, `Proofs/Time/Split.lean` | `Split`, `Ordered`, `orderEvents` and its four theorems, `cutBefore`, `cutAt`, `cut_train_append_test`, the three new `cutBefore_*` theorems and their `cutAt` twins; witnesses of 11.9 (`simp`, not `decide`, for the sort) |
| **T8** join | 4 | `Time/Join.lean`, `Proofs/Time/Join.lean` | D3 `Observation` join theorems; witness of 11.4 |
| **T9** expanding, definition and counts | 4 | `Time/Expanding.lean`, `Proofs/Time/Expanding.lean` | `splitCount`, `blocksFrom*`, `expandingGo`, `expanding`; `blocksFrom_zero/succ/le`, `expandingGo_eq`, `expanding_eq`, `length_expanding`, `splitCount_formula`, `splitCount_short`, `expanding_minTrain_too_large`, `expanding_short`, `mem_expanding`; the 11.9 `expanding` witnesses |
| **T10** expanding, structural | 5 | `Proofs/Time/ExpandingProps.lean` (no code file) | `train_mem`, `test_mem`, `no_leakage`, `no_leakage_sorted`, `test_not_in_train`, `train_test_nodup`, `train_grows`, `test_blocks_in_order`, `test_blocks_disjoint`, `test_blocks_step_eq_horizon`; each hypothesis (`Ordered`, `Nodup`, `h ≤ st`, `st = h`) met by a literal example |
| **T11** check | 5 | `Time/Check.lean`, `Proofs/Time/Check.lean` | D9: `checkSplit*`, `checkSplits`, `originsUsed`; `*_ok_iff`, `*_error_first`, the provable part, the falsifier witnesses, the `originsUsed` witnesses |
| **T12** vectors | 6 | `vectors/TimeVectors.lean`, `scripts/test_time_vectors.sh` (declared with `par` in `scripts/tier1.sh`, one line) | 11.14: the spec-hash pin, the coverage lines, the negative self-tests, `ran: time-vectors: N cases` |
| **T13** release | 7 | `VERSION`, `docs/` only | bump to `0.2.0` (11.16); the spec section is read once more against the code |
Order for parallel workers: T1; then T2 and T3; then T4; then T5, T6, T7; then T8 and T9; then T10 and T11; then T12; then T13. (T10 depends on T7 and T9; T11 on T7, T9; T8 on T6.) If a slice exceeds 150 lines or 45 minutes without a passing build it stops and writes a decomposition plan (the repository rule); no theorem is weakened to fit.

### 11.16 Compatibility

This is a MINOR version: `0.1.0` becomes `0.2.0` when T13 lands. New exported names only; nothing is removed or renamed; the existing `Event` (a (forecast, outcome) pair) is untouched and this section never uses the word. One source-level note, stated so a consumer is not surprised: `Refusal` (section 2) gains three constructors, which is additive, but a downstream function that matches `Refusal` exhaustively without a wildcard must add the three cases; no existing function of this library returns them. The consumer whose two incubating modules (a point-in-time guard and walk-forward splits, over two parallel stamped pair types) this section replaces migrates AFTER the release: it re-vendors this library at the `0.2.0` pin, switches to `Stamped` (adding the `origin` of each of its stamps, which it must now state), and deletes its copies; until then both coexist. A second consumer starts on this section directly (its pre-registered cut is `cutBefore`, D6).

### 11.17 Open questions (time)

Numbered in this list, referred to above as `[open question N]`; each says what depends on it.
1. **Calendars with non-contiguous periods, and between calendars.** The representation here (`periodEnd : Nat → Nat`, strictly increasing) makes periods contiguous and gives no way to say "period `p` of calendar A is period `q` of calendar B" or to state a gap (trading days, a 52/53-week retail calendar given only by a table). Depends on: `Calendar`, `notExpressible`, T2; a gap representation would add a field (for example a start), and `notExpressible` would then also cover a date that falls in a gap.
2. **Is `Vintages` keyed or a plain list?** This section defines `Vintages κ α` with a key and a list; no theorem uses the key. Depends on: T6's type; a plain `List (Stamped α)` plus a keyed container for the consumer is the alternative.
3. **May `collected` stamps be mixed with `published` stamps in one split?** The check reports `originsUsed`; whether a split with a `collected` item should refuse, or only be flagged, is not decided. Depends on: T11 (`originsUsed` could become a refusal of `checkSplit`) and the consumers' policy.
4. **A source with a publication TIME, not only a date.** How is a stamp finer than the caller's base clock represented (two sources on one day, an intraday release)? The base clock is the caller's, so it can simply be finer, but then a coarse source stamped by `ofPeriod` and a timed source need the SAME base clock. Depends on: `Stamped.at` (whether `at` stays one `Nat` or gains a second component) and the calendar examples.
5. **The name `Stamped` versus a longer name** (for example `KnownAt`); `Stamped` risks being read as "carrying a timestamp of its own", which is what D1 says it is not. Depends on: every signature in this section (a rename is cheap before T1, a breaking change after the release).
6. **Equal stamps in a `Vintages`**: two versions published at the same instant: the later in list order wins `asOf`; the strict twin ignores both. Is a same-instant revision allowed, or should `append` refuse it? Depends on: `append`, `asOf_mono`.
7. **The origin of a revision**: a revision published later may carry a different origin from the first version; `asOf` returns whichever it finds. Whether a vintage must be of one origin is not decided. Depends on: T6.
8. **Is `cut` (the `Bool`-flag convenience) worth keeping** beside `cutBefore` and `cutAt`? A `Bool` argument is the flag-argument smell the two named functions avoid. Depends on: T7 (it may be dropped before release at no cost).
9. **The exact shape of `ScoredCall` and of the incubating guard's statements** (what is scored, whether `score` takes a function). Written here from the names of the port target; if the incubating source differs, the source's shape wins and this table is corrected in the same slice. Depends on: T5.
10. **The legacy names `orderEvents*`**: they contain the word the section avoids; a rename (`orderItems*`) would break the port target's recognisability. Depends on: the migration of the consumer, T7.
11. **A private constructor on a structure** under the pinned Lean: if not expressible, the convention fallback of D1 applies. Depends on: T1.
12. **A named limit for the size of a list given to `orderEvents`/`expanding`** (the library chooses no number, and adds none here). Depends on: the owner's answer to open question 1 of the main list (the proposed values of the named limits).
13. **The pin of the vectors**: whether hashing the whole of section 11 is too coarse (any edit of the text of the section forces a regeneration even when no vector moves); a finer pin (only the code blocks) is possible. Depends on: T12.
