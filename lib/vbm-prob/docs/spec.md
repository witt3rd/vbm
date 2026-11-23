# vbm-prob: specification

Status: written BEFORE any Lean (hub guideline: spec first). Decisions here are logged as decisions; anything the brief did not give and could not be derived is marked `[open question]` and listed at the end.

## Purpose
Exact discrete probability, valid by construction and kept valid by every operation.

(One concept: a value that is a probability, or a finite distribution of them. Every function either returns a value of those types or refuses with a typed value. The repository's README and AGENTS.md carry an older, longer wording; a later slice item aligns them to this sentence.)

## Core first
This library imports Lean's `Init` only (Tier 1 scans the imports). Everything general that `Init` has is USED, not redefined:

- **`Rat`** (exact rationals, `Init/Data/Rat`): the value of every probability, weight, mean and level. Operations `+ - * /`, the order `<`/`≤`, `Rat.divInt`, `Rat.floor`, `Rat.num`, `Rat.den`, and the lemmas (`Rat.add_comm`, `Rat.mul_comm`, `Rat.add_mul`, `Rat.le_total`, `Rat.le_trans`, `Rat.add_lt_add_right`, `Rat.le_iff_sub_nonneg`, `Rat.divInt_eq_div`, ...). This library defines NO ratio type. Fact to design for: `decide` does NOT evaluate `Rat` arithmetic (`Rat.add`, `Rat.mul` are irreducible); `decide +kernel` does, and so does `simp`/`norm_num`-style rewriting with the `Rat` lemmas. Witnesses about `Rat` values use `decide +kernel` or `simp`, and carry no `native_decide`.
- **`List.mergeSort`** (`Init/Data/List/Sort`): the only sort. It is well-founded and irreducible: `decide` and `rfl` CANNOT evaluate it, even on three elements. What exists: `List.mergeSort_perm` (the result is a permutation), `List.pairwise_mergeSort` (the result is sorted by a total, transitive `le`), `List.mergeSort_of_pairwise` (a sorted list is a fixed point), `List.mergeSort_nil`, `List.mergeSort_singleton`, `List.mergeSort_pair`. Witnesses that involve a sort are therefore written (a) on inputs that are already sorted, by `mergeSort_of_pairwise`, or (b) on inputs of at most three elements by `simp [List.mergeSort]` (checked to work on `[3,1,2]` in the pinned toolchain), or (c) as a proof about every input, never by evaluation.
- **`List.Pairwise (· < ·)`** for "strictly increasing", with its core `Decidable` instance: no `StrictInc` of our own. `List.sum`/folds, `List.Perm`, `List.Forall₂`, `Nat.log2`, `Nat` division and remainder, the `Except` monad.

What this library adds on top (and nothing else): the refinement `Prob` of `Rat`, the positive `Scale`, the largest-remainder apportionment (not in core), and the finite distribution `Dist` with its operations and proofs.

## Conventions
- All namespaces are `VbmProb`. Every function below is total; "refuses" means it returns `Except Refusal _` with a constructor of `Refusal` (never a default value, never a panic, never `Option`).
- Positions in refusals are 0-based indices into the input list, of the FIRST offending element.
- No floating point anywhere. Randomness and time are not inputs of this library at all (it has no use for either).
- Results are canonical: two distributions are equal as values exactly when they have the same atoms (`Dist.ext`, by proof irrelevance), so equality of results is checkable and the properties below are stated with `=`.
- `Σ` in the properties is a fold over the atom list in order, `Rat` addition; slice items pick the exact fold form.

## Types

### `Refusal` (the one typed refusal, section "Typed refusals")

### `Prob`
```
structure Prob where
  val : Rat
  nonneg : 0 ≤ val
  le_one : val ≤ 1
```
A probability: an exact `Rat` in [0, 1]. `Prob.ext` : `p.val = q.val → p = q`. Constants `Prob.zero`, `Prob.one`, and the order `p ≤ q :↔ p.val ≤ q.val` (total, antisymmetric, transitive).

### `Scale`
```
structure Scale where
  n : Nat
  pos : 0 < n
```
A fixed-point scale (the number of units in a whole): `Scale.million` is one million; a named scale is a value, never a bare `Nat` that could be zero. `Scale.make (n : Nat) (lim : Limits) : Except Refusal Scale`.

### `Limits`
```
structure Limits where
  maxAtoms : Nat    -- default 1024
  maxBits  : Nat    -- default 512
  maxScale : Nat    -- default 10^18
```
`Limits.default` has the values above. They are parameters of the entry points that take external data, so a caller states its own bound; section "Named limits" gives the harm of each.

### `Key` (the carrier's laws)
A carrier `α` of atom keys is a type with `LT α`, a decidable `<`, and the three laws of a strict total order: irreflexive, transitive, trichotomous (`a < b ∨ a = b ∨ b < a`). They are bundled as one class `Key α` (built from core's order-law classes where `Init` has them; `[open question]`: the exact core class names to extend; the slice that declares `Key` picks them and reports). Instances: `Nat`, `Int`, `Rat`. `le a b` on keys means `¬ b < a` (so `a ≤ b ↔ a < b ∨ a = b`).

### `Dist`
```
structure Dist (α : Type) [Key α] where
  atoms : List (α × Prob)
  sorted : atoms.map (·.1) |>.Pairwise (· < ·)      -- keys strictly increasing, hence distinct
  positive : ∀ a ∈ atoms, 0 < a.2.val                -- no zero-probability atom
  total : Σ (atoms.map (·.2.val)) = 1                -- exactly 1
```
A finite distribution over an ordered carrier. DECISION (logged): atoms with probability 0 are not stored; the support is the key list. This makes a distribution canonical (its atom list is its identity), so `mixture` with weight 0 is the first operand AS A VALUE, and `normalize` drops zero weights. `Dist.ext`: equal atom lists give equal distributions. `Dist.support d := d.atoms.map (·.1)`; `Dist.size d := d.atoms.length` (at least 1, because the total is 1).

## Functions

### Probability (module `VbmProb.Prob`)
- `Prob.make (q : Rat) : Except Refusal Prob` — `belowZero q` if `q < 0`, `aboveOne q` if `1 < q`, else the probability with `val = q`. Pure and unlimited (a single `Rat`).
- `Prob.ofFrac (num : Int) (den : Nat) : Except Refusal Prob` — `denominatorZero` if `den = 0`, else `Prob.make (Rat.divInt num den)`.
- `Prob.complement (p) : Prob` — `val = 1 - p.val`.
- `Prob.mul (p q) : Prob` — `val = p.val * q.val` (the probability that two independent events both happen).
- `Prob.add (p q) : Except Refusal Prob` — `sumExceedsOne (p.val + q.val)` if the sum exceeds 1, else `val = p.val + q.val` (two disjoint events).
- `Prob.bayes (prior like likeNot : Prob) : Except Refusal Prob` — the posterior of a hypothesis H: `prior = P(H)`, `like = P(E|H)`, `likeNot = P(E|¬H)`. The evidence is `ev = prior·like + (1−prior)·likeNot`; `zeroEvidence` if `ev = 0`, else `val = prior·like / ev` (a probability: it is at most 1 because `prior·like ≤ ev`).
- `Prob.evidence (prior like likeNot : Prob) : Prob` — `ev` above (total probability; at most 1 by the type's own proof). `bayes` refuses exactly when `evidence` is zero.
- `Prob.conditional (joint marginal : Prob) : Except Refusal Prob` — `P(A|B)` from `P(A∧B)` and `P(B)`: `zeroMarginal` if `marginal = 0`; `jointExceedsMarginal` if `joint > marginal`; else `val = joint / marginal`.

### Fixed point (module `VbmProb.Scaled`)
- `toScaled (sc : Scale) (p : Prob) : Nat` — the nearest whole number of units, ties UP: `⌊p·n + 1/2⌋`, computed in integers as `(2·p.num·n + p.den) / (2·p.den)` (`n = sc.n`). Total.
- `ofScaled (sc : Scale) (k : Nat) : Except Refusal Prob` — `scaledAboveScale k n` if `k > n`, else exactly `k / n`. Exact.
- `ofScaledInt (sc : Scale) (k : Int) : Except Refusal Prob` — `belowZero`/`aboveOne` (carrying `k/n` as a `Rat`) outside `0..n`, else `ofScaled`. For a wire integer before validation.
- `apportion (sc : Scale) (ws : List Nat) : Except Refusal (List Nat)` — LARGEST REMAINDER. `W = Σ ws`; `zeroTotalWeight` if `W = 0` (including the empty list); else for each `i`: `floor_i = wᵢ·n / W`, `rem_i = wᵢ·n % W`; `k = n − Σ floor_i`; the result is `floor_i + 1` for the `k` indices with the largest `rem_i` (ties: the EARLIEST index first) and `floor_i` elsewhere. Same length as `ws`. DECISION (logged): the tie rule is the earliest index; the migration of the incubation checks its vectors against this rule (`[open question]`: whether its tie rule is the same).
- `Prob.scaleAll`: not a function; the distribution-level conversion is `Dist.toScaled`/`Dist.ofScaled` below.

### Distribution (modules `VbmProb.Dist`, `VbmProb.Dist.*`)
Constructors:
- `Dist.make (lim) (atoms : List (α × Prob)) : Except Refusal (Dist α)` — checks in this order: `tooManyAtoms` (length above `lim.maxAtoms`); `numberTooLarge i` (an atom probability whose `Rat.bits` exceeds `lim.maxBits`); `emptyDist`; `keysNotIncreasing i` (first `i ≥ 1` with key `i` not above key `i−1`); `zeroAtom i`; `atomSumNotOne s` (the exact sum `s ≠ 1`). Otherwise the distribution with those atoms.
- `Dist.point (a : α) : Dist α` — the single atom `(a, 1)`.
- `Dist.normalize (lim) (ws : List (α × Rat)) : Except Refusal (Dist α)` — from non-negative weights, in ANY order and with repeated keys: `tooManyAtoms`; `numberTooLarge i`; `negativeWeight i`; then keys are sorted by `List.mergeSort` with `le` on keys, equal keys are merged by adding their weights (`canon`), zero-weight atoms are dropped, `zeroTotalWeight` if nothing remains, else each atom gets `w / W`. EXACT (no rounding).
  - helper `canon (ws) : List (α × Rat)` — sort (`mergeSort` on keys) then merge equal neighbours (structural recursion); its output has strictly increasing keys, the same total weight, and the same weight at every key.
- `Dist.ofScaled (lim) (sc) (ws : List (α × Nat)) : Except Refusal (Dist α)` — weights at a scale (for example parts per million) that must sum to EXACTLY `sc.n`: `scaledSumNotScale s n` if not; then `normalize` (keys strictly increasing are required: `keysNotIncreasing i`; zero weights are dropped). Exact: `p = wᵢ / n`.

Queries:
- `Dist.mass (d) (e : α → Bool) : Prob` — the probability of the event, `Σ pᵢ` over atoms with `e aᵢ = true`.
- `Dist.expect (d) (f : α → Rat) : Rat` — `Σ f(aᵢ)·pᵢ`.
- `Dist.mean (d : Dist Rat) : Rat := d.expect id`. For `Int`/`Nat` carriers `d.expect (fun a => (a : Rat))`.
- `Dist.cdf (d) (x : α) : Prob` — `mass d (fun a => ¬ x < a)`, the mass at keys `≤ x`.
- `Dist.quantile (d) (q : Rat) : Except Refusal α` — `levelNotPositive q` if `q ≤ 0`, `levelAboveOne q` if `q > 1`, else the SMALLEST key `k` of the support with `q ≤ cdf d k`. Total on (0, 1]: the last key has cdf exactly 1.

Transformations:
- `Dist.mixture (lim) (lam : Prob) (a b : Dist α) : Except Refusal (Dist α)` — the convex combination: weight `1 − lam` on `a`, `lam` on `b`. `numberTooLarge` if `lam` exceeds `lim.maxBits`; `tooManyAtoms` if the union of the supports exceeds `lim.maxAtoms`; else atom probability `(1−lam)·a(k) + lam·b(k)` at every key `k` of either support (a sorted merge of the two atom lists; an atom whose weight is 0 is absent). `lam = 0` gives `a`, `lam = 1` gives `b`.
- `Dist.map (f : α → β) (d : Dist α) : Dist β` (`[Key β]`) — the pushforward: the atoms `(f aᵢ, pᵢ)` are put through `canon` (sort by image, merge equal images by adding probabilities). Total (no refusal: it cannot grow the number of atoms, and the weights already sum to 1).
- `Dist.mapMono (f) (h : ∀ a b, a < b → f a < f b) (d)` — the pushforward of a strictly increasing `f`: the same probabilities at the images, no sort, no merge.
- `Dist.shift (c : γ) (d : Dist γ)` for a carrier with `+` and the law `∀ a b c, a < b → a + c < b + c` (supplied by an instance for `Int` and `Rat`) — `mapMono (· + c)`.
- `Dist.condition (d) (e : α → Bool) : Except Refusal (Dist α)` — `nullEvent` if `mass d e = 0`, else the atoms satisfying `e`, each probability divided by the mass of the event.
- `Dist.toScaled (sc) (d) : List (α × Nat)` — the keys with the weights `apportion sc.n (probabilities)`; written as the exact proportions the probabilities are, so the call is total (the total weight is the positive `1`; the `Rat` probabilities are first brought to a common denominator `D` and `apportion` runs on the numerators; spelled as an integer-only function in its slice). Some weights can be 0 and are kept, so the result has the same keys as `d`.

## Typed refusals
One inductive, every constructor a way to refuse, none a default:
```
inductive Refusal where
  | belowZero (q : Rat)               -- a probability below 0
  | aboveOne (q : Rat)                -- a probability above 1
  | denominatorZero
  | sumExceedsOne (s : Rat)           -- Prob.add
  | zeroEvidence                      -- Prob.bayes: the evidence has probability 0
  | zeroMarginal                      -- Prob.conditional
  | jointExceedsMarginal
  | zeroScale                         -- Scale.make 0
  | scaleTooLarge (n max : Nat)       -- Scale.make above the limit
  | scaledAboveScale (k n : Nat)      -- ofScaled: k units above n
  | scaledSumNotScale (s n : Nat)     -- Dist.ofScaled: weights do not sum to the scale
  | zeroTotalWeight                   -- apportion, normalize: nothing to divide
  | negativeWeight (i : Nat)
  | emptyDist                         -- Dist.make with no atoms
  | keysNotIncreasing (i : Nat)
  | zeroAtom (i : Nat)
  | atomSumNotOne (s : Rat)
  | tooManyAtoms (n max : Nat)
  | numberTooLarge (i bits max : Nat) -- an input Rat above the bit limit (i: its position; 0 for a lone number)
  | levelNotPositive (q : Rat)        -- quantile
  | levelAboveOne (q : Rat)
  | nullEvent                         -- condition on an event of probability 0
```
`Refusal` has `DecidableEq`/`Repr` (derived). A consumer maps these into its own refusal type (the migration list says where).

## Named limits
Only limits that protect the machine or the money; each is a field of `Limits` and a parameter, never a hidden constant.

| Limit | Default | Harm it prevents | Refusal |
|---|---|---|---|
| `maxAtoms` | 1024 | `Dist.make`, `normalize` and `mixture` are linear in atoms but their `Rat` sums have denominators that multiply: an unbounded atom list read off a wire exhausts memory and time in the `mean`/`cdf` sums | `tooManyAtoms` |
| `maxBits` (bits of numerator + denominator of any input `Rat`) | 512 | `Rat` arithmetic does a gcd on every operation, quadratic in the bit size: a few huge numbers off a wire stall the process | `numberTooLarge` |
| `maxScale` | 10^18 | a scale is a `Nat`, and `toScaled`/`apportion` multiply by it: an absurd scale allocates unbounded integers | `scaleTooLarge` |

The bound on every RESULT is derived, not checked again: a result of `mixture`, `condition`, `map`, `shift`, `bayes` combines at most a fixed number (four) of input numbers per atom, so its size is a constant multiple of `maxBits`; `mean` and `cdf` sum at most `maxAtoms` such numbers. `Prob.make` and `Prob.ofFrac` take a lone value and carry no limit. `[open question]`: whether the defaults suit the consumers (a steward may pass its own `Limits`).

`Rat.bits q := bitLength |q.num| + bitLength q.den` with `bitLength 0 = 0` and `bitLength n = Nat.log2 n + 1` otherwise.

## Properties to prove
Stable labels. Each has a NON-VACUITY WITNESS (`W:`): a concrete case showing the hypotheses can hold and the claim is not trivially true; a property with a hypothesis also states a case where the hypothesis fails and the function refuses. Witnesses over `Rat` use `decide +kernel` or `simp`; those that sort use the means in section "Core first".

### Probability
- **PR1** `Prob.make q = .ok p ↔ 0 ≤ q ∧ q ≤ 1`, and then `p.val = q`; it refuses `belowZero q` for `q < 0` and `aboveOne q` for `q > 1`. W: `make (1/2)` ok; `make 0`, `make 1` ok (the edges); `make (-1/2) = belowZero (-1/2)`; `make (3/2) = aboveOne (3/2)`.
- **PR2** `ofFrac n d` is `denominatorZero` iff `d = 0`, and otherwise agrees with `make (n/d)`. W: `ofFrac 1 4` ok with `val = 1/4`; `ofFrac 1 0` refuses; `ofFrac 5 4` refuses `aboveOne`.
- **PR3** `complement` is an involution, `val (complement p) = 1 − p.val`, `complement zero = one`, and `p.val + (complement p).val = 1`. W: `complement (1/4)` has `val 3/4`.
- **PR4** `mul` has `val = p.val·q.val`, is commutative and associative, has `one` as unit and `zero` as absorbing element, and `mul p q ≤ p` and `≤ q`. W: `mul (1/2) (1/3)` has `val 1/6`.
- **PR5** `add p q = .ok r ↔ p.val + q.val ≤ 1` (then `r.val = p.val + q.val`), else `sumExceedsOne (p.val + q.val)`; it is commutative; `add p (complement p) = .ok one`. W: `add (1/2) (1/2) = .ok one`; `add (2/3) (2/3)` refuses.
- **PR6** `bayes prior like likeNot = .ok r ↔ evidence ≠ 0`; then `r.val · evidence.val = prior.val · like.val` (the defining equation of Bayes' rule) and `r.val = prior·like / (prior·like + (1−prior)·likeNot)`. `evidence.val = prior·like + (1−prior)·likeNot`. W: prior 1/100, `like` 99/100, `likeNot` 5/100 gives posterior 1/6; prior 1/2, `like = likeNot = 0` gives `zeroEvidence`.
- **PR7** Bayes boundaries (when the evidence is non-zero): `prior = 0` gives posterior 0; `prior = 1` gives posterior 1; `like = likeNot` gives posterior = prior (evidence that does not discriminate changes nothing); `likeNot = 0` and `like > 0` gives posterior 1. W: prior 1/2, `like` 1, `likeNot` 0 gives 1; prior 1/3, `like = likeNot = 1/2` gives 1/3.
- **PR8** `conditional joint marginal = .ok r ↔ marginal ≠ 0 ∧ joint ≤ marginal`, then `r.val · marginal.val = joint.val`; refusals `zeroMarginal`, `jointExceedsMarginal` otherwise. W: joint 1/4 marginal 1/2 gives 1/2; joint 3/4 marginal 1/2 refuses.
- **PR9** (Bayes agrees with conditioning) `bayes prior like likeNot = conditional (mul prior like) (evidence prior like likeNot)`. W: the PR6 witness.
- **PR10** the order on `Prob` is a total order: reflexive, transitive, antisymmetric (`p ≤ q → q ≤ p → p = q`, by `Prob.ext`), total. W: `1/3 ≤ 1/2`, not `1/2 ≤ 1/3`.

### Fixed point
- **FX1** `Scale.make n lim` refuses `zeroScale` for `n = 0` and `scaleTooLarge n lim.maxScale` for `n > lim.maxScale`; else a scale with that `n`. W: `make 1000000` ok; `make 0`; `make (10^18 + 1)` refuses.
- **FX2** `toScaled sc p ≤ sc.n`; `toScaled sc zero = 0`; `toScaled sc one = sc.n`. W: scale 10, `p = 1/3` gives 3.
- **FX3** (the proved error bound) `2 · |toScaled sc p · p.den − p.num · sc.n| ≤ p.den`, that is `|toScaled sc p / sc.n − p.val| ≤ 1/(2·sc.n)`: the rounding error is at most half a unit. W: scale 10^6, `p = 1/3` gives 333333 (error 1/3 unit); `p = 1/2000000` gives 1 (a tie, error exactly half a unit: the bound is attained, so it cannot be tightened).
- **FX4** `toScaled` is monotone: `p ≤ q → toScaled sc p ≤ toScaled sc q`. W: scale 10: `1/3 ≤ 1/2`, 3 ≤ 5.
- **FX5** `ofScaled sc k = .ok p ↔ k ≤ sc.n`, then `p.val = k / sc.n` EXACTLY; else `scaledAboveScale k sc.n`. W: scale 10^6, 250000 gives 1/4; 1000001 refuses.
- **FX6** `toScaled sc` after `ofScaled sc` is the identity: `ofScaled sc k = .ok p → toScaled sc p = k`. W: scale 10^6, 250000.
- **FX7** (`ofScaledInt`) refuses `belowZero` for a negative integer and `aboveOne` above the scale, else agrees with `ofScaled`. W: scale 10: -1, 0, 10, 11.
- **FX8** (largest remainder, the sum) `apportion sc ws = .ok vs → Σ vs = sc.n` and `vs.length = ws.length`. W: scale 10, `[1,1,1]` gives `[4,3,3]` (sum 10).
- **FX9** (largest remainder, within one unit) for every index, `vsᵢ · W − wsᵢ · n` lies strictly between `−W` and `W`: that is, `vsᵢ` is `⌊wsᵢ·n/W⌋` or `⌈wsᵢ·n/W⌉`, so it is within one unit of the exact proportion; and `vsᵢ = 0` when `wsᵢ = 0`. W: scale 10, `[1,2,4]` gives `[1,3,6]` (exact proportions 1.43, 2.86, 5.71).
- **FX10** `apportion` refuses `zeroTotalWeight` exactly when every weight is 0 (or the list is empty). W: `[]` and `[0,0]` refuse; `[0,1]` at scale 5 gives `[0,5]`.
- **FX11** (ties) for two indices `i < j` with equal weights `wsᵢ = wsⱼ`, `vsᵢ ≥ vsⱼ` (the earliest index wins a tie on the remainder). W: scale 2, `[1,1,1]` gives `[1,1,0]`.
- **FX12** (idempotence) if `Σ ws = sc.n` then `apportion sc ws = .ok ws`. W: scale 4, `[1,2,1]`; and a case with `Σ ≠ n`.
- **FX13** (distribution level) `Dist.toScaled sc d` has `Σ weights = sc.n`, the keys of `d` in order, and for every atom `|weight/n − p| < 1/n`. W: three atoms of 1/3 at scale 10^6 give `333334, 333333, 333333`.
- **FX14** `Dist.ofScaled lim sc ws = .ok d` iff the weights sum to `sc.n` (and the keys are strictly increasing, and the limits hold); then `d` has probability `wᵢ / n` at each key with `wᵢ > 0`. Refuses `scaledSumNotScale`. W: scale 10, `[(1,4),(2,3),(3,3)]` ok; `[(1,4),(2,3)]` refuses with sum 7.

### Distribution
- **DS1** (construction) `Dist.make lim atoms = .ok d → d.atoms = atoms`, and it refuses, in the stated order, each of `tooManyAtoms`, `numberTooLarge`, `emptyDist`, `keysNotIncreasing i`, `zeroAtom i`, `atomSumNotOne s`; the refusals are complete: if none applies, it is `.ok`. W: the atoms 1/4, 1/2, 1/4 at keys 100, 200, 300 are accepted; one case per refusal.
- **DS2** (extensionality) `Dist.ext : a.atoms = b.atoms → a = b`. W: two constructions of the same atoms are equal.
- **DS3** (`point`) `point a` has the one atom `(a, 1)`; its mean is `a`, every cdf at `x ≥ a` is 1, and below `a` is 0. W: `point 7` over `Int`.
- **DS4** (`canon`) for every input list, the output keys are strictly increasing, the total weight is unchanged, and the weight at every key is the sum of the input weights at that key; the output is a fixed point (`canon (canon ws) = canon ws`). Proved from `mergeSort_perm` and `pairwise_mergeSort` (with the total, transitive `le` on keys), never by evaluation. W: input `[(3,1),(1,1),(3,1),(2,1)]` gives `[(1,1),(2,1),(3,2)]` (by `simp [List.mergeSort]`); an already sorted input is unchanged (by `mergeSort_of_pairwise`).
- **DS5** (`normalize`) the result's probabilities sum to exactly 1 (the type says so); the probability at each key is `weight(key) / W`; zero-weight keys are absent; it refuses `negativeWeight i` for the first negative weight and `zeroTotalWeight` iff all weights are 0; if the weights already sum to 1 and have strictly increasing keys and positive values, `normalize` agrees with `make`; scaling all weights by `c > 0` does not change the result. W: weights 1, 2, 1 at keys 100, 200, 300 give 1/4, 1/2, 1/4; weights 1, 1, 1 give 1/3 each; one weight `-1` refuses.
- **DS6** (`mass`) `mass d (fun _ => true) = one`; `mass d (fun _ => false) = zero`; mass of a disjoint union adds: `mass d (e ∨ e') = mass d e + mass d e'` when no atom satisfies both; `mass d (¬e) = complement (mass d e)`. W: A (vectors) with `e = (≥ 200)` has mass 3/4, and `¬e` has mass 1/4.
- **DS7** (`cdf`) `cdf` is monotone (`x ≤ y → cdf x ≤ cdf y`); `cdf x = zero` below the least key; `cdf x = one` at and above the greatest key; `cdf` is right-continuous in the sense that `cdf x = cdf k` for the greatest key `k ≤ x`. W: cdf of A at 99, 100, 150, 200, 300 is 0, 1/4, 1/4, 3/4, 1.
- **DS8** (`quantile` total) for `0 < q ≤ 1`, `quantile d q = .ok k` with `k ∈ support d`; it refuses `levelNotPositive q` for `q ≤ 0` and `levelAboveOne q` for `q > 1`. W: A at `q = 1` gives 300; `q = 0` and `q = 11/10` refuse.
- **DS9** (the quantile/cdf Galois property) for `0 < q ≤ 1` and `quantile d q = .ok k`: for EVERY `x : α` (a key or not), `q ≤ (cdf d x).val ↔ k ≤ x`. Consequences: `k` is the smallest key with `q ≤ cdf k`; `quantile` is monotone in `q`; `cdf (quantile q) ≥ q`; and `x < k → cdf x < q`. W: A at `q = 1/4` gives 100 (`cdf 100 = 1/4 ≥ q`; `cdf 99 = 0 < q`); at `q = 1/3` gives 200 (the edge `q` strictly between two cdf values).
- **DS10** (`expect`) is linear: `expect d (f + g) = expect d f + expect d g`, `expect d (c·f) = c · expect d f`, `expect d (fun _ => c) = c`; monotone in `f`; `mean (point a) = a`. W: the mean of 1/3 each at keys 1, 2, 3 is 2.
- **DS11** (`mixture`, the sum) when `mixture lim lam a b = .ok d`, the probabilities of `d` sum to 1 (the type says so) and at every key `k`: `d(k) = (1−lam)·a(k) + lam·b(k)` (with `a(k) = 0` off the support). W: A, B, `lam = 1/2` (vectors).
- **DS12** (`mixture`, the ends) `lam = zero → mixture = .ok a`; `lam = one → mixture = .ok b` (equal as values, by `Dist.ext`); `mixture lam a b = mixture (complement lam) b a`; `mixture lam a a = a`. W: A, B at `lam` 0 and 1.
- **DS13** (`mixture`, the mean) `mean (mixture lam a b) = (1−lam)·mean a + lam·mean b`, and the same for `expect` of any `f`. W: A has mean 200, B has mean 250, `lam = 1/2` gives 225, `lam = 1/4` gives 425/2.
- **DS14** (`mixture`, the refusal) `mixture` refuses `tooManyAtoms` iff the union of the supports exceeds the limit, and `numberTooLarge` for an oversized weight. W: a limit `maxAtoms = 3` with A (3 keys) and B (keys inside A's) is ok; with a B that has a fourth key it refuses.
- **DS15** (`map`) `mass (map f d) e = mass d (e ∘ f)`; `expect (map f d) g = expect d (g ∘ f)`; `map id d = d`; `map g (map f d) = map (g ∘ f) d`; a constant `f` gives a point; if `f` is strictly increasing, `map f d = mapMono f d` and `size (map f d) = size d`. W: A mapped by `f k = k / 200` (integer division) gives 0 with 1/4 and 1 with 3/4 (two keys merged, the sum kept).
- **DS16** (`shift`) `shift c d` has the atoms `(a + c, p)` in the same order; `mean (shift c d) = mean d + c`; `cdf (shift c d) (x + c) = cdf d x`; `shift 0 d = d`; `shift c (shift c' d) = shift (c + c') d`. W: A shifted by 5 has keys 105, 205, 305; the hypothesis holds for `Int` and `Rat` (`Int.add_lt_add_right`, `Rat.add_lt_add_right`).
- **DS17** (`condition`) `condition d e = .ok d'` iff `mass d e ≠ 0` (else `nullEvent`); then `mass d' e = one`, `d'(k) = d(k) / mass d e` for each key with `e k`, and 0 (absent) elsewhere; `condition d (fun _ => true) = .ok d`; `mass d' e' = mass d (e ∧ e') / mass d e` for every event `e'`; conditioning on `e` and then on `e'` is conditioning on `e ∧ e'`. W: A on `(≥ 200)` gives 200 with 2/3 and 300 with 1/3; on `(> 300)` it refuses `nullEvent`.

### Reflection of the family's rule
- **RL1** (no float, no second ratio) a Tier 1 scan: the string `Float` does not occur in `VbmProb/`, and no `structure` in `VbmProb/` has fields `num` and `den`. This is a LIST of what the scan refuses, with its self-test (a file with `Float` is flagged); it is not a Lean theorem.

## Known-answer vectors
Plain text; each becomes a Lean `example` (or a proved theorem in `VbmProbProofs/Vectors.lean`) in the last slice, and each states the exact result. `A` is the distribution 100 ↦ 1/4, 200 ↦ 1/2, 300 ↦ 1/4; `B` is 200 ↦ 1/2, 300 ↦ 1/2 (keys `Int`, `Limits.default`).

**Probability**
```
make 1/2            -> ok 1/2          make 0, make 1 -> ok
make -1/2           -> belowZero (-1/2)    make 3/2 -> aboveOne (3/2)
ofFrac 1 0          -> denominatorZero     ofFrac 5 4 -> aboveOne (5/4)
complement 1/4      -> 3/4             mul 1/2 1/3 -> 1/6
add 1/2 1/2         -> ok 1            add 2/3 2/3 -> sumExceedsOne (4/3)
bayes prior=1/100 like=99/100 likeNot=5/100 -> ok 1/6
bayes prior=1/2 like=0 likeNot=0            -> zeroEvidence
bayes prior=1/2 like=1 likeNot=0            -> ok 1
bayes prior=1/3 like=1/2 likeNot=1/2        -> ok 1/3
conditional joint=1/4 marginal=1/2          -> ok 1/2
conditional joint=3/4 marginal=1/2          -> jointExceedsMarginal
conditional joint=0   marginal=0            -> zeroMarginal
```
**Fixed point** (`toScaled` at the stated scale; ties up)
```
scale 10^6: 1/3 -> 333333     2/3 -> 666667     0 -> 0     1 -> 1000000
scale 10^6: 1/2000000 -> 1    (tie, rounds up)
scale 10:   1/3 -> 3          scale 1: 1/2 -> 1     scale 1: 1/4 -> 0
ofScaled 10^6 250000  -> ok 1/4        ofScaled 10^6 1000001 -> scaledAboveScale 1000001 1000000
ofScaledInt 10 (-1)   -> belowZero (-1/10)    ofScaledInt 10 11 -> aboveOne (11/10)
Scale.make 0 -> zeroScale      Scale.make (10^18+1) -> scaleTooLarge (10^18+1) (10^18)
```
**Largest remainder** (`apportion scale weights`)
```
10   [1,1,1]  -> [4,3,3]            10  [1,2,4] -> [1,3,6]
10   [1,2,1]  -> [3,5,2]            1000 [3,8,5] -> [188,500,312]
10^6 [1,1,1]  -> [333334,333333,333333]
5    [0,1]    -> [0,5]              2   [1,1,1] -> [1,1,0]   (tie: earliest first)
4    [1,2,1]  -> [1,2,1]            10  [0,0]   -> zeroTotalWeight     10 [] -> zeroTotalWeight
```
**Distributions**
```
make [(1,1/2),(1,1/2)]            -> keysNotIncreasing 1
make [(2,1/2),(1,1/2)]            -> keysNotIncreasing 1
make [(1,1/2)]                    -> atomSumNotOne 1/2
make []                           -> emptyDist
make [(1,0),(2,1)]                -> zeroAtom 0
make [(100,1/4),(200,1/2),(300,1/4)] -> ok A
normalize [(100,1),(200,2),(300,1)]  -> A           (weights 1,2,1)
normalize [(1,1),(2,1),(3,1)]        -> 1/3 each
normalize [(1,0),(2,3)]              -> point 2     (zero weight dropped)
normalize [(3,1),(1,1),(3,1),(2,1)]  -> 1 ↦ 1/4, 2 ↦ 1/4, 3 ↦ 1/2   (sorted, merged)
normalize [(1,1),(2,-1)]             -> negativeWeight 1
normalize [(1,0),(2,0)]              -> zeroTotalWeight
cdf A:  99 -> 0   100 -> 1/4   150 -> 1/4   200 -> 3/4   300 -> 1   1000 -> 1
quantile A:  1/1000 -> 100   1/4 -> 100   1/3 -> 200   3/4 -> 200   4/5 -> 300   1 -> 300
quantile A:  0 -> levelNotPositive 0   -1/2 -> levelNotPositive (-1/2)   11/10 -> levelAboveOne (11/10)
mean A -> 200      mean B -> 250
mixture 1/2 A B -> 100 ↦ 1/8, 200 ↦ 1/2, 300 ↦ 3/8     mean 225
mixture 1/4 A B -> 100 ↦ 3/16, 200 ↦ 1/2, 300 ↦ 5/16   mean 425/2
mixture 0 A B -> A      mixture 1 A B -> B
mixture (maxAtoms = 3) 1/2 A (B with a fourth key) -> tooManyAtoms 4 3
map (k ↦ k / 200) A    -> 0 ↦ 1/4, 1 ↦ 3/4
shift 5 A              -> 105 ↦ 1/4, 205 ↦ 1/2, 305 ↦ 1/4
condition (k ≥ 200) A  -> 200 ↦ 2/3, 300 ↦ 1/3          condition (k > 300) A -> nullEvent
toScaled 10^6 A        -> [(100,250000),(200,500000),(300,250000)]
toScaled 10^6 (1/3 each over keys 1,2,3) -> [(1,333334),(2,333333),(3,333333)]
ofScaled 10 [(1,4),(2,3),(3,3)]  -> 1 ↦ 2/5, 2 ↦ 3/10, 3 ↦ 3/10
ofScaled 10 [(1,4),(2,3)]        -> scaledSumNotScale 7 10
```
(The vectors that sort run through `simp [List.mergeSort]` or are proved for the already sorted form; none relies on `decide` for a `Rat` or a sort.)

## Out of scope (they belong to other libraries; not specified here)
- **Scoring rules, calibration, reliability, resampling, forecast events** — the forecast-verification library. It builds on `Prob` and `Dist`.
- **Sampling and seeds** — the seeded-random library. It draws from a `Dist` through its own interface, reading `atoms` and `cdf`/`quantile`; this library contains no generator and takes no seed.
- **Decoding and encoding decimal strings, exponents, the wire's decimal limits** — the decision-model library (`Decimal`, `maxExponent`, `stripZeros`, the decimal tolerance policy). This library gives it `Prob.ofFrac`, `ofScaled`, `toScaled`.
- **Any domain type** — prices, quantities, money, units, dates, crops, marketing years. A domain distribution is a `Dist` over a key type of the consumer plus the consumer's own tag (for example a unit), kept in the consumer.
- **Input and output, storage, network, any model call, floating point.**
- **Variance, entropy, divergence, continuous distributions, joint/product distributions** — not needed by the four consumers; a later item if one needs them.

## The reconciliation
The inventory of the four incubations, each definition with WHERE IT LANDS or WHY IT STAYS. "Lands" means this library provides the one definition and the consumer deletes its own after migration.

### Decision-model library: probabilities as scaled decimals (`Prob.lean`)
| Definition | Disposition |
|---|---|
| `scale` (10^6) | LANDS as `Scale.million`; the consumer keeps no constant. |
| `Prob` (scaled structure) | LANDS as `Prob` (exact `Rat`); the wire's parts-per-million is `toScaled`/`ofScaled` at `Scale.million`. |
| `Decimal` | STAYS: decoding a decimal off the wire is the decision library's. |
| `ScaleRefusal` | STAYS for decimal-specific refusals (exponent, digits); the probability range and scale refusals map to `Refusal`. |
| `maxExponent` | STAYS (a decimal-wire limit). |
| `numer`, `denom` | STAY (a decimal to a fraction); their output feeds `Prob.ofFrac`. |
| `toScaled` (Decimal to scaled Nat) | STAYS as the decoder; it becomes `Prob.ofFrac (numer d) (denom d)` then `toScaled`. `[open question]`: the incubation's rounding or refusal of an inexact decimal is not given here; its code decides, and the migration item checks it against FX3. |
| `stripZeros`, `toDecimal` | STAY (encoding for the wire); `toDecimal` takes `toScaled` of `Prob`. |
| `ofDecimal` (Decimal to Prob) | STAYS as the decoder, returning the exact `Prob` through `ofFrac`. |
| `entryError`, `sumEpsilon`, `SumOk` (+ its `Decidable`) | STAY: a tolerance policy for rounded entries is the wire's, not an arithmetic fact; the exact check (`tolerance 0`) is `Dist.ofScaled`, and after `SumOk` a consumer repairs the sum with `apportion`. |

### Forecast-verification library: ratio and representations (`Rep.lean`)
| Definition | Disposition |
|---|---|
| `Scale` (abbrev Nat) | LANDS as `Scale` (positive). |
| `Ratio`, `le`, `eqv`, `add` | LAND as `Rat` and its `≤`, `=`, `+` (the canonical form makes `eqv` the equality). |
| `RawProb` (Int) | STAYS (the wire integer before validation); validated by `ofScaledInt`. |
| `BinaryEvent`, `CategoricalEvent`, `OrderedEvent`, `QuantileEvent`, `IntervalEvent` | STAY (forecast domain forms); their probability fields become `Prob`/`Dist` (a categorical or ordered forecast is a `Dist` over outcome indices). |
| `Refusal` (forecast) | STAYS; it gains one constructor wrapping this library's `Refusal`. |
| `Limits`, `limitEvents`, `limitOutcomes`, `limitBins`, `limitResamples` | STAY (forecast limits: events, outcomes, bins, resamples); the outcome count reuses `maxAtoms` as its value. |
| `IncFrom`, `StrictInc`, `incFromB`, `strictIncB` | LAND as core's `List.Pairwise (· < ·)` and its `Decidable` instance (no definition of ours either); the four are deleted. |
| `sumInt` | LANDS as core's `List.sum`; deleted. |
| `checkScale` | LANDS as `Scale.make`. |
| `checkProbsFrom`, `checkProbs` | LAND per element as `ofScaledInt` (the consumer adds the index to its own refusal). |
| `checkNormalised` (with tolerance) | STAYS (tolerance policy); its tolerance-0 case is `Dist.ofScaled`. |
| `checkOutcome`, `checkOutcomeCount`, `checkAligned`, `checkNonzero`, `checkSample`, `checkDraws`, `checkDrawsFrom` | STAY (forecast and resampling domain checks). |
| `checkIncreasing` | LANDS as `keysNotIncreasing` of `Dist.make`. |
| `checkLevel` | LANDS as the `quantile` level refusals. |
| `checkTail`, `checkInterval`, `checkEdges` | STAY (forecast semantics of tails, intervals and bin edges). |
| `validateBinary`, `validateCategorical`, `validateOrdered`, `validateQuantile`, `validateInterval` | STAY (compositions of checks); rewritten over `Prob`, `Dist`, `quantile`. |

### Product units module (`Units.lean`)
| Definition | Disposition |
|---|---|
| `UnitsError` | STAYS (domain refusals); `probOutOfRange` maps to `belowZero`/`aboveOne`. |
| `Money`, `add`, `neg`, `sub`, `ofCents`, `ofQuarterCents`, `Money.mulFloor` | STAY (money). |
| `Ratio`, `make`, `eqv`, `norm` | LAND as `Rat` (`Rat.divInt`, canonical form); the zero-denominator refusal stays as a `UnitsError`. |
| `Unit'`, `Quantity`, `Factors`, `convert`, `PricePerUnit`, `PricePerUnit.value` | STAY (domain). |
| `Prob` (ppm structure), `make`, `complement`, `mul`, `sum` | LAND as `Prob`, `ofScaled`/`Prob.make`, `complement`, `mul`, `add` (`sumExceedsOne`). The old `mul` rounds in parts per million; the new `mul` is exact and `toScaled` rounds once. `[open question]`: the old rounding rule is not given; the migration item compares. |
| `Date`, `isLeap`, `daysInMonth`, `make`, `toC`, `ofC`, `toDays`, `ofDays`, `addDays`, `diffDays`, `eraOk`, `marketingYear`, `Crop`, `Crop.marketingYear` | STAY (calendar and crops, not probability). |

### Product belief module (`Belief.lean`)
| Definition | Disposition |
|---|---|
| `All2` | STAYS as proof scaffolding or is replaced by core's `List.Forall₂`. |
| `Slot`, `sumFl`, `cntU`, `bestRem`, `bumpFirst`, `award`, `Inv`, `slotsOf`, `lrm` | LAND as `apportion` (the same method); the iterative slot machinery is an implementation detail of its proof and is not part of the interface. |
| `BeliefError` | STAYS for unit mismatch; the rest maps to `Refusal`. |
| `Dist` (with a unit tag and priced points) | LANDS as the generic `Dist α` over `Int` keys; the unit tag and `PricePerUnit` stay in a thin consumer wrapper. |
| `flatOf`, `toPts`, `build`, `Dist.make` | `make` LANDS as `Dist.make`; the three conversions between priced points and flat integer pairs STAY (domain). |
| `cdfN`, `Dist.cdf` | LAND as `cdf` (`Money` argument becomes the key). |
| `Dist.mean` | LANDS as `mean` (the exact `Rat` replaces the pair with 10^6). |
| `quantileAux`, `Dist.quantile`, `Dist.quantileAt` | LAND as `quantile` (the level is `Rat`; `quantileAt n` is `quantile (n / 10^6)`). `[open question]`: the old quantile takes a `Prob`, which includes 0; the new one refuses 0 (`levelNotPositive`). |
| `Dist.normalize` | LANDS as `normalize` (and `canon`). |
| `mergeF`, `mixW`, `mixture`, `mixMean` | LAND as `mixture` and `DS11`-`DS13` (the merge of two sorted lists is internal). |
| `Dist.shiftBy` | LANDS as `shift`. |
| `beliefA`, `beliefB`, `flatRes` | STAY as the consumer's fixtures (they become its vectors against this library). |

## Migration (expand and contract; small items for a steward to queue later)
Each item adds this library beside the old definition, migrates the callers, and deletes the old definition at zero references (hub rule). Each is a separate landing in the consumer's repository. Pin this library as a vendored dependency first (`land-pin`), after its first release.

1. **M0 (release)**: after slice S15, cut a release of `vbm-prob` so consumers can pin it.
2. **Belief module** (the biggest user; first):
   - M1: vendor `vbm-prob`; add a conversion between its `Dist` over `Int` keys and the module's `Dist`, and a vector test that the two agree on `beliefA`/`beliefB`.
   - M2: `lrm` to `apportion` (check the tie rule against FX11 and the vectors; `[open question]` above).
   - M3: `Dist.make`, `normalize`, `cdf`, `mean` to the library (callers first, then delete `cdfN`).
   - M4: `quantile` and `quantileAt` (level refusal difference), then delete `quantileAux`.
   - M5: `mixture`, `shiftBy`; delete `mergeF`, `mixW`, `mixMean`.
   - M6: delete `Slot`, `award`, `bumpFirst`, `bestRem`, `cntU`, `sumFl`, `Inv`, `slotsOf` at zero references; the module keeps the unit wrapper only.
3. **Units module**: M7: its `Prob` becomes `vbm-prob`'s `Prob` (callers of `ppm` use `toScaled`); M8: its `Ratio` becomes `Rat`; delete `make`, `eqv`, `norm`; M9: delete the old `complement`, `mul`, `sum` after callers use `complement`, `mul`, `add`.
4. **Decision-model library**: M10: vendor; `ofDecimal` returns the exact `Prob` through `ofFrac`; M11: `toDecimal` through `toScaled`; M12: replace the stored scaled `Prob` by this one at the call sites that hold a probability; keep `SumOk` and its tolerance and add the repair by `apportion`; M13: delete `scale` and the old `Prob` at zero references.
5. **Forecast-verification library**: M14: vendor; `Ratio` becomes `Rat` (callers, then delete `Ratio`, `le`, `eqv`, `add`); M15: `StrictInc`, `incFromB`, `strictIncB`, `IncFrom`, `sumInt` become core's `Pairwise` and `sum`; M16: `checkScale`, `checkProbs`, `checkIncreasing`, `checkLevel` become `Scale.make`, `ofScaledInt`, `Dist.make`, `quantile`; M17: categorical and ordered events carry a `Dist`.
6. **Seeded-random library**: M18: its sampler takes a `Dist` and reads `atoms`/`cdf` through this library's interface (no new definitions here for it).

## Slices
Each slice is about 150 production lines of Lean with its proofs and edits the shared files (`VbmProb.lean`, `VbmProbProofs.lean`, `VbmProbProofs/Ledger.lean`, the generated `docs/proof-ledger.md`), so the pool lands them ONE AT A TIME in the order below. The modules of different slices share no other file, so the dependency column is the real constraint: slices with no edge between them can be written in parallel by different workers and landed in any order that respects the dependencies. Behaviour lands behind the flag-off rule of the repository: the library is not linked by a consumer until M1, so each slice is dark by construction.

| Slice | Module | Content | Depends on |
|---|---|---|---|
| S1 | `VbmProb.Refusal`, `VbmProb.Limits` | `Refusal`, `Limits`, `Limits.default`, `Rat.bits` (with `bitLength`), `Key` class and instances for `Nat`, `Int`, `Rat` (order-law proofs, witnesses) | S0 |
| S2 | `VbmProb.Prob` | `Prob`, `ext`, `make`, `ofFrac`, `zero`, `one`, `complement`, `mul`, `add`, order; PR1-PR5, PR10 | S1 |
| S3 | `VbmProb.Prob.Bayes` | `evidence`, `bayes`, `conditional`; PR6-PR9 | S2 |
| S4 | `VbmProb.Scaled` | `Scale`, `Scale.make`, `million`, `toScaled`, `ofScaled`, `ofScaledInt`; FX1-FX7 | S2 |
| S5 | `VbmProb.Apportion` | `apportion` over `Nat` lists (largest remainder, earliest tie) and proofs FX8-FX12; no `Prob` needed | S1 |
| S6 | `VbmProb.Dist` | `Dist`, `ext`, `make`, `point`, `support`, `size`; DS1-DS3 | S2 |
| S7 | `VbmProb.Dist.Query` | `mass`, `expect`, `mean`, `cdf`; DS6, DS7, DS10 | S6 |
| S8 | `VbmProb.Dist.Quantile` | `quantile` and the Galois property; DS8, DS9 | S7 |
| S9 | `VbmProb.Dist.Canon` | `canon` (sort and merge) and DS4, from `mergeSort_perm` and `pairwise_mergeSort`; no `Dist` needed beyond `Key` | S1 |
| S10 | `VbmProb.Dist.Normalize` | `normalize`; DS5 | S6, S9 |
| S11 | `VbmProb.Dist.Mixture` | `mixture` and its sorted merge; DS11-DS14 | S7 |
| S12 | `VbmProb.Dist.Map` | `map`, `mapMono`, `shift`; DS15, DS16 | S7, S9, S10 |
| S13 | `VbmProb.Dist.Condition` | `condition`; DS17 | S7, S10 |
| S14 | `VbmProb.Dist.Scaled` | `Dist.toScaled`, `Dist.ofScaled`; FX13, FX14 | S4, S5, S10 |
| S15 | `VbmProbProofs.Vectors` and the Tier 1 scan RL1 | every vector above as a proved `example`; the RL1 scan with its self-test; the ledger closed (every label in this file has an obligation); `README.md`/`AGENTS.md` purpose wording aligned | S1-S14 |

Parallel groups (no edge between members): {S3, S4, S5, S6, S9} after S2 (S5 and S9 need only S1); {S7} then {S8, S11}; {S10} after S6 and S9; {S12, S13, S14} after their dependencies. Order for a one-at-a-time pool: S1, S2, S3, S4, S5, S9, S6, S7, S8, S10, S11, S12, S13, S14, S15. A slice that would exceed 150 lines or 45 minutes is stopped and decomposed (the repository's rule): the likely candidates are S5 (the proof of FX9) and S8 (DS9), which may each split in two (definition and sum; bound and ties).

## Open questions
1. Which core order-law classes `Key` should extend (the names in the pinned toolchain's `Init`); S1 reports.
2. The incubation's tie rule for the largest-remainder method is not given: this spec picks "earliest index first"; M2 compares vectors.
3. The incubation's rounding of a scaled product (units module) and of an inexact decimal (decision library) are not given: this spec rounds once, at `toScaled`, ties up; M7 and M10 compare.
4. The old quantile takes a `Prob` (0 allowed); this spec refuses level 0 (`levelNotPositive`) per the brief's "total on (0,1]".
5. The defaults of `Limits` (1024 atoms, 512 bits, scale 10^18) are chosen from the harms above, not measured; consumers may pass others.
6. `Dist.toScaled` on `Rat` probabilities: the spec says the numerators over a common denominator feed `apportion`; the slice may choose an equivalent integer-only form provided FX13 holds.
