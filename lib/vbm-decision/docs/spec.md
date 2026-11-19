# vbm-decision: specification

Status: written 2026-11-18, BEFORE any Lean (hub guideline: spec first). Version 1 of the contract. The next slices are written from this page by different workers in parallel; where this page and a slice disagree, this page wins and the slice is corrected.

## 1. What it is

A **decision model** is a model that is sent a **state** (text and, on some models, images, documents, audio or video) and one or more typed **questions**, and answers each question with a **typed result with probabilities**, never text and never reasoning. `vbm-decision` is the typed layer around such a model. It specifies:

- (a) the typed questions and the typed answers;
- (b) the exact decoding of the wire contract into them (and the encoding back); a sibling wire library does the bytes;
- (c) a **threshold truth table** that turns an answer into a decision and **fails closed**;
- (d) per-model **calibration** of thresholds from a labelled sample;
- (e) the **audit record** that every use can produce.

**Scope (from AGENTS.md).** Pure data and total functions over `Init`: no input or output, no network, no storage, no model call, no floating point, no clock, no randomness. Time and a random seed are INPUTS, never read. The library decides what this page says and nothing else; a boundary only moves bytes and never decides.

**What is trusted** (and marked in `docs/trust-ledger.md` when a slice needs it):
1. the provider's documentation of the wire contract (alpha: it can change between releases; every decoder refuses what it does not recognise);
2. the sibling wire library's bytes-to-`J` step (section 4.1), which is verified on its own;
3. the labelled sample handed to calibration (its labels are the caller's truth; the library cannot check them);
4. the caller's clock and seed inputs.

Nothing else is trusted: every other claim is a theorem (section 10).

## 2. Inputs and outputs

All functions are pure.

| Input | Type | Comes from |
|---|---|---|
| a decoded wire value | `J` (section 4.1) | the sibling wire library, from bytes |
| a question set | `Question` values (section 3.2) | the caller |
| thresholds | `Thresholds` bound to a model (section 5) | the caller, usually from calibration |
| a labelled sample | `List (Prob × Bool)` plus a target (section 6) | the caller |
| a time stamp | `Nat` (seconds, supplied) | the caller, only for the audit record |

| Output | Type |
|---|---|
| a typed request or response | `Request`, `Response` |
| a decision, an abstention or a refusal | `Outcome` |
| a threshold, or a refusal | `Except Refusal NoulThresholds` |
| an audit record, and its `J` form | `AuditRecord`, `J` |

Errors of the transport (HTTP 400 a request the model cannot serve, 401, 402 payment, 429, 5xx) are the BOUNDARY's and are not modelled here: this library takes a decoded answer or yields a typed refusal.

## 3. Core types

Lean names are in namespace `VbmDecision`. Strings are compared as exact byte sequences: no trimming, no case folding, no Unicode normalisation.

### 3.1 The probability representation (design question 1)

**Choice: `Prob` is a natural number of millionths, in `[0, 1000000]`.**

```
def scale : Nat := 1000000                       -- one, in millionths
structure Prob where  val : Nat   le : val ≤ scale   -- val / scale is the probability
structure Decimal where  neg : Bool  mantissa : Nat  exp : Int   -- ± mantissa × 10^exp, exactly
def Decimal.toScaled (d : Decimal) : Except RefusalCode Nat      -- the value times scale, exactly, or a refusal
def Prob.ofDecimal  (d : Decimal) : Except RefusalCode Prob      -- toScaled, then the range check
def Prob.toDecimal  (p : Prob) : Decimal                         -- mantissa val without trailing zeros, exp -6 (or 0), neg false; zero is {false, 0, 0}
```

Why millionths and not an exact rational: the provider's probabilities carry up to four decimals and zero as `0`; six decimals hold every such value exactly with room for a provider that prints six; the comparisons and sums of the truth table become `Nat` arithmetic that `omega` and `decide` close, which a rational (a gcd-normalised pair) would not; and a value has ONE representation, so equality of `Prob` is equality of probabilities and a record compares and round-trips structurally. Why not a rounded decimal: a rounded value is not what the provider said. So:

- `toScaled d`: if `mantissa = 0` the result is `0` (a signed zero is zero). Else if `neg` the refusal is `negative`. Else if `|exp| > maxExponent` the refusal is `exponentTooLarge` (named limit, so that `10^exp` is never computed for a huge `exp`). Else let `s = exp + 6`: if `s ≥ 0` the result is `mantissa × 10^s`; if `s < 0` and `10^(-s)` divides `mantissa` the result is `mantissa / 10^(-s)`; otherwise the refusal is `tooPrecise` (the decimal has more digits than six decimals hold: `0.1234567` is refused, `0.1234560` and `1.2345600e-1` are accepted because they are exactly 123456 millionths). Never rounded, never truncated.
- `Prob.ofDecimal d`: `toScaled` and then, if the result exceeds `scale`, `outOfRange`.
- Exactness theorem: whenever `Prob.ofDecimal d = ok p`, then `p.val × 10^(-6) = ± mantissa × 10^exp` as an equation of integers cross-multiplied (no division in the statement).

**The epsilon.** Exactly one rule compares a sum with one: **the sum rule** of a `choice` answer (over the options) and of a `score` answer (over the levels). A provider that prints each probability with four decimals (rounded or truncated) is off by less than `1e-4` = `100` millionths per entry; a sum of `n` entries is off by less than `100 × n`. So:

```
def entryError : Nat := 100                      -- millionths, per entry (named limit, section 8)
def sumEpsilon (n : Nat) : Nat := entryError * n
def SumOk (n : Nat) (ps : List Prob) : Prop := (ps.map Prob.val).sum + sumEpsilon n ≥ scale ∧ (ps.map Prob.val).sum ≤ scale + sumEpsilon n
```

with `n = ps.length`. The epsilon is per answer, scales with `n`, and is at most `100 × maxOptions` = 6400 millionths (0.64 percent). Every OTHER comparison (a threshold, a margin, a range) is exact on the reported values with no epsilon: the reported value is what is decided on; its distance from the model's true value (under 100 millionths) is the provider's, and the thresholds are calibrated on reported values (section 6), so the error is inside the calibration. The `score` position rule (section 3.3) has its own derived tolerance, stated there.

A position on a score scale uses the same scale: `Pos := Nat`, millionths of a level index (`x = 2.5` is `2500000`); it is not bounded by its type, its bound depends on the number of levels and is a check.

### 3.2 Questions (the request side)

```
structure Box where  top bottom left right : Prob        -- fractions of the image's height (top, bottom) and width (left, right) from the top-left corner

inductive Question where
  | noul   (instructions : String) (criteria : Option (String × String))   -- (text for true, text for false); optional as a whole
  | choice (instructions : String) (options : List (String × Option String)) -- option name, optional description; the order is the wire order
  | score  (instructions : String) (levels : List String)                     -- ordered, index 0 first
  | box    (instructions : String)
```

Well-formed question (`Question.Valid`, decided by `Question.check : Question → Except Refusal Unit`): a `choice` has between 2 and `maxOptions` options with distinct names (names non-empty); a `score` has between 2 and `maxLevels` levels; a `noul` with criteria has both texts. A box question has no `not found` answer.

A **state** is opaque to the library: `State := J`, valid iff it is an array (non-empty, at most `maxStateParts` elements, each a string or an object) or an object. The shape of a media part is the provider's and is not given here: `[open question 1]`; until it is answered the library passes a media part through untouched and never inspects it.

```
structure Request where
  model     : String                    -- "<maker>/<name>[-<version>]", exactly as sent; a non-empty maker without "/", then "/", then a non-empty remainder (else badModelName)
  state     : J
  questions : List (String × Question)  -- names non-empty and distinct; 1 to maxQuestions entries; wire order kept
```

The model string is NOT split into name and version (where the version begins is not given: `[open question 2]`). Everything keyed to a model is keyed to the whole requested string, plus the response's dated snapshot name (below).

### 3.3 Answers (the response side)

```
inductive Answer where
  | noul   (p : Prob)                                            -- the probability of yes
  | choice (selected : String) (probs : List (String × Prob)) (confidence : Prob)
  | score  (x : Pos) (confidence : Prob) (probs : List Prob) (legend : List String)   -- probs and legend by level index, 0 first
  | box    (b : Box) (confidence : Prob)

structure Usage where  inputTokens : Nat  outputTokens : Nat  cost : Decimal   -- cost: exact decimal dollars, never converted
structure Response where
  id : String   model : String   provider : String                -- model: the dated snapshot name
  answers : List (String × Answer)   usage : Usage
```

**Well-formed answer** (`WellFormed : Question → Answer → Prop`, decidable; `checkAnswer : Question → Answer → Except Refusal Unit` decides it and is proved equivalent):

- `noul`: always (its `Prob` is in range by type).
- `choice` with options `o₁..oₙ`: the `probs` keys are exactly the options, each once, in any order (else `unknownOption` / `missingOption` / `duplicateKey`); `SumOk n` of the probabilities (else `sumOffOne`); `selected` is a listed option (else `unknownOption`) and its probability is at least that of every other option (else `selectedNotMaximal`). The provider does not document that `selected` is the argmax; failing closed on a contradiction costs one refusal, deciding on it costs a wrong decision: `[open question 3]`.
- `score` with `n` levels: `probs.length = n` and `legend.length = n` (else `missingOption` / `unknownOption` with the index as the field); `legend` equals the question's levels entry by entry (else `legendMismatch`); `SumOk n`; `x ≤ (n-1) × scale` (else `scoreOutOfScale`); and the position matches the probabilities within a derived tolerance: `|x − Σ i·pᵢ| ≤ entryError × (n(n-1)/2 + 1)` (else `scoreInconsistent`): each `pᵢ` is off by under `entryError` and weighs at most `n-1`, summed over the indices gives `entryError × n(n-1)/2`, and `x` itself is printed with the same precision, `+ entryError`. `[open question 4]`: the provider says `x` is the probability-weighted position, not whether it is computed before rounding; the tolerance covers rounding only.
- `box`: `top ≤ bottom` and `left ≤ right` (else `boxInverted`), and in fact `top < bottom` and `left < right` (an empty or zero-area box is `boxEmpty`).

`Answer.kindOf` and `Question.kindOf` give a tag in `{noul, choice, score, box}`; an answer whose tag differs from its question's is `typeMismatch`.

## 4. The wire contract and its exact decoding (design: part b)

### 4.1 The decoded value `J`

The library cannot import `Lean` (AGENTS.md), so it owns the shape of a decoded JSON value; the sibling wire library maps the family's verified JSON codec to and from it, and that mapping is the one trusted step (a round trip proved there).

```
inductive J where
  | null | bool (b : Bool) | num (d : Decimal) | str (s : String)
  | arr (xs : List J) | obj (kvs : List (String × J))      -- an object is an ordered list; order and duplicates are preserved from the bytes
```

Decoder conventions, all of them typed refusals carrying the **field path** (a string like `answers.q1.probabilities.red`; `""` is the root; an array element is `[i]`):

- `wrongKind`: a value of another JSON kind than the field's (a string where an object is wanted; a JSON string `"0.5"` where a number is wanted: numbers are never read from strings).
- `missingField`: a required field is absent. `unknownField`: a field this page does not list for that object (a key outside the list is refused, the refusal names it; this includes a `reasoning` or `text` field on an answer). `duplicateKey`: the same key twice in one object, in any object.
- `unknownType`: a `type` tag outside `noul`, `choice`, `score`, `box`. `typeMismatch`: an answer whose tag is not its question's.
- a number: through `Prob.ofDecimal` (`negative`, `tooPrecise`, `outOfRange`, `exponentTooLarge`); a token count: a non-negative integer (`notNatural` otherwise).
- the score maps `probabilities` and `legend` have keys `"0"`, `"1"`, … in canonical decimal form (no sign, no leading zero, no space) covering exactly `0..n-1` (`badIndexKey` for a key that is not canonical; `missingOption` / `unknownOption` for a missing or extra index).

### 4.2 The request

```
{"model": <string>, "state": <array or object>, "questions": {"<name>": <question>, ...}}
```

`Request.encode : Request → Except Refusal J` (validates first; fields in the order `model`, `state`, `questions`) and `Request.decode : J → Except Refusal Request` (fields in any order; exactly these three).

A question is, on the wire (fields `type` and `instructions` always; `criteria` as shown; nothing else):

| type | `criteria` | notes |
|---|---|---|
| `noul` | optional object `{"true": <string>, "false": <string>}` (both keys when present) | `[open question 5]`: whether one key alone is legal |
| `choice` | required object, keys are the options, value a string or `null` | at least two keys, distinct (`duplicateKey` otherwise) |
| `score` | required array of strings, level 0 first | at least two |
| `box` | none (a `criteria` field is `unknownField`) | image question |

Encoding of a `null` description is `null`; an absent `criteria` on a `noul` is omitted, never `null`.

### 4.3 The response

```
{"id": <string>, "model": <string>, "provider": <string>, "answers": {"<name>": <answer>, ...},
 "usage": {"input_tokens": <nat>, "output_tokens": <nat>, "cost": <decimal>}}
```

`Response.decode : List (String × Question) → J → Except Refusal Response` takes the question set of the request (the answers can only be checked against the questions). It refuses an answer name that is not a question (`unexpectedAnswer`), a question without an answer (`missingAnswer`), and every field outside the list above (`unknownField`). `Response.encode : Response → J` is its inverse (section 10, W3). A response `answers` may hold fewer or more entries than the request only by being refused.

An answer is, on the wire (the fields listed and no others):

| type | fields |
|---|---|
| `noul` | `type`, `noul` (a probability) |
| `choice` | `type`, `choice` (a string), `probabilities` (object option to probability), `confidence` |
| `score` | `type`, `score` (a position: a decimal, millionths of an index), `confidence`, `probabilities` (object `"0"`.. to probability), `legend` (object `"0"`.. to string) |
| `box` | `type`, `box` (object with exactly `top`, `bottom`, `left`, `right`), `confidence` |

`Answer.decode : Question → J → Except Refusal Answer` does the structure, the numbers and then `checkAnswer`, so that **`decode` returns `ok a` only if `WellFormed q a`** (W2). Nothing is guessed: no field is defaulted, no number clamped, no key case-folded.

## 5. The threshold truth table (design question 2, part c)

### 5.1 Thresholds and decisions

```
inductive Thresholds where
  | noul   (no yes : Prob)                               -- valid iff no < yes
  | choice (minProb minMargin : Prob)
  | score  (lo hi : Pos) (minConfidence : Prob)           -- valid iff lo ≤ hi ≤ (n-1) × scale for the question's n
  | box    (minConfidence : Prob)

structure Binding where
  model : String                  -- the requested model string, exactly
  snapshot : Option String        -- some s: the response's dated snapshot must be s; none: any snapshot of `model`
  thresholds : Thresholds
structure Context where  requested : String  snapshot : String   -- what was sent and what the response says

inductive Decision where
  | yes | no                              -- noul
  | option (name : String)                -- choice
  | below | within | above                -- score, against the range [lo, hi]
  | found (b : Box)                       -- box
inductive AbstainReason where  | uncertainBand | lowProbability | lowMargin | lowConfidence
inductive Outcome where
  | decided (d : Decision) | abstain (r : AbstainReason) | refused (r : Refusal)
```

An **abstention is an answer of the table, not a default**: it means the model was heard and did not clear the bar; it carries its reason; the caller must treat it as "no decision" and never map it to `yes` or `no`. A **refusal** means the answer or the thresholds cannot be trusted at all.

Every threshold belongs to ONE model (and version): `Binding` carries the requested model string, and optionally the snapshot it was calibrated on (calibration, section 6, always pins the snapshot it saw). `[open question 6]`: whether a binding without a snapshot is acceptable in production (the provider says probabilities differ between models; it does not say how much between snapshots of one name).

### 5.2 The function

```
def decide (b : Binding) (c : Context) (q : Question) (a : Answer) : Outcome
```

Total: it is defined on every input and returns exactly one `Outcome`. In order, the first rule that applies wins:

1. `q` not valid, or `a` not well-formed for `q` (`checkAnswer`): `refused` with that refusal (this includes `typeMismatch`).
2. `b.model ≠ c.requested`: `refused modelMismatch`. `b.snapshot = some s` and `s ≠ c.snapshot`: `refused snapshotMismatch`.
3. The thresholds' kind differs from the question's: `refused thresholdKind`. The thresholds are not valid for `q` (`no ≥ yes`; `lo > hi`; `hi > (n-1) × scale`): `refused badThresholds`.
4. Otherwise, by kind (with `p`, `yes`, `no` all `val`):

| kind | rule |
|---|---|
| noul | `p ≥ yes` ⇒ `decided yes`; `p ≤ no` ⇒ `decided no`; else (`no < p < yes`) `abstain uncertainBand` |
| choice | let `ps` be the selected option's probability and `ru` the runner-up's (the largest probability among the other options; there are at least one); `ps < minProb` ⇒ `abstain lowProbability`; else `ps − ru < minMargin` ⇒ `abstain lowMargin` (the subtraction is exact in `Nat`: well-formedness gave `ps ≥ ru`); else `decided (option selected)` |
| score | `confidence < minConfidence` ⇒ `abstain lowConfidence`; else `x < lo` ⇒ `decided below`; `x > hi` ⇒ `decided above`; else `decided within` |
| box | `confidence < minConfidence` ⇒ `abstain lowConfidence`; else `decided (found b)` |

The `choice` `confidence` is carried to the audit record and is not used by the table in version 1. A tie for the selected option has margin 0: it is decided only if `minMargin = 0`.

**Fail closed** means exactly rule 1 to 3: a missing (`missingField`, `missingOption`, `missingAnswer`), malformed (`wrongKind`, `badIndexKey`, `duplicateKey`), out-of-range (`outOfRange`, `scoreOutOfScale`, `boxInverted`) or inconsistent (`sumOffOne`, `selectedNotMaximal`, `scoreInconsistent`, `legendMismatch`, `typeMismatch`) answer is a `refused`, never a decision and never an abstention.

## 6. Calibration (design question 3, part d)

### 6.1 Definitions

A sample is `List (Prob × Bool)`: the model's probability of yes on a case, and the case's true label (`true` is yes). The target `τ : Prob` is the minimum precision.

```
def countGE  (s : List (Prob × Bool)) (t : Prob) : Nat := (s.filter (fun e => t.val ≤ e.1.val)).length
def hitsGE   (s : List (Prob × Bool)) (t : Prob) : Nat := (s.filter (fun e => t.val ≤ e.1.val && e.2)).length   -- true positives at t
def Meets (s) (τ t : Prob) : Prop := minSupport ≤ countGE s t ∧ hitsGE s t * scale ≥ τ.val * countGE s t        -- precision ≥ τ, exactly, with enough support
```

Precision at `t` is `hitsGE / countGE` over the cases the rule `p ≥ t` would call yes. The comparison is cross-multiplied: no division, no rounding, no epsilon.

A **candidate** is the probability of some case of the sample (the precision only changes at a sample value, and a threshold between two sample values selects the same cases as the next one above).

```
def calibrateYes (s : List (Prob × Bool)) (τ : Prob) : Except Refusal Prob
```

1. `τ.val = 0`: `refused badTarget` (a target that is always met calibrates nothing).
2. `s.length < minSample`: `refused sampleTooSmall`. `s.length > maxSample`: `refused sampleTooLarge`.
3. fewer than `minPerClass` cases of either label: `refused sampleOneSided`.
4. no candidate meets: `refused noThresholdMeetsTarget`.
5. otherwise the **smallest candidate `t` with `Meets s τ t`**.

The result is used as the `yes` threshold (`p ≥ t` is yes). The mirror for the `no` side: `mirror s = s.map (fun (p, l) => (1 − p, !l))` and

```
def calibrateNo (s) (τ) : Except Refusal Prob := (calibrateYes (mirror s) τ).map (1 − ·)    -- the largest candidate u such that "p ≤ u is no" has precision ≥ τ on the false cases
def calibrateNoul (s) (τyes τno : Prob) : Except Refusal Thresholds
```

`calibrateNoul` returns `Thresholds.noul no yes` if both succeed and `no < yes`; if `no ≥ yes` the refusal is `bandInverted` (the sample cannot support two separate bars at those targets: raise a target or collect more data). The uncertain band `no < p < yes` is whatever remains between the two bars.

For a `choice`, `minProb` is calibrated by `calibrateYes` on the sample of (selected option's probability, whether the selected option was right); `minMargin` is NOT calibrated in version 1 (it is an explicit input, default 0). A `score` and a `box` are not calibrated in version 1 (`[open question 7]`).

A calibration result is wrapped, by the caller, into a `Binding` that pins the model string and the snapshot of the sample's cases (an input of the wrapper: `Binding.ofCalibration : String → String → Thresholds → Binding` sets `snapshot := some`).

### 6.2 What it does not claim

The target is met ON THE SAMPLE. The library claims nothing about the next case: a threshold with sample precision 0.95 does not make a future precision 0.95. The sample must be representative and correctly labelled: that is the caller's and is trusted (section 1). Randomness (a shuffle, a subsample) is never done here; a caller who must cut a larger sample passes a seed to its own selection and hands the result in.

## 7. The audit record (design question 4)

```
structure AuditRecord where
  specVersion : Nat                 -- this page's version: 1
  at : Nat                          -- seconds, supplied by the caller
  requested : String   snapshot : String   provider : String   responseId : String
  questionName : String   question : Question
  answer : Answer                   -- the probabilities returned (and the selected option, position or box)
  binding : Binding                 -- model, optional snapshot and the thresholds in force
  outcome : Outcome                 -- the decision, abstention or refusal
```

```
def audit (at : Nat) (req : Request) (resp : Response) (name : String) (b : Binding) : Except Refusal AuditRecord
def AuditRecord.toJ : AuditRecord → J
def AuditRecord.ofJ : J → Except Refusal AuditRecord
```

`audit` looks the question in `req.questions` and the answer in `resp.answers` under `name` (refusal `missingAnswer` / `unexpectedAnswer` when either is absent), sets `outcome := decide b ⟨req.model, resp.model⟩ q a`, and copies the rest. A refused decision still yields a record (its `outcome` is `refused`): the journal holds every use. `toJ` is canonical (fixed field order, a `Prob` as the `Decimal` of `Prob.toDecimal`); a journal stores `toJ`'s bytes through the wire library. A record holds no secret, no request state and no cost (the state may be private and is the caller's).

## 8. Named limits

Only limits that protect the machine or the money, or that prevent a named harm, exist. Each is a `def` in `VbmDecision/Limits` with its harm.

| Name | Value | Harm it prevents |
|---|---|---|
| `scale` | 1000000 | (a representation, not a limit) |
| `entryError` | 100 millionths | too small a value refuses honest four-decimal answers (a false refusal on every response); too large a value accepts a malformed answer |
| `maxQuestions` | 32 | a request that bills for dozens of questions at once by accident |
| `maxOptions` | 64 | unbounded work and an epsilon (`entryError × n`) that grows until the sum rule no longer checks anything (at most 6400 millionths) |
| `maxLevels` | 64 | the same, for a score scale |
| `maxStateParts` | 256 | a request whose state is an unbounded list of parts (money, memory) |
| `maxExponent` | 1000 | computing `10^exp` for a hostile exponent (time and memory) |
| `maxNestingDepth` | 32 | a hostile deeply nested `J` exhausting the stack in a decoder |
| `minSample` | 100 cases | **a threshold tuned on a handful of cases**: with ten cases a 90 percent precision is one error away from 80 and the smallest passing threshold is noise |
| `minPerClass` | 10 cases of each label | a sample with no negatives meets every target at every threshold: the threshold would be the lowest value, which decides nothing |
| `minSupport` | 30 cases at or above the threshold | a threshold chosen because the top two cases happened to be right (precision 100 percent on two cases) |
| `maxSample` | 10000 cases | unbounded work: the reference definition counts per candidate and is quadratic (at most 10^8 steps); a larger sample is cut by the caller |

The values are version 1 policy, chosen conservatively and not derived from a statistical bound; `[open question 8]` is whether `minSupport` should instead be a lower confidence bound on precision (an exact integer rule, for example a Wilson-type bound computed with integer square roots). Changing a value is a spec edit and a version bump.

## 9. Typed refusals

`Refusal` is a value, never a default: `structure Refusal where code : RefusalCode  field : String` (the path of section 4.1; for a threshold or a calibration the field is `thresholds` or `sample`).

| Group | `RefusalCode` |
|---|---|
| shape | `wrongKind`, `missingField`, `unknownField`, `duplicateKey`, `unknownType`, `typeMismatch`, `badIndexKey`, `nestingTooDeep` |
| numbers | `negative`, `tooPrecise`, `outOfRange`, `exponentTooLarge`, `notNatural` |
| request | `tooManyQuestions`, `noQuestions`, `badQuestionName`, `tooFewOptions`, `tooManyOptions`, `tooFewLevels`, `tooManyLevels`, `badModelName`, `badState`, `tooManyStateParts` |
| answer set | `missingAnswer`, `unexpectedAnswer` |
| answer | `unknownOption`, `missingOption`, `sumOffOne`, `selectedNotMaximal`, `scoreOutOfScale`, `scoreInconsistent`, `legendMismatch`, `boxInverted`, `boxEmpty` |
| thresholds | `thresholdKind`, `badThresholds`, `modelMismatch`, `snapshotMismatch` |
| calibration | `badTarget`, `sampleTooSmall`, `sampleTooLarge`, `sampleOneSided`, `noThresholdMeetsTarget`, `bandInverted` |

`RefusalCode` derives `DecidableEq`. Each code is reachable (a vector in section 11 or a slice test per code), and a code that no function can return is deleted. `Decimal.toScaled` returns a `RefusalCode`; the decoder adds the path. Nothing in the library has a default for a refused case: no `getD`, no clamp, no `0`.

## 10. Properties to prove

One sentence each; each names the slug for the obligation ledger (`VbmDecisionProofs/Ledger.lean`) and the **witness** that shows its hypotheses can hold (a concrete `example` closed by `decide`, `rfl` or `native`-free evaluation).

**Probability (slice S1a)**
- P1 `prob-ofdecimal-exact`: if `Prob.ofDecimal d = ok p` then `p.val` times the decimal's denominator equals the decimal's numerator times `scale` (exactness, no rounding). Witness: `0.1234560` gives `123456`.
- P2 `prob-toscaled-refuses-imprecise`: a decimal whose value is not a whole number of millionths yields `tooPrecise`. Witness: `0.1234567`.
- P3 `prob-roundtrip`: `Prob.ofDecimal (p.toDecimal) = ok p` for every `p`. Witness: `0`, `1`, `0.9731`.
- P4 `prob-range`: `Prob.ofDecimal d = ok p` implies `p.val ≤ scale`, and a value above one or negative is refused (`outOfRange`, `negative`). Witness: `1.000001` refused, `1` accepted.

**Truth table (slices S3, S4)**
- T1 `check-sound-complete`: `checkAnswer q a = ok ()` iff `WellFormed q a` (and `Question.check` likewise for `Valid`). Witness: a well-formed answer of each kind and one violating each rule.
- T2 `decide-total`: `decide` is a total function: for all inputs it returns an `Outcome` (provable by construction, stated and proved as `∀ b c q a, ∃ o, decide b c q a = o` with `o` classified as decided, abstain or refused by exactly one constructor). Witness: an evaluation of each constructor.
- T3 `fail-closed`: for every `q`, `a` with `¬ WellFormed q a`, `decide b c q a` is `refused` (for any `b`, `c`); and likewise for thresholds not valid for `q`, and for a binding of another model or snapshot. Witness: one malformed example per rule 1-3 gives the named refusal.
- T4 `noul-characterised`: for valid noul thresholds, `decide … = decided yes ↔ yes ≤ p`, `= decided no ↔ p ≤ no`, `= abstain uncertainBand ↔ no < p ∧ p < yes`. Witness: `no = 300000`, `yes = 800000`, with `p` at 300000, 300001, 799999, 800000.
- T5 `one-decision`: for valid noul thresholds the yes condition and the no condition never hold together (`¬ (yes ≤ p ∧ p ≤ no)`), so no input gets two decisions; a choice decision names exactly the selected option. Witness: the example above, plus the boundary `no + 1 = yes` (an empty band) still has no overlap.
- T6 `noul-monotone`: for fixed valid thresholds and `p ≤ p'`: `decide p = decided yes → decide p' = decided yes`, and `decide p' = decided no → decide p = decided no` (so raising the probability of yes never turns a `yes` into a `no`, nor into an abstention). Witness: `p = 800000 ≤ p' = 900000`.
- T7 `score-monotone`: for `x ≤ x'` and equal other inputs, `above` at `x` implies `above` at `x'`, and `below` at `x'` implies `below` at `x`. Witness: three levels, range [1.0, 2.0].
- T8 `threshold-monotone`: lowering the yes threshold (`yes' ≤ yes`, keeping `no < yes'`) never turns `decided yes` into anything else. Witness: `yes 800000 → 700000`.
- T9 `choice-characterised`: for a well-formed choice answer and valid thresholds, the outcome is `option selected` iff `minProb ≤ ps ∧ minMargin ≤ ps − ru`, and otherwise `abstain lowProbability` / `abstain lowMargin` in the order of section 5.2. Witness: three options (0.6, 0.3, 0.1) with `minProb 0.5`, `minMargin 0.2` and with `minMargin 0.4`.

**Calibration (slice S5)**
- C1 `calibrate-meets`: if `calibrateYes s τ = ok t` then `Meets s τ t`: precision at `t` on the sample is at least `τ` with the support required. Witness: a 100-case sample for which it returns a stated value (computed by `decide`).
- C2 `calibrate-minimal`: no candidate below `t` meets the target. Witness: the same sample, with the precision of the next candidate below shown to be under the target.
- C3 `calibrate-candidate`: `t` is the probability of some case of the sample. Witness: the same sample.
- C4 `calibrate-refuses`: `calibrateYes` refuses `sampleTooSmall` iff `s.length < minSample`; `sampleTooLarge` iff above `maxSample`; `sampleOneSided`; `badTarget` iff `τ = 0`; and `noThresholdMeetsTarget` exactly when the size checks pass and no candidate meets. Witness: a 99-case sample, a one-label sample, and a 100-case sample whose best precision is under the target.
- C5 `calibrate-order-free`: a permutation of the sample gives the same result. Witness: a sample and its reverse.
- C6 `calibrate-target-monotone`: for `τ ≤ τ'`, if `calibrateYes s τ' = ok t'` then `calibrateYes s τ = ok t` with `t ≤ t'`. Witness: the sample of C1 at two targets.
- C7 `calibrate-noul-valid`: if `calibrateNoul … = ok th` then `th` is valid noul thresholds (`no < yes`), so `decide` does not refuse it as `badThresholds`; and `bandInverted` arises exactly when `no ≥ yes`. Witness: a sample with a clean band, and one whose targets cross.

**Audit (slice S6)**
- A1 `audit-roundtrip`: for every `r : AuditRecord` that is valid (its question valid, its answer well-formed for it or its outcome refused), `AuditRecord.ofJ r.toJ = ok r`. Witness: one record per outcome constructor (decided, abstain, refused).
- A2 `audit-faithful`: `audit` yields a record whose `outcome` equals `decide` on the same arguments, whose `binding` is the thresholds passed in, and whose `answer` is the answer returned. Witness: the record of a noul decision.
- A3 `audit-total-on-refusal`: a refused decision still yields a record (`ok`), unless the name is absent from the request or the response. Witness: a malformed answer, recorded.

**Wire (slices S7a, S7b)**
- W1 `decode-refuses-unknown`: for every object kind of section 4, an extra key makes the decoder return `unknownField` naming it, and a duplicate key `duplicateKey`; a tag outside the four is `unknownType`. Witness: the `reasoning` vector of section 11.
- W2 `decode-wellformed`: `Answer.decode q j = ok a` implies `WellFormed q a`. Witness: the noul, choice, score and box vectors decode.
- W3 `message-roundtrip`: `Request.decode (Request.encode r) = ok r` and `Response.decode qs (Response.encode r) = ok r` for every valid `r` (wire order of questions and answers preserved). Witness: the vectors of section 11.
- W4 `decode-total`: every decoder is total: it returns `ok` or a typed `Refusal`, including on a `J` deeper than `maxNestingDepth` (`nestingTooDeep`). Witness: a vector nested 33 deep.

Totality of every function is also checked by the build (structural or well-founded recursion, no `partial`).

## 11. Vectors (shape only)

The documented provider examples are captured by slice S9; these constructed vectors fix the shapes now. The maker `acme` is made up.

```
V1 request   {"model":"acme/alpha-2026","state":["The invoice is overdue."],
              "questions":{"overdue":{"type":"noul","instructions":"Is the invoice overdue?"},
                           "tone":{"type":"choice","instructions":"Which tone?","criteria":{"calm":null,"angry":"hostile words"}},
                           "urgency":{"type":"score","instructions":"How urgent?","criteria":["none","some","high"]}}}
V2 response  {"id":"r1","model":"alpha-2026-11-01","provider":"acme-cloud",
              "answers":{"overdue":{"type":"noul","noul":0.9731},
                         "tone":{"type":"choice","choice":"calm","probabilities":{"calm":0.8,"angry":0.2},"confidence":0.8},
                         "urgency":{"type":"score","score":1.5,"confidence":0.7,"probabilities":{"0":0,"1":0.5,"2":0.5},"legend":{"0":"none","1":"some","2":"high"}}},
              "usage":{"input_tokens":12,"output_tokens":3,"cost":0.0004}}
```

| Vector | Input | Expected |
|---|---|---|
| V3 | `"noul":0.9731` with thresholds no 0.2, yes 0.9 | `decided yes` |
| V4 | `"noul":0.5` with the same | `abstain uncertainBand` |
| V5 | `"noul":1.2` | `refused outOfRange` at `answers.overdue.noul` |
| V6 | `"noul":0.1234567` | `refused tooPrecise` at `answers.overdue.noul` |
| V7 | `"noul":-0.1` | `refused negative` |
| V8 | choice `0.7`, `0.1` (sum 0.8, n = 2) | `refused sumOffOne` at `answers.tone.probabilities` |
| V9 | choice with `"choice":"happy"` | `refused unknownOption` at `answers.tone.choice` |
| V10 | noul answer plus `"reasoning":"..."` | `refused unknownField` at `answers.overdue.reasoning` |
| V11 | score `"score":2.5` on three levels (maximum 2) | `refused scoreOutOfScale` |
| V12 | box `{"top":0.6,"bottom":0.2,...}` | `refused boxInverted` |
| V13 | a `choice` answer to the `noul` question | `refused typeMismatch` |
| V14 | thresholds for model A, response from model B | `refused modelMismatch` |

## 12. Slices

Each slice is about 150 production lines of Lean with its proofs, lands behind no flag (pure definitions nothing calls yet; behaviour is only ever reached through a later slice), and adds its obligations to the ledger in the same commit. `VbmDecision/` imports `Init` and itself only; the proofs live in `VbmDecisionProofs/`. A slice that touches a file another slice touches is not parallel with it: the file lists below share nothing within a wave.

| Slice | Files (production) | Depends on | Wave | Contents |
|---|---|---|---|---|
| S1a | `VbmDecision/Prob.lean` | none | 1 | `scale`, `Prob`, `Decimal`, `toScaled`, `ofDecimal`, `toDecimal`, `SumOk`; P1-P4 |
| S1b | `VbmDecision/Refusal.lean`, `VbmDecision/Limits.lean` | none | 1 | `RefusalCode`, `Refusal`, every limit of section 8 (the values and their statement as `decide`d facts) |
| S2 | `VbmDecision/Types.lean` | S1a | 2 | `Box`, `Question`, `Answer`, `Usage`, `Response`, `Request`, `Thresholds`, `Binding`, `Context`, `Decision`, `AbstainReason`, `Outcome`, `J` and the kind tags (types only; no logic) |
| S5 | `VbmDecision/Calibrate.lean` | S1a, S1b | 2 | `countGE`, `hitsGE`, `Meets`, `calibrateYes`, `mirror`, `calibrateNo`, `calibrateNoul`; C1-C7 (needs `Thresholds.noul`: S2 lands the type first, or S5 states `calibrateNoul` over a local pair and S4's binding wraps it; the steward picks S2-first, it is about 40 lines) |
| S3 | `VbmDecision/Check.lean` | S1a, S1b, S2 | 3 | `Question.check`, `WellFormed`, `checkAnswer`, threshold validity; T1 |
| S4 | `VbmDecision/Truth.lean` | S3 | 4 | `decide`; T2-T9 |
| S7a | `VbmDecision/Decode.lean` | S2, S3 | 4 | `Question`/`Answer` decode and encode over `J`, the path, the unknown-field and duplicate-key rules; W1, W2, W4 (for these) |
| S7b | `VbmDecision/Message.lean` | S7a | 5 | `Request`/`Response` decode and encode; W3, W4 |
| S6 | `VbmDecision/Audit.lean` | S4, S7a | 5 | `AuditRecord`, `audit`, `toJ`, `ofJ`; A1-A3 |
| S8 | the sibling wire library (a separate repository `vbm-decision-wire`; may import `Lean`) | S7b (pinned by a release) | 6 | bytes to `J` and back on the family's verified JSON codec, `Decimal` from and to the number token (exact, no float); its own round-trip proof; the documented examples as vectors |
| S9 | `vectors/` and the conformance runner (in the wire library's tests or here, no network) | S7b, S8 | 7 | the real provider examples, captured once by hand and stored; each decodes, checks and decides as expected; every refusal code of section 9 is hit by at least one vector or an in-slice test; the run prints `ran: conformance: N cases` |

The parallel order and its justification:

- **Wave 1: S1a and S1b** share no file and depend on nothing: they can be written at once. S1a is the base of every type; S1b is the base of every function that can refuse.
- **Wave 2: S2 and S5** share no file; both need S1a (S5 also S1b). S2 is types only, so it is small and quick; S5 is independent of the truth table and of the wire (it works on `Prob` and `Bool` only) and carries the longest proofs, so it starts as early as possible.
- **Wave 3: S3** needs the types (S2) and the refusals (S1b); S5 may still be running.
- **Wave 4: S4 and S7a** share no file and both need only S3 (S4 for `WellFormed`, S7a for `checkAnswer` inside `Answer.decode`).
- **Wave 5: S7b and S6** share no file; S7b needs S7a; S6 needs S4 (`decide`) and S7a (the `J` forms of `Question` and `Answer`).
- **Wave 6: S8** can start its bytes-to-`J` half after S2 (the `J` type exists) and only needs S7b to be released for its vectors; the steward may start it at wave 3.
- **Wave 7: S9** needs the whole path. The capture of the real examples (no network from a test: they are stored files) has no code dependency and can be done by hand at any time.

The critical path is S1a, S2, S3, S7a, S7b, S9: six slices. S5, S4, S6 and S8 hang off it.

## 13. Open questions

1. The wire shape of a media part in `state` (an image, a document, audio, video): the field names and encodings are not given. The library passes parts through unread.
2. Where the version begins in `<maker>/<name>[-<version>]` (a name may contain `-`): the library keys everything on the whole string and the response's snapshot.
3. Whether the provider's `choice` is always the argmax of its `probabilities` (the library refuses when it is not).
4. Whether `score` is computed from the printed probabilities or before rounding (the tolerance of section 3.3 covers rounding only), and whether a `score` position can legitimately be printed outside `0..n-1`.
5. Whether a `noul` `criteria` may carry only one of `true` and `false`.
6. Whether a threshold binding without a pinned snapshot is acceptable in production, and how far probabilities move between snapshots of one name.
7. Whether `score` and `box` thresholds should be calibrated in a later version, and on which labels (a range, an intersection over union).
8. Whether `minSupport` should become an exact lower-confidence-bound rule rather than a count.
9. Whether the provider rounds or truncates to four decimals (the sum epsilon assumes the worse, truncation, 100 millionths per entry), and whether a `0` and a `1` are ever printed with other forms (`0.0`, `1.0`), which `Decimal` already accepts.
10. Whether a response can carry fields beyond those listed (a created time, a request id): the library refuses them as `unknownField`, and a release of the provider that adds one breaks decoding until this page is amended. This is deliberate for an alpha surface.
