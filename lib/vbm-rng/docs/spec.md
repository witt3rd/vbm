# vbm-rng: specification

Status: accepted for slicing. This file is written BEFORE any Lean (hub guideline: spec first). The Lean specification is the code in `VbmRng/`; this file says what it must be, concretely enough that each slice at the end can be written by a different worker in parallel without asking a question. Where a fact is not derived or verified here it is marked `[open question]` and listed in the last section before the slices.

## What it is
A pseudo-random source for simulation and experiments in which the same seed always gives the same output, bit for bit, on every machine, and which can be split into independent streams (one per simulated path, one per worker) with no shared state. It is general: nothing in it names a product.

The design is COUNTER-BASED on a BIJECTIVE 64-bit mixing function. A stream is a key and a position; its output number `i` is `mix (key + (position + i + 1) * gamma)` (all arithmetic modulo 2^64). Because `mix` is a bijection and the counter values are distinct, the property that matters is PROVED, not hoped for: within one stream no two outputs among any 2^64 consecutive outputs are equal (this is the largest range there is: there are only 2^64 words). There is no hidden state: every operation is a total pure function of the stream and the index, and `next` returns the output and the advanced stream.

The experiment-phase standard applies: exact deterministic integer arithmetic only; NO floating point anywhere in the specification, the code or the proofs; randomness is an input (a seed); time is an input (the library never reads a clock).

## Inputs and outputs
Scope: pure data and total functions over `Init`. No input or output, no network, no storage, no model call, no clock, no allocator across any boundary. A wire layer, if one is ever needed, is a separate sibling library; it decides nothing.

Inputs: a seed (`UInt64`), a child index (`UInt64`), a stream position or index (`UInt64`), a bound `n`, a number of bits `k`, a rational probability `num/den`, a list. Outputs: words (`UInt64`), bounded naturals, dyadic fractions, a shuffled list, a Boolean, the advanced stream, or a typed refusal.

Notation in this file: `⊕` is bitwise xor, `x >> s` is the logical right shift, `*` and `+` on `UInt64` wrap modulo 2^64 (this is what `UInt64` does in Lean), `Nat` is unbounded. Hexadecimal constants are written `0x...` with 16 digits.

## Types
```
structure Stream where        -- the whole state of a stream; two words, no hidden state
  key : UInt64                -- identifies the stream
  pos : UInt64                -- how many outputs have been consumed (wraps at 2^64)

inductive Refusal where       -- every way a primitive refuses; each a value, never a default
  | boundZero                 -- uniformBelow with n = 0
  | boundTooLarge             -- uniformBelow with n > 2^64 (also the bound of a Bernoulli denominator)
  | fractionBitsOutOfRange    -- uniformFraction with k = 0 or k > 64
  | probabilityDenominatorZero-- Bernoulli with den = 0
  | probabilityOutOfRange     -- Bernoulli with num < 0 or num > den
  | fuelExhausted             -- the rejection loop used all its fuel (see Named limits)

abbrev Draw (α : Type) := Except Refusal (α × Stream)   -- a value and the advanced stream, or a refusal

structure Fraction where      -- the exact dyadic rational  num / 2^bits
  num  : Nat
  bits : Nat
```

## The mixer (part M)

### Constants (all exact; each is stated, none is a guess)
```
gamma   = 0x9E3779B97F4A7C15     -- odd; the stream increment
mulA    = 0xBF58476D1CE4E5B9     -- odd
mulB    = 0x94D049BB133111EB     -- odd
shifts  = 30, 27, 31
splitSalt = 0x6A09E667F3BCC908   -- domain separation for split (the high 64 fractional bits of the square root of 2)
seedSalt  = 0xBB67AE8584CAA73B   -- domain separation for seeding (the same for the square root of 3)
```
Verification of the constants (not trusted on memory): `gamma`, `mulA`, `mulB` and the shifts are the published SplitMix64 constants; the reference model written from this file reproduces the published first outputs of the SplitMix64 generator started from state 0 (`0xE220A8397B1DCDAF`, `0x6E789E6AA1B965F4`, `0x06C45D188009454F`, `0xF88BB8A8724C81EC`), see the vectors. `splitSalt` and `seedSalt` are chosen here (any fixed values work for the proofs); they are `isqrt(2 * 2^128) mod 2^64` and `isqrt(3 * 2^128) mod 2^64`, which anyone can recompute. The three multipliers being odd is what the proofs use; `by decide` checks it.

### Functions
```
mix : UInt64 → UInt64
mix z =  let z := z ⊕ (z >> 30)
         let z := z * mulA
         let z := z ⊕ (z >> 27)
         let z := z * mulB
         z ⊕ (z >> 31)

unmix : UInt64 → UInt64        -- the proved inverse of mix
unmix z = let z := invXorShift 31 z
          let z := z * mulBInv
          let z := invXorShift 27 z
          let z := z * mulAInv
          invXorShift 30 z

invXorShift (s) (y) = y ⊕ (y >> s) ⊕ (y >> 2s) ⊕ ...   -- the terms while the shift is below 64
mulAInv  = 0x96DE1B173F119089   -- mulA * mulAInv = 1 (mod 2^64)
mulBInv  = 0x319642B2D24D8EC3   -- mulB * mulBInv = 1 (mod 2^64)
gammaInv = 0xF1DE83E19937733D   -- gamma * gammaInv = 1 (mod 2^64)
```
The inverse constants were computed as modular inverses; a slice checks each product by `decide` (the check, not this file, is the authority). `mix 0 = 0` (the mixer fixes zero): this is why a stream's key is never used raw for seeding (see below).

### Properties to prove (M)
- **M1 (xor-shift is invertible):** for `s` in 1..63, `invXorShift s (x ⊕ (x >> s)) = x` for all `x`. Witness: `x = 0x0123456789ABCDEF, s = 30`.
- **M2 (mix is a bijection, with its inverse):** `unmix (mix x) = x` and `mix (unmix y) = y` for all words. Witness: `unmix (mix 1) = 1` with `mix 1 = 0x5692161D100B05E5`.
- **M3 (mix is injective):** `mix x = mix y → x = y` (a corollary of M2). Witness: `mix 1 ≠ mix 2` (`mix 2 = 0xDBD238973A2B148A`).
- **M4 (multiplication by an odd constant is a bijection):** `x * gamma = y * gamma → x = y`, from `gamma * gammaInv = 1`. Witness: `gamma * gammaInv = 1` by `decide`.

## Streams, determinism and skip-ahead (part T)

### Functions
```
Stream.ofKey  (k : UInt64) : Stream := { key := k, pos := 0 }          -- a raw key, for tests and for split
Stream.ofSeed (s : UInt64) : Stream := Stream.ofKey (mix (s ⊕ seedSalt))   -- the seeding function

Stream.at (st : Stream) (i : UInt64) : UInt64 :=               -- output number i, by random access
  mix (st.key + (st.pos + i + 1) * gamma)

Stream.advance (st : Stream) (j : UInt64) : Stream := { st with pos := st.pos + j }   -- skip ahead

Stream.next (st : Stream) : UInt64 × Stream := (st.at 0, st.advance 1)
```
SEEDING. A seed becomes a key by `mix (seed ⊕ seedSalt)`: `mix` is a bijection, so DISTINCT SEEDS GIVE DISTINCT KEYS (proved, S1); seed 0 gives a non-zero key. The raw stream `Stream.ofKey 0` is exactly the published SplitMix64 generator from state 0 (the conformance link).

SKIP-AHEAD. `at` is random access: output `i` without computing any earlier one, in constant time. `advance` adds to the position, with wrap-around modulo 2^64: a stream has period 2^64 (output `i + 2^64` equals output `i`); nothing here consumes more than a few words per call, so a 2^64 wrap is not reachable in practice, and the properties below are stated for it.

### Properties to prove (T)
- **T1 (determinism):** `at`, `next`, `advance`, `ofSeed` are functions: equal arguments give equal results (this is immediate in Lean, and stated as a theorem over the named equations: `Stream.ofSeed s = Stream.ofSeed s' ↔ s = s'`, which needs M3). Witness: `(Stream.ofSeed 0).at 0 = 0xFAA2702D3A581CDC`.
- **T2 (no repeats, the full range):** for every stream `st` and indices `i ≠ j` (both `UInt64`), `st.at i ≠ st.at j`. So the first 2^64 outputs of a stream (indeed any 2^64 consecutive ones) are pairwise distinct, and `st.at` is a bijection from `UInt64` to `UInt64` (every 64-bit word appears exactly once per period). Proof shape: `i ↦ pos + i + 1` is a translation, `· * gamma` is a bijection (M4), `key + ·` is a translation, `mix` is a bijection (M2). Witness: `(Stream.ofKey 0).at 0 ≠ (Stream.ofKey 0).at 1`.
- **T3 (skip-ahead agrees with stepping):** `st.at (i + j) = (st.advance j).at i` for all `i, j` (modulo-2^64 addition). Witness: `(Stream.ofKey 1).at 8 = ((Stream.ofKey 1).advance 5).at 3 = 0x491718DE357E3DA8`.
- **T4 (next is at and advance):** `(st.next).1 = st.at 0` and `(st.next).2 = st.advance 1`; and `advance` composes: `(st.advance a).advance b = st.advance (a + b)`. Witness: `(Stream.ofKey 1).next` returns `0x910A2DEC89025CC1` with position 1.
- **T5 (seeds give distinct streams):** `s ≠ s' → (Stream.ofSeed s).key ≠ (Stream.ofSeed s').key`. Witness: seeds 0 and 1 (keys `0x86FA59FA943FE6F8`, `0x6DF8F8D77B172277`).

## Splitting (part P)

### Functions
```
childKey (k : UInt64) (c : UInt64) : UInt64 :=
  mix (mix (k ⊕ splitSalt) + (c + 1) * gamma)

Stream.split (st : Stream) (c : UInt64) : Stream := Stream.ofKey (childKey st.key c)
```
The child index `c` names the child; `split` depends on the parent's KEY only (not its position): the children of a stream are the same whenever they are asked for, which is what makes a tree of streams (path `c1, c2, ...`) reproducible. The inner `mix` with the salt keeps a child's key from being an output of the parent stream.

### Properties to prove (P)
- **P1 (distinct children):** for every key `k` and `c ≠ c'` (both `UInt64`), `childKey k c ≠ childKey k c'`; for all 2^64 child indices, the children have pairwise distinct keys. Witness: indices 0, 1, 2 and `2^64 - 1` of key `0x6DF8F8D77B172277` give `0xD0E6AA970FAF36DD`, `0xFDC79FB16B6BCA7E`, `0xB766FC3237EA4433`, `0xBF8F68540A6A4DFB`.
- **P2 (split is a function of the parent's key and the index):** `(st.split c)` equals `(st'.split c)` whenever `st.key = st'.key`. Witness: seed-1 stream at position 0 and at position 7, child 0.
- **P3 (children start at zero):** `(st.split c).pos = 0`.
- **QUALITY ASSUMPTION Q1 (trusted, NOT proved):** the streams of distinct children, and the outputs of different streams, behave as statistically independent sources. This is not provable in general; it is the same assumption every counter-based generator makes of its mixer. Q1 is recorded in `docs/trust-ledger.md` by the split slice and marked trusted in every statement that depends on it. What IS proved is only the distinctness of keys (P1); distinct keys do not imply disjoint streams (see Q2).
- **QUALITY ASSUMPTION Q2 (trusted, NOT proved):** two streams with different keys `k`, `k'` are windows on the SAME cycle of 2^64 values (the one `mix (· * gamma)` walks), shifted by `(k' - k) * gammaInv` positions; they share outputs exactly when their windows overlap. With keys derived by `mix`, treated as uniformly spread (Q1), the chance that two streams of length `L` overlap is about `2 L / 2^64` per pair; for `m` streams of length `L` about `m^2 L / 2^64`. Users must keep `m^2 L` far below 2^64 (this is the document's honest bound; the library does not enforce it).

## Uniform bounded integers (part U)

### Functions
```
rejectionFuel : Nat := 64                       -- the named limit (see below)
maxBound      : Nat := 2^64                     -- the largest n accepted

threshold (n : Nat) : Nat := 2^64 % n           -- words below this are rejected

uniformBelowWith (fuel : Nat) (n : Nat) (st : Stream) : Draw Nat
  -- n = 0                      → refuse boundZero
  -- n > 2^64                   → refuse boundTooLarge
  -- otherwise draw words w₀, w₁, ... = st.at 0, st.at 1, ... in order; the first wᵢ with
  --   i < fuel and wᵢ ≥ threshold n is accepted and the result is  (wᵢ mod n,  st.advance (i+1))
  -- if all `fuel` words are below the threshold → refuse fuelExhausted

uniformBelow (n : Nat) (st : Stream) : Draw Nat := uniformBelowWith rejectionFuel n st
```
The result is `< n`. The advanced stream's position is exactly the number of words consumed (one more than the number of rejected words).

WHY IT IS EXACT. `threshold n = 2^64 mod n`, so the number of accepted words, `2^64 - threshold n`, is a multiple of `n`; the accepted words `[threshold n, 2^64)` are mapped by `w ↦ w mod n`, and every residue in `[0, n)` has exactly `(2^64 - threshold n) / n` preimages among them. There is no modulo bias, and no scaled-multiplication approximation.

### Properties to prove (U)
- **U1 (the result is in range):** if `uniformBelowWith fuel n st = .ok (v, st')` then `v < n`, and `0 < n ≤ 2^64`. Witness: `uniformBelow 10 (Stream.ofSeed 1) = .ok (0, _)`.
- **U2 (exactness):** for `0 < n ≤ 2^64` and every `v < n`, the number of words `w < 2^64` with `w ≥ threshold n` and `w mod n = v` equals `(2^64 - threshold n) / n`, the same for every `v`. Prove it on the arithmetic (a statement about `Nat`), then connect it to the specification by U3. Witnesses: `n = 10` (threshold 6; every residue has exactly 1844674407370955161 preimages, and the slice also checks the scaled-down analogue with 8-bit words by `decide`: threshold 6, 25 preimages each) and `n = 2^64` (threshold 0, 1 preimage each).
- **U3 (the specification matches the counting):** the first accepted word of the stream is the word the specification returns: `uniformBelowWith` returns `v = w mod n` exactly when `w` is the first word of the stream (positions `0, 1, ...`) with `w ≥ threshold n`. Witness: `n = 2^63 + 1`, seed 1: the first word `0x15D22D6DFEA07126` is below the threshold `2^63 - 1` and is rejected, the second is accepted, position 2 (vectors).
- **U4 (accepted fraction):** `2^63 < 2^64 - threshold n` for `0 < n ≤ 2^64`: at least half of all words are accepted. Under Q1 this gives an expected number of words consumed below 2 (`2^64 / (2^64 - threshold n) < 2`) and a chance of all `fuel` words being rejected below `2^-fuel` (`2^-64` at the default fuel); the expectation is a consequence of Q1, so it is stated and marked trusted, not proved.
- **U5 (the fuel is enough when the threshold is small):** if `threshold n < fuel` then `uniformBelowWith fuel n st` never refuses with `fuelExhausted`, for every stream (the outputs of a stream are distinct, T2, so at most `threshold n` of the first `fuel` words can be rejected). Witnesses: `n = 1` (threshold 0), `n = 3` (threshold 1), `n = 2^64` (threshold 0).
- **U6 (refusals):** `n = 0` gives `.error boundZero`; `n > 2^64` gives `.error boundTooLarge`; `fuel = 0` gives `.error fuelExhausted`. Witnesses: `uniformBelow 0 st`, `uniformBelow (2^64 + 1) st`, and `uniformBelowWith 1 (2^63 + 1) (Stream.ofSeed 1)` (the first word is rejected, one word of fuel is not enough).
- **U7 (determinism and advance):** the result is a function of `(fuel, n, st)`; and on success the advanced stream is `st.advance k` with `1 ≤ k ≤ fuel`. Witness: `uniformBelow 10 (Stream.ofSeed 1)` consumes 1 word.

### Named limits (U)
| limit | value | harm it prevents |
|---|---|---|
| `rejectionFuel` | 64 words per `uniformBelow` | An unbounded rejection loop hangs a simulation. Under Q1 each word is rejected with chance below 1/2, so exhausting 64 words has chance below 2^-64; reaching it is a typed refusal `fuelExhausted`, never a loop and never a silently biased answer. |
| `maxBound` | `n ≤ 2^64` | A bound above the word size cannot be sampled from one word exactly; it is refused (`boundTooLarge`) rather than reduced modulo something, which would bias the result. |

## Uniform dyadic fractions (part F)

### Functions
```
uniformFraction (k : Nat) (st : Stream) : Draw Fraction
  -- k = 0 or k > 64 → refuse fractionBitsOutOfRange
  -- otherwise: (w, st') = st.next;  result ({ num := (w >> (64 - k)).toNat, bits := k }, st')
```
The value is the exact dyadic rational `num / 2^k`: the top `k` bits of one word. It consumes exactly one word. No rejection is needed: every numerator in `[0, 2^k)` has exactly `2^(64-k)` preimages among the 2^64 words.

### Properties to prove (F)
- **F1 (in range):** on success `num < 2^k`, that is `num / 2^k` is in `[0, 1)` (stated as `num < 2^bits`, with `bits = k`). Witness: `k = 8`, seed 1: `num = 21`.
- **F2 (exactness):** for `1 ≤ k ≤ 64` and every `m < 2^k`, exactly `2^(64-k)` words `w` have `w >> (64 - k) = m` (arithmetic on `Nat`, then connected to the specification). Witness: the scaled-down analogue (8-bit words, `k = 3`: 32 words each) by `decide`, and `k = 64` (1 each).
- **F3 (refusals):** `k = 0` and `k = 65` give `.error fractionBitsOutOfRange`. Witness: those two calls.
- **F4 (consumption):** on success the advanced stream is `st.advance 1`. Witness: any vector.

## Shuffle (part S)

### Function
```
shuffle {α} (xs : List α) (st : Stream) : Draw (List α)
```
Fisher-Yates from the back: let `a` be `xs` as an array indexed from 0 and `L` its length. For `i = L - 1` down to `1` (none when `L ≤ 1`): draw `(j, st) = uniformBelow (i + 1) st` (a refusal from this call is the shuffle's refusal, the first one is returned), then swap `a[i]` and `a[j]`. Return `(a, st)`. The empty list and singletons consume no word. The lists the library can be asked about are bounded by memory long before the bound `i + 1 ≤ 2^64` of the draw is a concern; a list longer than 2^64 elements would refuse `boundTooLarge`. In Lean it is a structural recursion on the index (total).

### Properties to prove (S)
- **S1 (permutation):** if `shuffle xs st = .ok (ys, st')` then `ys` is a permutation of `xs` (`List.Perm`). Witness: `shuffle [0,1,...,9] (Stream.ofSeed 1)` (the vector).
- **S2 (function of stream and list):** the result is a function of `(st, xs)`: equal inputs, equal `(ys, st')`; and the result depends on the elements only through their positions, i.e. `shuffle (xs.map f) st` has result `ys.map f` for the same stream (the permutation chosen depends on the length only). Witness: shuffling `[a,b,c,d,e]` and `[0,1,2,3,4]` from the same stream gives the same index permutation.
- **S3 (length and consumption):** `ys.length = xs.length`; on success the advanced stream is `st.advance k` with `k ≥ xs.length - 1` when `xs.length ≥ 1` (and `k = 0` for `[]` and singletons). Witness: the vectors (nine words for ten elements).
- **S4 (refusal propagates):** if a draw refuses, `shuffle` is that refusal and no partial list is returned. Witness: `shuffleWith 0 [1,2] st = .error fuelExhausted` (the slice provides `shuffleWith fuel` beside `shuffle`, which is `shuffleWith rejectionFuel`; fuel 0 is the smallest literal that makes a draw refuse).
- **S5 (stretch, optional, NOT required to land the library):** the permutation is uniform (each of the `L!` permutations has the same number of accepted word sequences). It follows from U2 per step but needs a counting argument over the whole draw sequence; if it is not proved, the ledger marks it `limit`, never `proved`. `[open question]`: whether the owner wants it proved in this library or left to a user of the draws.

## Bernoulli (part B)

### Function
```
bernoulli (num : Int) (den : Nat) (st : Stream) : Draw Bool
  -- den = 0                         → refuse probabilityDenominatorZero
  -- num < 0 or num > den            → refuse probabilityOutOfRange   (p must be in [0, 1])
  -- den > 2^64                      → refuse boundTooLarge
  -- otherwise: (u, st') = uniformBelow den st;   result (decide (u < num), st')
```
The probability is the exact rational `num/den`: `true` has probability exactly `num/den` because `u` is exactly uniform in `[0, den)` (U2) and `num` of the `den` values satisfy `u < num`. The checks run in the order listed (first refusal wins). A draw always consumes one accepted word, also for `num = 0` and `num = den` (a fixed discipline: the position never depends on whether the answer was certain), so a stream's consumption is a function of the call sequence alone.

### Properties to prove (B)
- **B1 (exactness):** for `0 < den ≤ 2^64` and `0 ≤ num ≤ den`, the number of `u ∈ [0, den)` with `u < num` is `num`, so the number of accepted words that give `true` is `num * ((2^64 - threshold den) / den)` out of `2^64 - threshold den`: exactly `num/den`. Witness: `num/den = 1/3` (scaled analogue by `decide`), `0/1`, `1/1`.
- **B2 (certain cases):** `num = 0` gives `false`, `num = den` gives `true`, for every stream. Witness: `(0, 1)` and `(1, 1)`, `(3, 3)`.
- **B3 (refusals):** `den = 0`, `num < 0`, `num > den`, `den > 2^64` give the matching refusals. Witnesses: `(1, 0)`, `(-1, 3)`, `(4, 3)`, `(1, 2^64 + 1)`.
- **B4 (function of stream; advance):** the result is a function of `(num, den, st)`; on success the stream advanced by `1 ≤ k ≤ rejectionFuel`.

## Named limits (all parts)
Only limits that protect the machine or the money exist. This library has two (the table in part U): the rejection fuel (hung simulation) and the bound `n ≤ 2^64` (silent bias). Everything else is total: a list is as long as memory allows, `uniformFraction` consumes one word, `at` and `advance` take constant time.

## Typed refusals
Every refusal is a `Refusal` value in an `Except`, never a default value, never a panic, never a silent clamp:

| refusal | when |
|---|---|
| `boundZero` | `uniformBelow` with `n = 0` (and so a shuffle never asks, it asks for `i + 1 ≥ 2`) |
| `boundTooLarge` | `uniformBelow` with `n > 2^64`; `bernoulli` with `den > 2^64` |
| `fractionBitsOutOfRange` | `uniformFraction` with `k = 0` or `k > 64` |
| `probabilityDenominatorZero` | `bernoulli` with `den = 0` |
| `probabilityOutOfRange` | `bernoulli` with `num < 0` or `num > den` |
| `fuelExhausted` | `uniformBelowWith` with all of its fuel rejected (also surfaced by `shuffle` and `bernoulli`) |

Each refusal has a proved witness: the property U6, F3, B3 (and S4 for propagation) name a literal call that returns it.

## Known-answer vectors (part V)
These are the family's conformance evidence. They were generated by an independent model of the functions above (unbounded integers reduced modulo 2^64, written from this file, not from the Lean code) and the raw-key-0 stream was cross-checked against the published SplitMix64 outputs. A slice checks them into the repository as kernel-checked `example`s and as a plain-text file; a later change of any function that changes a line here is a breaking change by definition. All words are 64-bit, in hexadecimal; `i` counts from 0.

**Mixer** (`mix x`):
```
mix 0x0000000000000000 = 0x0000000000000000
mix 0x0000000000000001 = 0x5692161D100B05E5
mix 0x0000000000000002 = 0xDBD238973A2B148A
mix 0xFFFFFFFFFFFFFFFF = 0xB4D055FCF2CBBD7B
mix 0x0123456789ABCDEF = 0xB2C058E4EBB5112C
```
**Raw streams** (`(Stream.ofKey k).at i`, i = 0..3):
```
key 0x0000000000000000: E220A8397B1DCDAF 6E789E6AA1B965F4 06C45D188009454F F88BB8A8724C81EC
key 0x0000000000000001: 910A2DEC89025CC1 BEEB8DA1658EEC67 F893A2EEFB32555E 71C18690EE42C90B
key 0x0123456789ABCDEF: 157A3807A48FAA9D D573529B34A1D093 2F90B72E996DCCBE A2D419334C4667EC
key 0xFFFFFFFFFFFFFFFF: E4D971771B652C20 E99FF867DBF682C9 382FF84CB27281E9 6D1DB36CCBA982D2
```
**Seeded streams** (`(Stream.ofSeed s)`: key, then `at` 0..3):
```
seed 0x0000000000000000: key 86FA59FA943FE6F8: FAA2702D3A581CDC 3C5CF444C8657B78 EFDB4E177B0B3541 1BC8C5A31EA54F5D
seed 0x0000000000000001: key 6DF8F8D77B172277: 15D22D6DFEA07126 D267F8FB4683E9E3 ED0EC2DFFBED0830 B200728D501A78C8
seed 0x0123456789ABCDEF: key 8C85FA23033A91DE: B9ED29F41599B816 D3F91EA455BE1362 11AFABE62566E08B 252A5A8B5E9E9888
seed 0xFFFFFFFFFFFFFFFF: key A4A0E31617CFD1A1: 75055E6DBB91D266 47C7405A5292ACC2 3E5B3FF10EE91C29 338AF1928F9A632F
```
**Skip-ahead** (`at`, random access):
```
(ofKey 1).at 1000000          = 0x18D805F4F66E8EF0
(ofKey 1).at (2^64 - 1)       = 0x5692161D100B05E5      -- the counter wraps to the key: equals mix 1
(ofKey 1).at 8                = 0x491718DE357E3DA8 = ((ofKey 1).advance 5).at 3
(ofSeed 1).at 1000000         = 0x2346460DFEBFC015
(ofSeed 1).at 1048576         = 0x24402AA9ED7030A3
(ofSeed 1).at (2^64 - 1)      = 0x0A377D1E0EA7DD99
```
**Split** (parent `ofSeed 1`, key `0x6DF8F8D77B172277`; child key, then its `at 0`, `at 1`):
```
child 0:         key D0E6AA970FAF36DD: D8B3C18DF3D9E123 A2E71C264FFA6F97
child 1:         key FDC79FB16B6BCA7E: 87016AD7B81BC459 4A9931DF72E67C7A
child 2:         key B766FC3237EA4433: 86847152ADE57FD7 AFD172FB6F7A3A07
child 2^64 - 1:  key BF8F68540A6A4DFB: DF108A08167153BD 2D6A439B8839D7C3
grandchild (0, 0): key A47AA05215A01329
(ofSeed 0).split 0: key 383C38EE70DF4217
((ofSeed 1) advanced by 7).split 0: key D0E6AA970FAF36DD   -- same as child 0
```
**uniformBelow** (three draws in a row from the stream, then the position; no rejection unless noted):
```
n = 10,      seed 1: 0 3 2,      position 3
n = 10,      seed 0: 8 8 1,      position 3
n = 7,       seed 0: 4 6 4,      position 3
n = 1,       seed 1: 0 0 0,      position 3
n = 2^64,    seed 1: 1572369170352337190 15161360428669594083 17081804703922980912, position 3   -- the words themselves
n = 2^63+1,  seed 3: 4658251182101344059 2841104050483902510 8369637337981164616, position 5       -- a rejection occurs
n = 2^63+1,  seed 1, one draw: 5937988391814818274, position 2 (the first word 0x15D22D6DFEA07126 is below the threshold 2^63-1)
uniformBelowWith 1 (2^63+1) (ofSeed 1)  = .error fuelExhausted
uniformBelow 0 _ = .error boundZero;   uniformBelow (2^64+1) _ = .error boundTooLarge
```
**uniformFraction** (`num` for `k` = 1, 8, 53, 64; position 1):
```
seed 0: 1 250 8818418357062403 18060120795263802588
seed 1: 0 21  767758383961102  1572369170352337190
uniformFraction 0 _ = uniformFraction 65 _ = .error fractionBitsOutOfRange
```
**shuffle** (result, position after):
```
[0..9],  seed 1:        [2,1,4,3,7,5,8,9,6,0], position 9
[0..9],  seed 0:        [9,7,4,3,5,0,2,1,6,8], position 9
[0..9],  seed 0x0123456789ABCDEF: [8,0,7,4,5,6,1,3,9,2], position 9
[a,b,c,d,e], seed 2:    [d,b,a,c,e], position 4
[],      seed 1: [], position 0;    [7], seed 1: [7], position 0
```
**bernoulli** (eight draws in a row; 1 is `true`; position 8):
```
1/3, seed 1: 0 1 1 0 0 0 0 1
3/4, seed 0: 1 1 1 1 1 1 0 1
0/1, seed 1: 0 0 0 0 0 0 0 0
1/1, seed 1: 1 1 1 1 1 1 1 1
bernoulli (-1) 3 _ = .error probabilityOutOfRange;  bernoulli 4 3 _ = .error probabilityOutOfRange
bernoulli 1 0 _ = .error probabilityDenominatorZero; bernoulli 1 (2^64+1) _ = .error boundTooLarge
```

## Quality assumptions and what is trusted
Nothing is trusted in the arithmetic: every claim in parts M, T, P (P1-P3), U (U1-U3, U5-U7), F, S (S1-S4), B is a theorem. What is trusted, and recorded in `docs/trust-ledger.md` by the slice that first needs it:
- **Q1** the statistical independence and uniformity of mixed outputs and of split children (part P); no statistical test battery is run or claimed; `[open question]`: whether a battery run on the reference model (offline, never in the gate) is wanted as extra evidence.
- **Q2** the stream-overlap bound (part P).
- **Q3** the expectation and tail of rejection (U4), which are consequences of Q1.
- **T-toolchain** the entry T1 already there (the compiler is faithful; `UInt64` wraps modulo 2^64 as documented).

## Open questions
1. `[open question]` Q1 evidence: is an offline statistical battery on the reference model wanted? Not needed to land the library; verify by running a standard battery on the first 2^32 outputs of a few seeds and recording the result in a decision file.
2. `[open question]` S5: prove the uniformity of the shuffle's permutation (owner's call; default: not proved, ledger status `limit`).
3. `[open question]` Whether a bound above 2^64 for `uniformBelow` (multi-word, exact) is wanted. Default: refused, `boundTooLarge`.
4. `[open question]` How fast the kernel checks `unmix (mix x) = x` (M2): the proof route is `bv_decide` on the 64-bit word (Std, allowed in `VbmRngProofs`) or an explicit step-by-step argument (xor-shift inverse M1, odd-multiplier inverse M4). The statement does not change if the route does.

## Slices
Each slice is about 150 production lines of Lean with its proofs; the files of two slices that run in parallel never overlap. Every slice that adds a claim adds it to `VbmRngProofs/Ledger.lean`, regenerates `docs/proof-ledger.md`, and a property with a hypothesis carries its non-vacuity witness. Each lands behind no flag (pure functions nothing calls yet) with `.land/land-direct`. Module names: code in `VbmRng/X.lean`, proofs in `VbmRngProofs/X.lean`; only `VbmRng.lean` and `VbmRngProofs.lean` (the module roots, one `import` line per slice) and `VbmRngProofs/Ledger.lean` are shared: a slice adds its own lines there, which merge without conflict, and a rebase resolves them.

| slice | files | content | depends on |
|---|---|---|---|
| **S1 Mixer** | `VbmRng/Mix.lean`, `VbmRngProofs/Mix.lean` | the constants, `mix`, `unmix`, `invXorShift`; M1-M4; the mixer vectors | none |
| **S2 Stream** | `VbmRng/Stream.lean`, `VbmRngProofs/Stream.lean` | `Stream`, `ofKey`, `ofSeed`, `at`, `advance`, `next`; T1-T5; the raw, seeded and skip-ahead vectors | S1 |
| **S3 Refusal and Draw** | `VbmRng/Refusal.lean`, `VbmRngProofs/Refusal.lean` | `Refusal`, `Draw`, `Fraction`; the constructors are distinct (`decide`) | none (parallel with S1) |
| **S4 Split** | `VbmRng/Split.lean`, `VbmRngProofs/Split.lean` | `childKey`, `Stream.split`; P1-P3; the split vectors; the trust-ledger entries for Q1, Q2 | S2 |
| **S5 Below** | `VbmRng/Below.lean`, `VbmRngProofs/Below.lean` | `threshold`, `rejectionFuel`, `uniformBelowWith`, `uniformBelow`; U1-U7; the uniformBelow vectors; the trust entry for Q3 | S2, S3 |
| **S6 Fraction** | `VbmRng/Fraction.lean`, `VbmRngProofs/Fraction.lean` | `uniformFraction`; F1-F4; the fraction vectors | S2, S3 |
| **S7 Shuffle** | `VbmRng/Shuffle.lean`, `VbmRngProofs/Shuffle.lean` | `shuffle`, `shuffleWith`; S1-S4 (S5 optional, own follow-up slice if wanted); the shuffle vectors | S5 |
| **S8 Bernoulli** | `VbmRng/Bernoulli.lean`, `VbmRngProofs/Bernoulli.lean` | `bernoulli`; B1-B4; the bernoulli vectors | S5 |
| **S9 Vectors** | `vectors/known-answers.txt`, `VbmRngProofs/Vectors.lean`, `scripts/test_vectors.sh` | every vector of part V checked into the repository as plain text and as kernel-checked `example`s; the test script ends with `ran: vectors: N cases` (N > 0) and a negative self-test (a wrong vector is detected); a README section "conformance" naming the file | S1-S8 (a vector group may land with its own slice; S9 is the closing check that none is missing) |

Order and parallelism (which slices can run at the same time):
1. **Wave 1, in parallel:** S1 and S3 (no shared file).
2. **Wave 2:** S2 (needs S1).
3. **Wave 3, in parallel:** S4, S5, S6 (each needs only S2 and S3; no shared file).
4. **Wave 4, in parallel:** S7 and S8 (each needs S5; no shared file).
5. **Wave 5:** S9, then the release candidate runs the full suite.

Each slice is its own landing; if one grows past about 150 production lines or 45 minutes without a passing build, it stops and writes a decomposition plan (for S1: the xor-shift inverse M1 and the multiplier part M4 are the natural split; for S5: U2 as a pure `Nat` counting lemma first, then the Stream-level statement).
