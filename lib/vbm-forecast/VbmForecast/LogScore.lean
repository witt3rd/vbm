import VbmForecast.Rep
/-! # S4: the logarithmic score

Two tools (`docs/spec.md`, section 3.2). (A) The exact comparison of two forecasters on the same events, with no logarithm: the forecaster whose realised-outcome probabilities have the larger product has the strictly lower total log loss. (B) `log2Enclosure`: integers `(lo, hi)` with `lo ≤ 2^F * log2 (num / den) ≤ hi` and `hi - lo ≤ 2`, the claim being the exact power relation `Log2Lower` / `Log2Upper` (no logarithm function exists in `Init`). Base 2, units of `2^-F` bits. -/
namespace VbmForecast

/-! ## (A) The exact comparison -/

/-- The product of realised-outcome probabilities (numerators over one scale). -/
def natProd : List Nat → Nat
  | [] => 1
  | x :: xs => x * natProd xs

/-- A is better iff `gt`: the product of A's realised-outcome probabilities against B's (`s^n` cancels). Zero needs no special case. -/
def logCompare (as bs : List Nat) : Ordering := compare (natProd as) (natProd bs)

/-- `logCompare` after the length check (`lengthMismatch`) and the `maxEvents` limit. -/
def logCompareV (lim : Limits) (as bs : List Nat) : Except Refusal Ordering := do
  checkAligned as.length bs.length
  checkSample lim as.length
  pure (logCompare as bs)

/-- The verdict on the log score: refused below the minimum sample, else decided by the exact comparison (`eq` is the tie). -/
inductive LogVerdict where
  | refused (tooFew minEvents : Nat)
  | decided (o : Ordering)
  deriving DecidableEq, Repr

/-- The minimum-sample rule is checked first (on `as.length`), then the length check and `maxEvents`, then the exact comparison. -/
def logVerdict (lim : Limits) (as bs : List Nat) : Except Refusal LogVerdict :=
  if as.length < lim.minEvents then .ok (.refused as.length lim.minEvents)
  else do
    let o ← logCompareV lim as bs
    pure (.decided o)

/-! ## (B) The enclosure of `2^F * log2 (num / den)` -/

/-- `lo ≤ 2^F * log2 (num/den)`, defined as `2^lo ≤ (num/den)^(2^F)` cross-multiplied into `Nat`s. -/
def Log2Lower (num den F : Nat) (lo : Int) : Prop :=
  2 ^ lo.toNat * den ^ (2 ^ F) ≤ 2 ^ (-lo).toNat * num ^ (2 ^ F)

/-- `2^F * log2 (num/den) ≤ hi`, defined as `(num/den)^(2^F) ≤ 2^hi` cross-multiplied into `Nat`s. -/
def Log2Upper (num den F : Nat) (hi : Int) : Prop :=
  num ^ (2 ^ F) * 2 ^ (-hi).toNat ≤ 2 ^ hi.toNat * den ^ (2 ^ F)

/-- The mantissa width in bits after the point: `3 F + 4`, so that the error term `6^F` is at most `2^W` (sufficient for the proved width bound; not claimed minimal). -/
def logWidth (F : Nat) : Nat := 3 * F + 4

/-- The number `k` of doublings that bring `num / den` into `[1, 2)`; `fuel ≥ den` suffices. -/
def redK (den : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | num, f + 1 => if den ≤ num then 0 else redK den (2 * num) f + 1

/-- The truncated mantissa `t` over `2^W`, with its binary exponent `b`: the value `2^b * t / 2^W` is a lower bound. -/
structure LogState where
  b : Nat
  t : Nat

/-- One squaring at `m = 2^W`: the exponent doubles and gains a bit when the square reaches 2; the mantissa is truncated down. -/
def logStep (m : Nat) (s : LogState) : LogState :=
  if 2 * m * m ≤ s.t * s.t then ⟨2 * s.b + 1, s.t * s.t / (2 * m)⟩ else ⟨2 * s.b, s.t * s.t / m⟩

/-- `F` squarings. -/
def logRun (m : Nat) : Nat → LogState → LogState
  | 0, s => s
  | j + 1, s => logStep m (logRun m j s)

/-- The enclosure `(lo, hi)` of `2^F * log2 (num / den)`, for `0 < num ≤ den`: `badScale` for `den = 0`, `probOutOfRange 0 num` for `num > den`,
`zeroProbability` for `num = 0`. An exact power of two is returned exactly `(lo, lo)`; otherwise `hi - lo` is 1 or 2. -/
def log2Enclosure (num den F : Nat) : Except Refusal (Int × Int) :=
  if den = 0 then .error .badScale
  else if den < num then .error (.probOutOfRange 0 (num : Int))
  else if num = 0 then .error .zeroProbability
  else
    let m := 2 ^ logWidth F
    let k := redK den num den
    let p := num * 2 ^ k
    let kn : Int := ((k * 2 ^ F : Nat) : Int)
    if p = den then .ok (-kn, -kn)
    else
      let r := logRun m F ⟨0, m * p / den⟩
      .ok ((r.b : Int) - kn, (r.b : Int) + (if r.t + 6 ^ F ≤ 2 * m then 1 else 2) - kn)

/-- The `what` field of `Refusal.tooMany` for `F > logBits`. -/
def limitLogBits : Nat := 4

/-- `log2Enclosure` with the named limit `F ≤ logBits`. -/
def log2EnclosureV (lim : Limits) (num den F : Nat) : Except Refusal (Int × Int) :=
  if lim.logBits < F then .error (.tooMany limitLogBits F lim.logBits) else log2Enclosure num den F

end VbmForecast
