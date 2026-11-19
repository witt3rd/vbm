/-! # The mixer (S1)

The constants, the bijective 64-bit mixer `mix`, its inverse `unmix`, and the xor-shift inverse `invXorShift`. Exact `UInt64` arithmetic only (wraps modulo 2^64); no floating point. The properties are proved in `VbmRngProofs/Mix.lean`. -/
namespace VbmRng

/-- The stream increment (odd). -/
def gamma : UInt64 := 0x9E3779B97F4A7C15
/-- The first mixer multiplier (odd). -/
def mulA : UInt64 := 0xBF58476D1CE4E5B9
/-- The second mixer multiplier (odd). -/
def mulB : UInt64 := 0x94D049BB133111EB
/-- Domain separation for split: the high 64 fractional bits of the square root of 2. -/
def splitSalt : UInt64 := 0x6A09E667F3BCC908
/-- Domain separation for seeding: the high 64 fractional bits of the square root of 3. -/
def seedSalt : UInt64 := 0xBB67AE8584CAA73B
/-- The inverse of `mulA` modulo 2^64. -/
def mulAInv : UInt64 := 0x96DE1B173F119089
/-- The inverse of `mulB` modulo 2^64. -/
def mulBInv : UInt64 := 0x319642B2D24D8EC3
/-- The inverse of `gamma` modulo 2^64. -/
def gammaInv : UInt64 := 0xF1DE83E19937733D

/-- The terms `y >> t ⊕ y >> (t + s) ⊕ ...` while the shift is below 64, at most `fuel` terms (structural recursion). -/
def invXorShiftGo (s : Nat) (y : UInt64) : Nat → Nat → UInt64
  | 0, _ => 0
  | fuel + 1, t => if t < 64 then (y >>> t.toUInt64) ^^^ invXorShiftGo s y fuel (t + s) else 0

/-- The inverse of `x ↦ x ⊕ (x >> s)` for `1 ≤ s ≤ 63`: `y ⊕ (y >> s) ⊕ (y >> 2s) ⊕ ...` while the shift is below 64. -/
def invXorShift (s : Nat) (y : UInt64) : UInt64 := invXorShiftGo s y 64 0

/-- The bijective 64-bit mixing function. -/
def mix (z : UInt64) : UInt64 :=
  let z := z ^^^ (z >>> 30)
  let z := z * mulA
  let z := z ^^^ (z >>> 27)
  let z := z * mulB
  z ^^^ (z >>> 31)

/-- The inverse of `mix`. -/
def unmix (z : UInt64) : UInt64 :=
  let z := invXorShift 31 z
  let z := z * mulBInv
  let z := invXorShift 27 z
  let z := z * mulAInv
  invXorShift 30 z

end VbmRng
