import VbmRng.Stream
import VbmRng.Refusal
/-! # Uniform bounded integers (S5)

`uniformBelow n st` draws words `st.at 0, st.at 1, ...` in order and accepts the first one that is at least `threshold n = 2^64 % n`; the result is that word modulo `n`. The accepted words are a whole number of copies of `[0, n)`, so there is no modulo bias. At most `rejectionFuel` words are drawn; if all are rejected the draw is the typed refusal `fuelExhausted`. The properties U1-U7 are proved in `VbmRngProofs/Below.lean`. -/
namespace VbmRng

/-- The most words one `uniformBelow` may draw (a named limit: it prevents an unbounded rejection loop). -/
def rejectionFuel : Nat := 64

/-- The largest bound accepted: a bound above the word size cannot be sampled exactly from one word. -/
def maxBound : Nat := 2 ^ 64

/-- The words below this are rejected: `2^64 mod n`. -/
def threshold (n : Nat) : Nat := 2 ^ 64 % n

/-- The rejection loop: draw the next word; accept it if it is at least `th`, else advance and retry while fuel lasts. -/
def drawGo (n th : Nat) : Nat → Stream → DrawWith Stream Nat
  | 0, _ => .error .fuelExhausted
  | fuel + 1, st =>
    if th ≤ (st.«at» 0).toNat then .ok ((st.«at» 0).toNat % n, st.advance 1)
    else drawGo n th fuel (st.advance 1)

/-- A uniform natural below `n` from at most `fuel` words, or a typed refusal. -/
def uniformBelowWith (fuel n : Nat) (st : Stream) : DrawWith Stream Nat :=
  if n = 0 then .error .boundZero
  else if maxBound < n then .error .boundTooLarge
  else drawGo n (threshold n) fuel st

/-- A uniform natural below `n` with the default fuel `rejectionFuel`. -/
def uniformBelow (n : Nat) (st : Stream) : DrawWith Stream Nat := uniformBelowWith rejectionFuel n st

end VbmRng
