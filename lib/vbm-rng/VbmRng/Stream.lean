import VbmRng.Mix
/-! # The stream (S2)

A stream is a key and a position (two words, no hidden state). Output number `i` is `mix (key + (pos + i + 1) * gamma)`, all arithmetic modulo 2^64. The properties T1-T5 are proved in `VbmRngProofs/Stream.lean`. -/
namespace VbmRng

/-- The whole state of a stream. -/
structure Stream where
  /-- Identifies the stream. -/
  key : UInt64
  /-- How many outputs have been consumed (wraps at 2^64). -/
  pos : UInt64
  deriving DecidableEq

namespace Stream

/-- A raw key as a stream at position zero. -/
def ofKey (k : UInt64) : Stream := { key := k, pos := 0 }

/-- The seeding function: a seed becomes a key by `mix (seed ⊕ seedSalt)`. -/
def ofSeed (s : UInt64) : Stream := ofKey (mix (s ^^^ seedSalt))

/-- Output number `i`, by random access. -/
def «at» (st : Stream) (i : UInt64) : UInt64 := mix (st.key + (st.pos + i + 1) * gamma)

/-- Skip ahead by `j` outputs (the position wraps modulo 2^64). -/
def advance (st : Stream) (j : UInt64) : Stream := { st with pos := st.pos + j }

/-- The next output and the advanced stream. -/
def next (st : Stream) : UInt64 × Stream := (st.«at» 0, st.advance 1)

end Stream
end VbmRng
