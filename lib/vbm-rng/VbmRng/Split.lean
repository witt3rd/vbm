import VbmRng.Stream
/-! # Splitting (S4)

A child's key is `mix (mix (key ⊕ splitSalt) + (c + 1) * gamma)`: it depends on the parent's key and the child index only, never on the parent's position. The inner `mix` with the salt keeps a child's key from being an output of the parent stream. The properties P1-P3 are proved in `VbmRngProofs/Split.lean`. -/
namespace VbmRng

/-- The key of child `c` of a stream whose key is `k`. -/
def childKey (k : UInt64) (c : UInt64) : UInt64 :=
  mix (mix (k ^^^ splitSalt) + (c + 1) * gamma)

namespace Stream

/-- Child `c` of a stream: a fresh stream at position zero whose key is `childKey st.key c`. -/
def split (st : Stream) (c : UInt64) : Stream := ofKey (childKey st.key c)

end Stream
end VbmRng
