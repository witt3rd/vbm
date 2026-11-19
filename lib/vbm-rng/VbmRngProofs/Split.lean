import VbmRng.Split
import VbmRngProofs.Stream
/-! # The split's proofs (S4): P1-P3 and the split vectors

P1 composes the bijections `mix` (M3), a translation, multiplication by `gamma` (M4) and a translation of the child index. The quality assumptions Q1 and Q2 are not provable; they are recorded `limit` in the ledger and in `docs/trust-ledger.md`. -/
namespace VbmRng

/-- **P1 (distinct children), contrapositive form.** Equal child keys come from equal child indices. -/
theorem childKey_injective (k : UInt64) {c c' : UInt64} (h : childKey k c = childKey k c') : c = c' := by
  have h1 := mix_injective h
  have h2 : (c + 1) * gamma = (c' + 1) * gamma := Stream.add_cancel_left _ _ _ h1
  have h3 := mul_gamma_injective h2
  exact Stream.add_cancel_left 1 c c' (by rw [UInt64.add_comm 1 c, UInt64.add_comm 1 c']; exact h3)

/-- **P1 (distinct children).** -/
theorem childKey_ne (k : UInt64) {c c' : UInt64} (h : c ≠ c') : childKey k c ≠ childKey k c' :=
  fun e => h (childKey_injective k e)

namespace Stream

/-- **P2 (split is a function of the parent's key and the index).** -/
theorem split_key_eq {st st' : Stream} (c : UInt64) (h : st.key = st'.key) : st.split c = st'.split c := by
  unfold split; rw [h]

/-- **P3 (children start at zero).** -/
theorem split_pos (st : Stream) (c : UInt64) : (st.split c).pos = 0 := rfl

/-- The child's key is `childKey` of the parent's key. -/
theorem split_key (st : Stream) (c : UInt64) : (st.split c).key = childKey st.key c := rfl

/-- Distinct children of one stream have distinct keys (P1 at the stream level). -/
theorem split_key_ne (st : Stream) {c c' : UInt64} (h : c ≠ c') : (st.split c).key ≠ (st.split c').key :=
  childKey_ne st.key h

-- Non-vacuity witnesses (small literals) and the split vectors, kernel-checked.
-- P1: distinct indices, distinct keys; the hypothesis `c ≠ c'` can hold.
example : (0 : UInt64) ≠ 1 ∧ childKey 0x6DF8F8D77B172277 0 ≠ childKey 0x6DF8F8D77B172277 1 :=
  ⟨by decide +kernel, childKey_ne _ (by decide +kernel)⟩
-- P2: seed 1 at position 0 and at position 7, child 0 (the hypothesis holds).
example : (ofSeed 1).key = ((ofSeed 1).advance 7).key ∧ (ofSeed 1).split 0 = ((ofSeed 1).advance 7).split 0 :=
  ⟨rfl, split_key_eq 0 rfl⟩
example : (ofSeed 1).split 0 = ((ofSeed 1).advance 7).split 0 := by decide +kernel
-- P3.
example : ((ofSeed 1).split 5).pos = 0 := by decide +kernel

-- Child keys of the seed-1 stream.
example : (ofSeed 1).key = 0x6DF8F8D77B172277 := by decide +kernel
example : childKey 0x6DF8F8D77B172277 0 = 0xD0E6AA970FAF36DD := by decide +kernel
example : childKey 0x6DF8F8D77B172277 1 = 0xFDC79FB16B6BCA7E := by decide +kernel
example : childKey 0x6DF8F8D77B172277 2 = 0xB766FC3237EA4433 := by decide +kernel
example : childKey 0x6DF8F8D77B172277 0xFFFFFFFFFFFFFFFF = 0xBF8F68540A6A4DFB := by decide +kernel
-- Each child's key and its first two outputs.
example : (ofSeed 1).split 0 = ofKey 0xD0E6AA970FAF36DD ∧ ((ofSeed 1).split 0).«at» 0 = 0xD8B3C18DF3D9E123 ∧
    ((ofSeed 1).split 0).«at» 1 = 0xA2E71C264FFA6F97 := by decide +kernel
example : (ofSeed 1).split 1 = ofKey 0xFDC79FB16B6BCA7E ∧ ((ofSeed 1).split 1).«at» 0 = 0x87016AD7B81BC459 ∧
    ((ofSeed 1).split 1).«at» 1 = 0x4A9931DF72E67C7A := by decide +kernel
example : (ofSeed 1).split 2 = ofKey 0xB766FC3237EA4433 ∧ ((ofSeed 1).split 2).«at» 0 = 0x86847152ADE57FD7 ∧
    ((ofSeed 1).split 2).«at» 1 = 0xAFD172FB6F7A3A07 := by decide +kernel
example : (ofSeed 1).split 0xFFFFFFFFFFFFFFFF = ofKey 0xBF8F68540A6A4DFB ∧ ((ofSeed 1).split 0xFFFFFFFFFFFFFFFF).«at» 0 = 0xDF108A08167153BD ∧
    ((ofSeed 1).split 0xFFFFFFFFFFFFFFFF).«at» 1 = 0x2D6A439B8839D7C3 := by decide +kernel
-- Grandchild (0, 0), another seed, and the parent advanced by 7.
example : ((ofSeed 1).split 0).split 0 = ofKey 0xA47AA05215A01329 := by decide +kernel
example : (ofSeed 0).split 0 = ofKey 0x383C38EE70DF4217 := by decide +kernel
example : ((ofSeed 1).advance 7).split 0 = ofKey 0xD0E6AA970FAF36DD := by decide +kernel

end Stream
end VbmRng
