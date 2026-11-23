import VbmRng.Stream
import VbmRngProofs.Mix
/-! # The stream's proofs (S2): T1-T5 and the raw, seeded and skip-ahead vectors

T2 composes four bijections: a translation of the index, multiplication by `gamma` (M4), a translation by the key, and `mix` (M3). -/
namespace VbmRng
namespace Stream

theorem xor_cancel (a b c : UInt64) (h : a ^^^ c = b ^^^ c) : a = b := by
  have := congrArg (· ^^^ c) h
  simpa [UInt64.xor_assoc] using this

/-- **T5 (seeds give distinct streams).** -/
theorem ofSeed_key_injective {s s' : UInt64} (h : (ofSeed s).key = (ofSeed s').key) : s = s' :=
  xor_cancel _ _ _ (mix_injective h)

/-- **T1 (determinism, over the named equations).** -/
theorem ofSeed_inj (s s' : UInt64) : ofSeed s = ofSeed s' ↔ s = s' :=
  ⟨fun h => ofSeed_key_injective (congrArg Stream.key h), fun h => h ▸ rfl⟩

theorem at_det {st st' : Stream} {i i' : UInt64} (h : st = st') (hi : i = i') : st.«at» i = st'.«at» i' := by
  subst h; subst hi; rfl

theorem next_det {st st' : Stream} (h : st = st') : st.next = st'.next := h ▸ rfl

theorem advance_det {st st' : Stream} {j j' : UInt64} (h : st = st') (hj : j = j') :
    st.advance j = st'.advance j' := by
  subst h; subst hj; rfl

theorem add_cancel_left (a x y : UInt64) (h : a + x = a + y) : x = y := by
  have := congrArg (fun z => z - a) h
  simpa [UInt64.sub_eq_add_neg, UInt64.add_comm a x, UInt64.add_comm a y, UInt64.add_assoc] using this

/-- **T2 (no repeats, the full range).** -/
theorem at_injective (st : Stream) {i j : UInt64} (h : st.«at» i = st.«at» j) : i = j := by
  have h1 := mix_injective h
  have h2 : (st.pos + i + 1) * gamma = (st.pos + j + 1) * gamma := add_cancel_left st.key _ _ h1
  have h3 := mul_gamma_injective h2
  have h4 : (st.pos + 1) + i = (st.pos + 1) + j := by
    have e : ∀ x : UInt64, st.pos + 1 + x = st.pos + x + 1 := fun x => by ac_rfl
    rw [e, e]; exact h3
  exact add_cancel_left _ _ _ h4

theorem at_ne (st : Stream) {i j : UInt64} (h : i ≠ j) : st.«at» i ≠ st.«at» j :=
  fun e => h (at_injective st e)

/-- `st.at` is onto: every word appears (so, with injectivity, a bijection). -/
theorem at_surjective (st : Stream) (w : UInt64) : ∃ i, st.«at» i = w := by
  refine ⟨((unmix w - st.key) * gammaInv) - (st.pos + 1), ?_⟩
  unfold Stream.«at»
  have : st.pos + (((unmix w - st.key) * gammaInv) - (st.pos + 1)) + 1 = (unmix w - st.key) * gammaInv := by
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]
    bv_omega
  rw [this, mul_inv_cancel' _ _ _ gamma_gammaInv]
  have e : st.key + (unmix w - st.key) = unmix w := by
    apply UInt64.toBitVec_inj.mp
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_sub]
    bv_omega
  rw [e, mix_unmix]

/-- **T3 (skip-ahead agrees with stepping).** -/
theorem at_add (st : Stream) (i j : UInt64) : st.«at» (i + j) = (st.advance j).«at» i := by
  unfold Stream.«at» advance
  have : st.pos + (i + j) + 1 = st.pos + j + i + 1 := by ac_rfl
  simp only [this]

/-- **T4 (next is at and advance).** -/
theorem next_fst (st : Stream) : st.next.1 = st.«at» 0 := rfl
theorem next_snd (st : Stream) : st.next.2 = st.advance 1 := rfl

theorem advance_advance (st : Stream) (a b : UInt64) : (st.advance a).advance b = st.advance (a + b) := by
  unfold advance
  simp [UInt64.add_assoc]

-- Non-vacuity witnesses and the vectors (kernel-checked).
example : ofSeed 0 = ofSeed 0 ↔ (0 : UInt64) = 0 := ofSeed_inj 0 0
example : (ofSeed 0).«at» 0 = 0xFAA2702D3A581CDC := by decide +kernel
example : (ofKey 0).«at» 0 ≠ (ofKey 0).«at» 1 := by decide +kernel
example : (ofKey 1).«at» 8 = 0x491718DE357E3DA8 ∧ ((ofKey 1).advance 5).«at» 3 = 0x491718DE357E3DA8 := by decide +kernel
example : (ofKey 1).next = (0x910A2DEC89025CC1, { key := 1, pos := 1 }) := by decide +kernel
example : (ofSeed 0).key = 0x86FA59FA943FE6F8 ∧ (ofSeed 1).key = 0x6DF8F8D77B172277 := by decide +kernel
example : (ofSeed 0).key ≠ (ofSeed 1).key := by decide +kernel

-- Raw streams, `at` 0..3.
example : [(ofKey 0).«at» 0, (ofKey 0).«at» 1, (ofKey 0).«at» 2, (ofKey 0).«at» 3] =
    [0xE220A8397B1DCDAF, 0x6E789E6AA1B965F4, 0x06C45D188009454F, 0xF88BB8A8724C81EC] := by decide +kernel
example : [(ofKey 1).«at» 0, (ofKey 1).«at» 1, (ofKey 1).«at» 2, (ofKey 1).«at» 3] =
    [0x910A2DEC89025CC1, 0xBEEB8DA1658EEC67, 0xF893A2EEFB32555E, 0x71C18690EE42C90B] := by decide +kernel
example : [(ofKey 0x0123456789ABCDEF).«at» 0, (ofKey 0x0123456789ABCDEF).«at» 1, (ofKey 0x0123456789ABCDEF).«at» 2, (ofKey 0x0123456789ABCDEF).«at» 3] =
    [0x157A3807A48FAA9D, 0xD573529B34A1D093, 0x2F90B72E996DCCBE, 0xA2D419334C4667EC] := by decide +kernel
example : [(ofKey 0xFFFFFFFFFFFFFFFF).«at» 0, (ofKey 0xFFFFFFFFFFFFFFFF).«at» 1, (ofKey 0xFFFFFFFFFFFFFFFF).«at» 2, (ofKey 0xFFFFFFFFFFFFFFFF).«at» 3] =
    [0xE4D971771B652C20, 0xE99FF867DBF682C9, 0x382FF84CB27281E9, 0x6D1DB36CCBA982D2] := by decide +kernel

-- Seeded streams: key, then `at` 0..3.
example : (ofSeed 0).key = 0x86FA59FA943FE6F8 ∧ [(ofSeed 0).«at» 0, (ofSeed 0).«at» 1, (ofSeed 0).«at» 2, (ofSeed 0).«at» 3] =
    [0xFAA2702D3A581CDC, 0x3C5CF444C8657B78, 0xEFDB4E177B0B3541, 0x1BC8C5A31EA54F5D] := by decide +kernel
example : (ofSeed 1).key = 0x6DF8F8D77B172277 ∧ [(ofSeed 1).«at» 0, (ofSeed 1).«at» 1, (ofSeed 1).«at» 2, (ofSeed 1).«at» 3] =
    [0x15D22D6DFEA07126, 0xD267F8FB4683E9E3, 0xED0EC2DFFBED0830, 0xB200728D501A78C8] := by decide +kernel
example : (ofSeed 0x0123456789ABCDEF).key = 0x8C85FA23033A91DE ∧ [(ofSeed 0x0123456789ABCDEF).«at» 0, (ofSeed 0x0123456789ABCDEF).«at» 1, (ofSeed 0x0123456789ABCDEF).«at» 2, (ofSeed 0x0123456789ABCDEF).«at» 3] =
    [0xB9ED29F41599B816, 0xD3F91EA455BE1362, 0x11AFABE62566E08B, 0x252A5A8B5E9E9888] := by decide +kernel
example : (ofSeed 0xFFFFFFFFFFFFFFFF).key = 0xA4A0E31617CFD1A1 ∧ [(ofSeed 0xFFFFFFFFFFFFFFFF).«at» 0, (ofSeed 0xFFFFFFFFFFFFFFFF).«at» 1, (ofSeed 0xFFFFFFFFFFFFFFFF).«at» 2, (ofSeed 0xFFFFFFFFFFFFFFFF).«at» 3] =
    [0x75055E6DBB91D266, 0x47C7405A5292ACC2, 0x3E5B3FF10EE91C29, 0x338AF1928F9A632F] := by decide +kernel

-- Skip-ahead.
example : (ofKey 1).«at» 1000000 = 0x18D805F4F66E8EF0 := by decide +kernel
example : (ofKey 1).«at» 0xFFFFFFFFFFFFFFFF = 0x5692161D100B05E5 := by decide +kernel
example : (ofKey 1).«at» 8 = 0x491718DE357E3DA8 := by decide +kernel
example : (ofSeed 1).«at» 1000000 = 0x2346460DFEBFC015 := by decide +kernel
example : (ofSeed 1).«at» 1048576 = 0x24402AA9ED7030A3 := by decide +kernel
example : (ofSeed 1).«at» 0xFFFFFFFFFFFFFFFF = 0x0A377D1E0EA7DD99 := by decide +kernel

end Stream
end VbmRng
