import ZlibF.Proof.«deflate.c.engine.fill-preserve»

/-! # Resuming fill_window after consuming bytes without new input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem first_fill_padding {d : DeflateState} {n : UInt32} {copied : Array UInt8}
    (ss : d.strstart = 0) (window : d.window_size = 65536) (bound : n.toNat ≤ 65536) :
    let df := firstFillState d n copied
    min (df.strstart.toNat + df.lookahead.toNat + 258) df.window_size.toNat ≤ df.high_water.toNat := by
  have high := (firstFill_high_water n bound).1
  have fields : (firstFillState d n copied).strstart = 0 ∧
      (firstFillState d n copied).lookahead = n ∧ (firstFillState d n copied).window_size = 65536 := by
    unfold firstFillState primeState
    split <;> exact ⟨ss, rfl, window⟩
  simp only [fields.1, fields.2.1, fields.2.2, show (0 : UInt32).toNat = 0 from rfl, Nat.zero_add]
  change min (n.toNat + 258) 65536 ≤ (n.toUInt64 + firstPadding n).toNat
  rw [high]
  omega

theorem fill_body_no_input {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (input : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    fillBody (some (.tab ds)) d.w_size false h = .ok (true, h) := by
  simp only [fillBody, bind_app, ldDeflateState_tab good.live.hs, noSlide, if_false,
    rdD_eq, good.live.hs, good.live.back, zrd_eq, good.live.hz, input]
  rfl

theorem fill_high_water_retained {h : Heap} {ds : Nat} {d : DeflateState}
    (state : h.dstates ds = some d) (inv : DStInv h ds d)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (padded : min (d.strstart.toNat + d.lookahead.toNat + 258) d.window_size.toNat ≤ d.high_water.toNat) :
    fillHighWater (some (.tab ds)) h = .ok ((), h) := by
  have ws : d.w_size.toNat ≤ 32768 := by
    rw [inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) inv.wbits_hi
         _ = 32768 := by decide
  have window : d.window_size.toNat ≤ 65536 := by rw [inv.wsz]; omega
  have sum : (d.strstart.toUInt64 + d.lookahead.toUInt64).toNat = d.strstart.toNat + d.lookahead.toNat := by
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt (by omega)]
  have extra : (d.strstart.toUInt64 + d.lookahead.toUInt64 + WIN_INIT_u).toNat =
      d.strstart.toNat + d.lookahead.toNat + 258 := by
    rw [UInt64.toNat_add, sum]
    change (d.strstart.toNat + d.lookahead.toNat + 258) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  unfold fillHighWater
  simp only [bind_app, ldDeflateState_tab state]
  by_cases less : d.high_water < d.window_size
  · have lt : d.high_water.toNat < d.window_size.toNat := UInt64.lt_iff_toNat_lt.mp less
    have enough : d.strstart.toNat + d.lookahead.toNat + 258 ≤ d.high_water.toNat := by omega
    have first : ¬ d.high_water < d.strstart.toUInt64 + d.lookahead.toUInt64 := by
      rw [UInt64.lt_iff_toNat_lt, sum]
      omega
    have second : ¬ d.high_water < d.strstart.toUInt64 + d.lookahead.toUInt64 + WIN_INIT_u := by
      rw [UInt64.lt_iff_toNat_lt, extra]
      omega
    simp only [less, if_true, first, if_false, second]
    rfl
  · simp only [less, if_false]
    rfl

/-- `local void fill_window(deflate_state *s)`.
A resumed call with no input and no slide keeps an already padded window
unchanged. This is the case reached when consumption preserves the valid
data endpoint. Sliding and new-input resumptions are separate obligations. -/
theorem fill_window_resume_no_input {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (input : z.avail_in = 0)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (padded : min (d.strstart.toNat + d.lookahead.toNat + 258) d.window_size.toNat ≤ d.high_water.toNat) :
    fill_window (some (.tab ds)) h = .ok ((), h) := by
  have loop := do_once (fill_body_no_input good input noSlide) (fill_cond_break (some (.tab ds)) h)
  rw [fill_window_source]
  simp only [bind_app, rdD_eq, good.live.hs, loop]
  exact fill_high_water_retained good.live.hs good.inv range padded

end Zlib.Deflate.Engine.Proofs
