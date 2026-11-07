import ZlibF.Proof.«deflate.c.engine.fill-read»

/-! # Free window space derived from the actual fill guard -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open ZlibF.Spec.Public
set_option autoImplicit false

def fillMore (d : DeflateState) : UInt32 :=
  (d.window_size - d.lookahead.toUInt64 - d.strstart.toUInt64).toUInt32

theorem fill_more_nat {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat) :
    (fillMore d).toNat = d.window_size.toNat - (d.strstart.toNat + d.lookahead.toNat) := by
  have extent := window_extent good win get
  have first : (d.window_size - d.lookahead.toUInt64).toNat = d.window_size.toNat - d.lookahead.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64]; omega),
      UInt32.toNat_toUInt64]
  have second : (d.window_size - d.lookahead.toUInt64 - d.strstart.toUInt64).toNat =
      d.window_size.toNat - (d.strstart.toNat + d.lookahead.toNat) := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, first, UInt32.toNat_toUInt64]; omega),
      first, UInt32.toNat_toUInt64]
    omega
  unfold fillMore
  rw [UInt64.toNat_toUInt32, second, Nat.mod_eq_of_lt (by omega)]

/-- A short lookahead and the source's non-sliding guard imply real free
space and enough total capacity to finish the fill in one read. -/
theorem fill_room_no_slide {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    0 < (fillMore d).toNat ∧ 262 ≤ d.lookahead.toNat + (fillMore d).toNat := by
  have wsUpper : d.w_size.toNat ≤ 32768 := by
    rw [good.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) good.inv.wbits_hi
         _ = 32768 := by decide
  have wsLower : 512 ≤ d.w_size.toNat := by
    rw [good.inv.wsize]
    have power := Nat.pow_le_pow_right (n := 2) (by decide) good.inv.wbits_lo
    exact power
  have sub : (d.w_size - MIN_LOOKAHEAD_u).toNat = d.w_size.toNat - 262 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; change 262 ≤ _; omega)]
    rfl
  have threshold : (d.w_size + (d.w_size - MIN_LOOKAHEAD_u)).toNat = 2 * d.w_size.toNat - 262 := by
    rw [UInt32.toNat_add, sub, Nat.mod_eq_of_lt (by omega)]
    omega
  change ¬ d.w_size + (d.w_size - MIN_LOOKAHEAD_u) ≤ d.strstart at noSlide
  rw [UInt32.le_iff_toNat_le, threshold] at noSlide
  rw [fill_more_nat good win get range, good.inv.wsz]
  rw [good.inv.wsz] at range
  exact ⟨by omega, by omega⟩

/-- Public caller buffers cannot alias the private window. This discharges
the copy-separation premise instead of adding it to the public API domain. -/
theorem caller_input_window_separate {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (win : d.window = .ref (.blk w) 0) (pointer : z.next_in = .ref ref io) : BRef.blk w ≠ ref := by
  obtain ⟨z0, get0, caller, _, _⟩ := buffers
  have same : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
  subst z0
  rcases caller with null | ⟨_, _, unowned⟩
  · rw [pointer] at null
    contradiction
  · intro eq
    subst ref
    have ownedWindow : StreamOwned h r w :=
      ⟨z, good.live.hz, Or.inr ⟨ds, d, good.live.zst, good.live.hs, Or.inr (Or.inl win)⟩⟩
    exact unowned w (by simp [ByteRoot, pointer]) ownedWindow

theorem caller_input_array {h : Heap} {r : ZStreamRef} {ds io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_in = .ref ref io) :
    ∃ array, Space.get h ref = some array ∧ io + z.avail_in.toNat ≤ array.size := by
  obtain ⟨z0, get0, caller, _, _⟩ := buffers
  have same : z0 = z := Option.some.inj (get0.symm.trans good.live.hz)
  subst z0
  rcases caller with null | ⟨⟨xs, bytes⟩, _, _⟩
  · rw [pointer] at null
    contradiction
  · rcases bytes with null | ⟨ref0, off0, array, address, data, bound, _⟩
    · have contradiction := null.1
      rw [pointer] at contradiction
      contradiction
    · have addresses := Ptr.ref.inj (address.symm.trans pointer)
      rcases addresses with ⟨refs, offsets⟩
      subst ref0 off0
      exact ⟨array, data, bound⟩

end Zlib.Deflate.Engine.Proofs
