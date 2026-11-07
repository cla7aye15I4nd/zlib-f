import ZlibF.Proof.«trees.c.payload-state»
import ZlibF.Math.DeflatePayload

/-! # trees.c: source-ordered compress_block fragments

These names expose the existing expressions for proofs. The full source
equality checks their order independently of any execution proof.
-/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out

/-- Actual literal/match branch after the three symbol-byte reads. -/
def cbSymbol (s : DeflateStatePtr) (ltree dtree : CtDataPtr) (dist : UInt32) (lc : Int32) : M Unit := do
  if dist == 0 then
    send_code s lc.toInt ltree
  else
    let code := (← Ptr.index (.ref .st_length_code 0 : BPtr) lc.toInt).toUInt32
    send_code s (code + (i2u LITERALS) + 1).toNat ltree
    let extra ← Ptr.index (.ref .st_extra_lbits 0 : IPtr) code.toNat
    let mut lc := lc
    if extra != 0 then
      lc ← isub lc (← Ptr.index (.ref .st_base_length 0 : IPtr) code.toNat)
      send_bits s lc extra
    let dist := dist - 1
    let code := (← d_code dist).toUInt32
    send_code s code.toNat dtree
    let extra ← Ptr.index (.ref .st_extra_dbits 0 : IPtr) code.toNat
    if extra != 0 then
      let dist := dist - (i2u (← Ptr.index (.ref .st_base_dist 0 : IPtr) code.toNat))
      send_bits s (u2i dist) extra

/-- Actual symbol-byte reads and unsigned cursor increments in source order. -/
def cbReadSymbol (s : DeflateStatePtr) (sx : UInt32) : M (UInt32 × UInt32 × Int32) := do
  let sb := (← rd s).sym_buf
  let b0 ← Ptr.index sb sx.toNat
  let sx := sx + 1
  let dist : UInt32 := b0.toUInt32 &&& 0xff
  let b1 ← Ptr.index sb sx.toNat
  let sx := sx + 1
  let dist := dist + ((b1.toUInt32 &&& 0xff) <<< 8)
  let b2 ← Ptr.index sb sx.toNat
  let sx := sx + 1
  let lc := u8i b2
  pure (sx, dist, lc)

/-- The actual body groups the reads before executing its branch. -/
def cbReadBody (s : DeflateStatePtr) (ltree dtree : CtDataPtr) (sx : UInt32) : M UInt32 := do
  let (sx, dist, lc) ← cbReadSymbol s sx
  cbSymbol s ltree dtree dist lc
  pure sx

/-- Actual do-while condition, including its state read. -/
def cbCondition (s : DeflateStatePtr) (sx : UInt32) : M (Bool × UInt32) := do
  pure (decide (sx < (← rd s).sym_next), sx)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- The entire actual function, with the three named source fragments.
This theorem asserts no execution or format contract. -/
theorem compress_block_eq (s : DeflateStatePtr) (ltree dtree : CtDataPtr) :
    compress_block s ltree dtree = (do
      if (← rd s).sym_next != 0 then
        let _ ← cdoWhile (cbReadBody s ltree dtree) (cbCondition s) 0
        pure ()
      send_code s END_BLOCK.toInt ltree) := by
  unfold compress_block cbReadBody cbReadSymbol cbSymbol cbCondition
  simp only [M_bind_assoc, M_pure_bind, merge_ite_bind]

/-- The two loaded bytes reconstruct the stored unsigned distance exactly. -/
theorem cb_distance_toNat (lo hi : UInt8) :
    ((lo.toUInt32 &&& (0xff : UInt32)) + ((hi.toUInt32 &&& (0xff : UInt32)) <<< (8 : UInt32))).toNat =
      lo.toNat + 256 * hi.toNat := by
  have hlo := lo.toNat_lt
  have hhi := hi.toNat_lt
  have h0 : (lo.toUInt32 &&& (0xff : UInt32)).toNat = lo.toNat := by
    rw [UInt32.toNat_and]
    simp only [UInt8.toNat_toUInt32, show (0xff : UInt32).toNat = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h1 : (hi.toUInt32 &&& (0xff : UInt32)).toNat = hi.toNat := by
    rw [UInt32.toNat_and]
    simp only [UInt8.toNat_toUInt32, show (0xff : UInt32).toNat = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [UInt32.toNat_add, UInt32.toNat_shiftLeft, h0, h1]
  simp only [show (8 : UInt32).toNat % 32 = 8 from rfl, Nat.shiftLeft_eq]
  omega

/-- All three actual reads execute before any output write. The loaded
symbol and the three cursor increments agree with the original buffer;
output/symbol aliasing is handled by the explicit no-overtaking bound. -/
theorem cbReadSymbol_run {h0 h : Heap} {id b : Nat} {d0 d : DeflateState} {buf0 buf : Array UInt8}
    {w : List Bool} (ht : EmitState id b h0 d0 buf0 w h d buf) (sx : UInt32) (j offset : Nat)
    (hsx : sx.toNat = j) (hj32 : j + 3 < 2 ^ 32) (hoff : d0.lit_bufsize.toNat = offset)
    (hbuf : offset + j + 2 < buf0.size)
    (hno : 8 * d0.pending.toNat + d0.bi_valid.toInt.toNat + w.length ≤ 8 * (offset + j)) :
    cbReadSymbol (Sp id) sx h = .ok ((UInt32.ofNat (j + 3),
      UInt32.ofNat (buf0[offset + j]!.toNat + 256 * buf0[offset + j + 1]!.toNat),
      u8i buf0[offset + j + 2]!), h) := by
  have h1 : (sx + 1).toNat = j + 1 := by rw [toNat_add_one_u32 (by omega), hsx]
  have h2 : (sx + 1 + 1).toNat = j + 2 := by rw [toNat_add_one_u32 (by omega), h1]
  have h3 : (sx + 1 + 1 + 1).toNat = j + 3 := by rw [toNat_add_one_u32 (by omega), h2]
  have hs3 : sx + 1 + 1 + 1 = UInt32.ofNat (j + 3) := by
    apply UInt32.toNat_inj.mp
    rw [h3, UInt32.toNat_ofNat', Nat.mod_eq_of_lt hj32]
  have idx0 := ht.symbol_byte offset j hoff (by omega) hno
  have idx1 := ht.symbol_byte offset (j + 1) hoff (by omega) (by omega)
  have idx2 := ht.symbol_byte offset (j + 2) hoff (by omega) (by omega)
  simp only [bind_app, rd_run ht.inv.base.dstate] at idx0 idx1 idx2
  have hdist : (buf0[offset + j]!.toUInt32 &&& (0xff : UInt32)) +
      ((buf0[offset + (j + 1)]!.toUInt32 &&& (0xff : UInt32)) <<< (8 : UInt32)) =
      UInt32.ofNat (buf0[offset + j]!.toNat + 256 * buf0[offset + j + 1]!.toNat) := by
    apply UInt32.toNat_inj.mp
    rw [cb_distance_toNat, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by
      have h0 := UInt8.toNat_lt buf0[offset + j]!
      have h1 := UInt8.toNat_lt buf0[offset + j + 1]!
      omega)]
    rw [Nat.add_assoc]
  unfold cbReadSymbol
  simp only [bind_app, rd_run ht.inv.base.dstate]
  rw [hsx, idx0]
  simp only []
  rw [h1, idx1]
  simp only []
  rw [h2, idx2]
  simp only [pure_app, hs3, hdist, Nat.add_assoc]

end Zlib.Trees.Proofs
