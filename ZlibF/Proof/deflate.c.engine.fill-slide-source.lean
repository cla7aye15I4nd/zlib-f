import ZlibF.Proof.«deflate.c.engine.fill-source»
import ZlibF.Proof.«deflate.c.engine.fill-read-resume»
import ZlibF.Proof.«deflate.c.engine.block-balance»
import ZlibF.Proof.«deflate.c.engine.slide»

/-! # The source sliding prefix and its actual machine counts -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The contiguous source statements in the taken sliding branch. -/
def fillSlide (s : DeflateStatePtr) (d : DeflateState) (wsize more : UInt32) : M Unit := do
  memcpyB d.window (← padd d.window wsize.toNat) (wsize - more).toNat
  wr s (fun d => { d with match_start := d.match_start - wsize })
  wr s (fun d => { d with strstart := d.strstart - wsize })
  let block_start ← lsub (← rd s (·.block_start)) wsize.toUInt64.toInt64
  wr s (fun d => { d with block_start })
  wr s (fun d => { d with insert := if d.insert > d.strstart then d.strstart else d.insert })
  slide_hash s

def fillAfterSlide (s : DeflateStatePtr) (more : UInt32) : M Bool := do
  let strm ← rd s (·.strm)
  if (← zrd strm (·.avail_in)) == 0 then return true
  let d ← ldDeflateState s
  let dst ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat
  let n ← read_buf strm dst more
  wr s (fun d => { d with lookahead := d.lookahead + n })
  fillPrime s
  pure false

theorem fill_body_slide_source (s : DeflateStatePtr) (wsize : UInt32) (brk : Bool) :
    fillBody s wsize brk = (do
      let d ← ldDeflateState s
      let more := fillMore d
      if d.strstart ≥ wsize + (d.w_size - MIN_LOOKAHEAD_u) then
        fillSlide s d wsize more
        fillAfterSlide s (more + wsize)
      else fillAfterSlide s more) := by
  unfold fillBody fillSlide fillAfterSlide fillMore
  simp only [M_bind_assoc, M_pure_bind, fill_ite_bind]

def slideBeforeHash (d : DeflateState) : DeflateState :=
  { d with
    match_start := d.match_start - d.w_size,
    strstart := d.strstart - d.w_size,
    block_start := Int64.ofInt (d.block_start.toInt - (d.w_size.toNat : Int)),
    insert := if d.insert > d.strstart - d.w_size then d.strstart - d.w_size else d.insert }

def slideState (d : DeflateState) : DeflateState := { slideBeforeHash d with slid := 1 }

theorem slide_window_sizes {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) :
    512 ≤ d.w_size.toNat ∧ d.w_size.toNat ≤ 32768 := by
  constructor
  · rw [good.inv.wsize]
    exact Nat.pow_le_pow_right (n := 2) (by decide) good.inv.wbits_lo
  · rw [good.inv.wsize]
    exact Nat.pow_le_pow_right (n := 2) (by decide) good.inv.wbits_hi

theorem slide_threshold {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) :
    (d.w_size + (d.w_size - MIN_LOOKAHEAD_u)).toNat = 2 * d.w_size.toNat - 262 := by
  have bounds := slide_window_sizes good
  have sub : (d.w_size - MIN_LOOKAHEAD_u).toNat = d.w_size.toNat - 262 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; change 262 ≤ _; omega)]
    rfl
  rw [UInt32.toNat_add, sub, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The same allocation contains disjoint source and destination ranges.
The copy count is exactly the old valid endpoint minus one window. -/
theorem fill_slide_counts {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    d.w_size.toNat + 1 ≤ d.strstart.toNat ∧
      (d.w_size - fillMore d).toNat = fillEnd d - d.w_size.toNat ∧
      (d.w_size - fillMore d).toNat ≤ d.w_size.toNat ∧
      d.w_size.toNat + (d.w_size - fillMore d).toNat ≤ wa.size ∧
      (slideState d).strstart.toNat = d.strstart.toNat - d.w_size.toNat ∧
      fillEnd (slideState d) = fillEnd d - d.w_size.toNat ∧
      fillEnd (slideState d) ≤ d.w_size.toNat ∧
      (fillMore d + d.w_size).toNat = d.window_size.toNat - fillEnd (slideState d) ∧
      ¬ (slideState d).strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u) := by
  have bounds := slide_window_sizes good
  have extent := window_extent good win get
  have more := fill_more_nat good win get range
  have threshold := slide_threshold good
  rw [GE.ge, UInt32.le_iff_toNat_le, threshold] at taken
  have wsz := good.inv.wsz
  have current : fillEnd d = d.strstart.toNat + d.lookahead.toNat := rfl
  have smaller : (fillMore d).toNat ≤ d.w_size.toNat := by omega
  have sub : (d.w_size - fillMore d).toNat = d.w_size.toNat - (fillMore d).toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr smaller)
  have start : (slideState d).strstart.toNat = d.strstart.toNat - d.w_size.toNat := by
    change (d.strstart - d.w_size).toNat = _
    exact UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))
  have endpoint : fillEnd (slideState d) = fillEnd d - d.w_size.toNat := by
    change (slideState d).strstart.toNat + d.lookahead.toNat = _
    rw [start]
    omega
  have added : (fillMore d + d.w_size).toNat = (fillMore d).toNat + d.w_size.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, by omega, by omega, by omega, start, endpoint, by omega, by omega, ?_⟩
  rw [GE.ge, UInt32.le_iff_toNat_le, threshold, start]
  omega

end Zlib.Deflate.Engine.Proofs
