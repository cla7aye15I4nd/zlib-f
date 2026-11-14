import ZlibF.Proof.«deflate.c.engine.fill-read-invariant»
import ZlibF.Proof.«deflate.c.engine.fill-padding-invariant»
import ZlibF.Proof.«deflate.c.engine.fill-initial»
import ZlibF.Spec.Functional.Checksums

/-! # Complete non-sliding fill_window resumption with new input -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

def resumedFillState (d : DeflateState) (n : UInt32) (copied : Array UInt8) : DeflateState :=
  paddedState (resumeReadState d n copied)

def resumedFillHeap (h : Heap) (r : ZStreamRef) (ds w : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (io : Nat) (ia wa : Array UInt8) : Heap :=
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  paddedHeap (resumeReadHeap h r ds w z d ref io ia wa) ds w (resumeReadState d n copied) copied

theorem resumed_fill_record (d : DeflateState) (n : UInt32) (copied : Array UInt8) :
    ∃ key high, resumedFillState d n copied =
      { d with lookahead := d.lookahead + n, ins_h := key, high_water := high } := by
  obtain ⟨key, fields⟩ := resume_read_record d n copied
  refine ⟨key, UInt64.ofNat (paddingTarget (resumeReadState d n copied)), ?_⟩
  unfold resumedFillState paddedState
  rw [fields]

set_option maxHeartbeats 1200000 in
/-- `local void fill_window(deflate_state *s)`.
The whole resumed call with new input, short lookahead, no slide and no
deferred insertion. Old window contents and current position are arbitrary.
The source's capacity test proves that its outer loop stops after this read.
Padding executes through both possible high-water write paths.
-/
theorem fill_window_resume_read {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (range : fillEnd d ≤ d.window_size.toNat)
    (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ fillEnd d + (rbLen z.avail_in (fillMore d)).toNat ≤ io ∨
      io + (rbLen z.avail_in (fillMore d)).toNat ≤ fillEnd d) :
    fill_window (some (.tab ds)) h = .ok ((), resumedFillHeap h r ds w z d ref io ia wa) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let df := resumeReadState d n copied
  let hr := resumeReadHeap h r ds w z d ref io ia wa
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  have goodR : DGood hr r ds z' df := resume_read_good good get
  have count := resume_read_counts good win get range
  have capacity := fill_room_no_slide good win get range short noSlide
  obtain ⟨key, fields⟩ := resume_read_record d n copied
  change df = _ at fields
  have look : df.lookahead = d.lookahead + n := by rw [fields]
  have rangeR : fillEnd df ≤ df.window_size.toNat := by
    rw [fields]
    exact count.2.2
  have getR : hr.bytes w = some copied := by simp [hr, resumeReadHeap, n, copied]
  have winR : df.window = .ref (.blk w) 0 := by rw [fields]; exact win
  have next : fillCond (some (.tab ds)) false hr = .ok ((false, false), hr) := by
    have exhausted : df.lookahead < MIN_LOOKAHEAD_u → z'.avail_in = 0 := by
      intro small
      rw [UInt32.lt_iff_toNat_lt, look, count.2.1] at small
      change d.lookahead.toNat + n.toNat < 262 at small
      have nCount : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
      have all : n = z.avail_in := UInt32.toNat_inj.mp (by omega)
      simp only [z', readStream, all, UInt32.sub_self]
    unfold fillCond
    simp only [bind_app, ldDeflateState_tab goodR.live.hs, Bool.false_eq_true, if_false, goodR.live.back]
    by_cases small : df.lookahead < MIN_LOOKAHEAD_u
    · simp only [small, if_true, bind_app, zrd_eq, goodR.live.hz, exhausted small]
      rfl
    · simp only [small, if_false]
      rfl
  have body : fillBody (some (.tab ds)) d.w_size false h = .ok (false, hr) :=
    fill_body_resume_read good win get (window_writable good win) range short noSlide insert wrap
      pointer input inputBound nonempty separate
  have loop := do_once body next
  have pad := fill_high_water_complete goodR winR getR (window_writable goodR winR) rangeR
  rw [fill_window_source]
  simp only [bind_app, rdD_eq, good.live.hs, loop]
  exact pad

set_option maxHeartbeats 1200000 in
/-- Complete resumed execution and its engine boundary on the same heap.
The initialized padding, chains and conditional rolling hash are all
derived from actual read and padding executions.
-/
theorem fill_window_resume_complete {h : Heap} {r : ZStreamRef} {ds w io top : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ fillEnd d + (rbLen z.avail_in (fillMore d)).toNat ≤ io ∨
      io + (rbLen z.avail_in (fillMore d)).toNat ≤ fillEnd d) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    let read := resumeReadState d n copied
    let final := resumedFillState d n copied
    let output := fillRange copied (paddingStart read) (paddingCount read) 0
    let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    let after := resumedFillHeap h r ds w z d ref io ia wa
    fill_window (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z' final ∧ HeapChains after final top ∧
      final.window = .ref (.blk w) 0 ∧ after.bytes w = some output ∧
      fillEnd final ≤ final.window_size.toNat ∧
      min (fillEnd final + 258) final.window_size.toNat ≤ final.high_water.toNat ∧
      (3 ≤ final.lookahead.toNat → InsHForm final.hash_shift final.hash_mask
        (bfn output) final.strstart.toNat final.ins_h) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let dr := resumeReadState d n copied
  let hr := resumeReadHeap h r ds w z d ref io ia wa
  have goodR := resume_read_good (ref := ref) (io := io) (ia := ia) good get
  have chainsR := resume_read_chains (ref := ref) (io := io) (ia := ia) good chains win get range
  have count := resume_read_counts good win get range
  obtain ⟨key, fields⟩ := resume_read_record d n copied
  change dr = _ at fields
  have winR : dr.window = .ref (.blk w) 0 := by rw [fields]; exact win
  have getR : hr.bytes w = some copied := by simp [hr, resumeReadHeap, n, copied]
  have rangeR : fillEnd dr ≤ dr.window_size.toNat := by rw [fields]; exact count.2.2
  refine ⟨fill_window_resume_read good win get range short noSlide insert wrap pointer input inputBound nonempty separate,
    padded_good goodR winR getR rangeR, padded_chains goodR chainsR winR getR rangeR,
    winR, ?_, rangeR, padded_initialized goodR winR getR rangeR, ?_⟩
  · simp [resumedFillHeap, paddedHeap, dr, hr, n, copied]
  · intro large
    apply padded_form goodR winR getR rangeR large
    change 3 ≤ dr.lookahead.toNat at large
    rw [fields] at large
    have ready : d.lookahead + n ≥ 3 := UInt32.le_iff_toNat_le.mpr large
    have params : HashParams d.hash_size d.hash_shift d.hash_mask := hash_parameters good.inv
    have primed : InsHForm d.hash_shift d.hash_mask (bfn copied) d.strstart.toNat dr.ins_h :=
      resume_prime_form (d := { d with lookahead := d.lookahead + n }) (wa := copied)
        params
        (by rw [size_copyRange, (window_extent good win get).1]; exact count.2.2) ready
    change InsHForm dr.hash_shift dr.hash_mask (bfn copied) dr.strstart.toNat dr.ins_h
    simpa only [fields] using primed

end Zlib.Deflate.Engine.Proofs
