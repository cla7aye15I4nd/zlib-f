import ZlibF.Proof.«deflate.c.engine.fill-read-prefix»

/-! # Complete non-sliding refill with a real deferred-insertion count -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

set_option maxHeartbeats 3000000 in
/-- Actual read, complete pending-insertion loop, outer-loop stop and
high-water padding. insert need not be zero. The lower hash frontier and
insert<=strstart are representation facts, not callee contracts.
-/
theorem fill_window_pending_complete {h : Heap} {r : ZStreamRef} {ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat - d.insert.toNat))
    (pending : d.insert.toNat ≤ d.strstart.toNat)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    ∃ after result output,
      fill_window (some (.tab ds)) h = .ok ((), after) ∧ DGood after r ds z' result ∧
      HeapChains after result (result.strstart.toNat - result.insert.toNat) ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some output ∧
      fillEnd result ≤ result.window_size.toNat ∧
      min (fillEnd result + 258) result.window_size.toNat ≤ result.high_water.toNat ∧
      (3 ≤ result.lookahead.toNat → result.insert = 0 ∧
        InsHForm result.hash_shift result.hash_mask (bfn output) result.strstart.toNat result.ins_h) ∧
      result = { d with
        lookahead := d.lookahead + n, ins_h := result.ins_h, insert := result.insert, high_water := result.high_water } ∧
      result.insert.toNat = min d.insert.toNat (2 - result.lookahead.toNat) ∧
      (∀ b, b ≠ w → after.bytes b = h.bytes b) ∧
      (∀ i, i < fillEnd result → bfn output i = bfn copied i) ∧
      (262 ≤ result.lookahead.toNat ∨ z'.avail_in = 0) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let hr := pendingReadHeap h r ds w z d ref io ia wa
  let dr := pendingReadState d n
  have goodR : DGood hr r ds z' dr := pending_read_good good get
  have chainsR : HeapChains hr dr (dr.strstart.toNat - dr.insert.toNat) :=
    pending_read_chains good chains win get range
  have counts := resume_read_counts good win get range
  have rangeR : fillEnd dr ≤ dr.window_size.toNat := counts.2.2
  have getR : hr.bytes w = some copied := by simp [hr, pendingReadHeap, n, copied]
  have winR : dr.window = .ref (.blk w) 0 := win
  obtain ⟨hp, dp, primeRun, goodP, chainsP, bytesP, frameP, countP, formP⟩ :=
    fill_prime_pending goodR chainsR winR getR rangeR pending
  change fillPrime (some (.tab ds)) (pendingReadHeap h r ds w z d ref io ia wa) = .ok ((), hp) at primeRun
  have fields : dp = { d with lookahead := d.lookahead + n, ins_h := dp.ins_h, insert := dp.insert } := by
    unfold PendingInsertFrame at frameP
    rw [frameP]
    rfl
  have lookP : dp.lookahead.toNat = d.lookahead.toNat + n.toNat := by rw [fields]; exact counts.2.1
  have rangeP : fillEnd dp ≤ dp.window_size.toNat := by rw [fields]; exact counts.2.2
  have winP : dp.window = .ref (.blk w) 0 := by rw [fields]; exact win
  have getP : hp.bytes w = some copied := by rw [bytesP]; exact getR
  have capacity := fill_room_no_slide good win get range short noSlide
  have inputCount : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
  have exhausted : dp.lookahead < MIN_LOOKAHEAD_u → z'.avail_in = 0 := by
    intro small
    have less : dp.lookahead.toNat < 262 := UInt32.lt_iff_toNat_lt.mp small
    have all : n = z.avail_in := UInt32.toNat_inj.mp (by omega)
    simp only [z', readStream, all, UInt32.sub_self]
  have condition : fillCond (some (.tab ds)) false hp = .ok ((false, false), hp) := by
    unfold fillCond
    simp only [bind_app, ldDeflateState_tab goodP.live.hs, Bool.false_eq_true, if_false, goodP.live.back]
    by_cases small : dp.lookahead < MIN_LOOKAHEAD_u
    · simp only [small, if_true, bind_app, zrd_eq, goodP.live.hz, exhausted small]
      rfl
    · simp only [small, if_false]
      rfl
  have body : fillBody (some (.tab ds)) d.w_size false h = .ok (false, hp) := by
    rw [fill_body_slide_source]
    simp only [bind_app, ldDeflateState_tab good.live.hs, noSlide, if_false]
    rw [fill_after_slide_read_prefix good win get range short noSlide wrap pointer input inputBound nonempty separate]
    simp only [bind_app, primeRun, pure_app]
  have loop := do_once body condition
  have pad := fill_high_water_complete goodP winP getP (window_writable goodP winP) rangeP
  let after := paddedHeap hp ds w dp copied
  let result := paddedState dp
  let output := fillRange copied (paddingStart dp) (paddingCount dp) 0
  have run : fill_window (some (.tab ds)) h = .ok ((), after) := by
    rw [fill_window_source]
    simp only [bind_app, rdD_eq, good.live.hs, loop]
    exact pad
  refine ⟨after, result, output, run, padded_good goodP winP getP rangeP,
    padded_chains goodP chainsP winP getP rangeP, winP, ?_, rangeP,
    padded_initialized goodP winP getP rangeP, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [after, output, paddedHeap]
  · intro large
    obtain ⟨zero, form⟩ := formP large
    exact ⟨zero, padded_form goodP winP getP rangeP large form⟩
  · dsimp only [result, paddedState]
    rw [fields]
  · change dp.insert.toNat = min d.insert.toNat (2 - dp.lookahead.toNat)
    have look : dp.lookahead = dr.lookahead := congrArg (·.lookahead) frameP
    rw [look]
    exact countP
  · intro b different
    change (paddedHeap hp ds w dp copied).bytes b = _
    simp only [paddedHeap, setD_bytes, upd_ne _ _ _ _ different, bytesP,
      hr, pendingReadHeap, setD_bytes, ZStreamRef.put_bytes, upd_ne _ _ _ _ different]
  · exact padded_prefix goodP winP getP rangeP
  · by_cases enough : 262 ≤ dp.lookahead.toNat
    · exact Or.inl enough
    · right
      exact exhausted (UInt32.lt_iff_toNat_lt.mpr (by change dp.lookahead.toNat < 262; omega))

end Zlib.Deflate.Engine.Proofs
