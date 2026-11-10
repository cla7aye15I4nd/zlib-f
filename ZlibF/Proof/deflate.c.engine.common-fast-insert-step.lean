import ZlibF.Proof.«deflate.c.engine.match-insert-full-storage»

/-! # The actual fast match-insertion step and its complete heap effects -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- `s->strstart++; INSERT_STRING(s, s->strstart, hash_head);`
The two actual statements in the fast match-insertion do-loop. -/
def fastInsertBody (s : DeflateStatePtr) (_ : UInt32) : M UInt32 := do
  wr s (fun d => {d with strstart := d.strstart + 1})
  INSERT_STRING s (← rd s (·.strstart))

/-- `while (--s->match_length != 0);`
The actual fast do-loop condition, including its counter store. -/
def fastInsertCond (s : DeflateStatePtr) (head : UInt32) : M (Bool × UInt32) := do
  wr s (fun d => {d with match_length := d.match_length - 1})
  pure ((← rd s (·.match_length)) != 0, head)

def fastCountDown (d : DeflateState) : DeflateState := {d with match_length := d.match_length - 1}

/-- Only the insertion key, position and actual fast counter change. -/
def FastInsertFrame (before after : DeflateState) : Prop :=
  after = {before with strstart := after.strstart, ins_h := after.ins_h, match_length := after.match_length}

/-- These transparent fragments are exactly the lambdas in the actual
translated fast insertion loop. Neither the loop nor its counter is
replaced by the slow strategy's previous-length counter. -/
theorem fast_insert_source (s : DeflateStatePtr) (head : UInt32) :
    cdoWhile
      (fun (_ : UInt32) => do
        wr s (fun d => {d with strstart := d.strstart + 1})
        INSERT_STRING s (← rd s (·.strstart)))
      (fun hh => do
        wr s (fun d => {d with match_length := d.match_length - 1})
        pure ((← rd s (·.match_length)) != 0, hh)) head =
      cdoWhile (fastInsertBody s) (fastInsertCond s) head := rfl

theorem fast_count_down_good {h : Heap} {r : ZStreamRef} {ds top : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (chains : HeapChains h d top) :
    DGood (setD h ds (fastCountDown d)) r ds z (fastCountDown d) ∧
      HeapChains (setD h ds (fastCountDown d)) (fastCountDown d) top := by
  simpa only [fastCountDown, matchState] using matchState_good good chains d.match_start (d.match_length - 1)

theorem fast_insert_frame_step {before state : DeflateState}
    (frame : FastInsertFrame before state) (key : UInt32) :
    FastInsertFrame before (fastCountDown {bumpStart state with ins_h := key}) := by
  unfold FastInsertFrame at *
  rw [frame]
  rfl

/-- A complete actual fast insertion iteration preserves its real hash
frontier and rolling key. The input and byte arrays do not change; all
stores remain in the stream's private objects with no allocations. -/
theorem fast_match_insert_step_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (positive : 1 ≤ d.match_length.toNat) (lookahead : 3 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + d.match_length.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (head : UInt32) :
    ∃ key candidate mid after,
      let result := fastCountDown {bumpStart d with ins_h := key}
      fastInsertBody (some (.tab ds)) head h = .ok (candidate, mid) ∧
      fastInsertCond (some (.tab ds)) candidate mid = .ok ((result.match_length != 0, candidate), after) ∧
      DGood after r ds z result ∧ HeapChains after result (result.strstart.toNat + 1) ∧
      after.bytes w = some wa ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.match_length.toNat = d.match_length.toNat - 1 ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h ∧
      FastInsertFrame d result ∧ after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have bumped := bump_start_good good chains win get (by omega)
  let hb := setD h ds (bumpStart d)
  have getB : hb.bytes w = some wa := get
  have primed : InsHForm (bumpStart d).hash_shift (bumpStart d).hash_mask (bfn wa)
      (bumpStart d).strstart.toNat (bumpStart d).ins_h := by
    change InsHForm d.hash_shift d.hash_mask (bfn wa) (bumpStart d).strstart.toNat d.ins_h
    rw [bumped.1]
    exact form
  obtain ⟨key, candidate, mid, insert, goodI, chainsAt, bytesI, formI, storageI, shapeI, fullI, allocI, nextI⟩ :=
    current_insert_full_storage_at bumped.2.1 bumped.2.2.1.at win getB (by rw [bumped.1]; omega)
      bumped.2.2.2 (by
        change (bumpStart d).strstart.toNat + 3 ≤ (bumpStart d).strstart.toNat + d.lookahead.toNat
        omega) primed
  have chainsI : HeapChains mid {bumpStart d with ins_h := key} ((bumpStart d).strstart.toNat + 1) :=
    chainsAt.collapse rfl
  let di := {bumpStart d with ins_h := key}
  let result := fastCountDown di
  let after := setD mid ds result
  have kept := fast_count_down_good goodI chainsI
  have startA : result.strstart.toNat = d.strstart.toNat + 1 := bumped.1
  have countA : result.match_length.toNat = d.match_length.toNat - 1 := u32_sub_one positive
  have writeB : wr (some (.tab ds)) bumpStart h = .ok ((), hb) := by simp [wrD_eq, good.live.hs, hb]
  have body : fastInsertBody (some (.tab ds)) head h = .ok (candidate, mid) := by
    unfold fastInsertBody
    change (do
      wr (some (.tab ds)) bumpStart
      INSERT_STRING (some (.tab ds)) (← rd (some (.tab ds)) (·.strstart))) h = _
    rw [bind_app, writeB]
    have stateB : hb.dstates ds = some (bumpStart d) := bumped.2.1.live.hs
    simp only [bind_app, rdD_eq, stateB]
    exact insert
  have condition : fastInsertCond (some (.tab ds)) candidate mid =
      .ok ((result.match_length != 0, candidate), after) := by
    unfold fastInsertCond
    change (do
      wr (some (.tab ds)) fastCountDown
      pure ((← rd (some (.tab ds)) (·.match_length)) != 0, candidate)) mid = _
    have write : wr (some (.tab ds)) fastCountDown mid = .ok ((), after) := by
      simp [wrD_eq, goodI.live.hs, after, result, di]
    rw [bind_app, write]
    have stateA : after.dstates ds = some result := kept.1.live.hs
    simp only [bind_app, rdD_eq, stateA]
    rfl
  have shapeB := shape_setD good.live.hs (bumpStart d)
  have fullB : Frame h hb (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame h ds _) (fun _ same => Or.inr (Or.inl same))
  have shapeC := shape_setD goodI.live.hs result
  have fullC : Frame mid after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) :=
    full_frame_weaken (state_store_full_frame mid ds _) (fun _ same => Or.inr (Or.inl same))
  refine ⟨key, candidate, mid, after, body, condition, kept.1, kept.2, ?_, startA, countA,
    formI, rfl, bytesI, ?_, (shapeB.trans shapeI).trans shapeC,
    full_frame_trans_shape (full_frame_trans_shape fullB fullI shapeB) fullC (shapeB.trans shapeI), allocI, nextI⟩
  · change mid.bytes w = some wa
    rw [bytesI]; exact getB
  · exact ((byte_frame_setD h ds (bumpStart d)).trans storageI).trans (byte_frame_setD mid ds result)

end Zlib.Deflate.Engine.Proofs
