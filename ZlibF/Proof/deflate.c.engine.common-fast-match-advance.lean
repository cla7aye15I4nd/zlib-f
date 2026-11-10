import ZlibF.Proof.«deflate.c.engine.common-fast-match-advance-source»
import ZlibF.Proof.«deflate.c.engine.common-fast-match-inserting»
import ZlibF.Proof.«deflate.c.engine.common-fast-match-skipping»

/-! # Both actual fast match-advance branches share one complete contract -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every selected fast match takes its actual insertion guard. Both
branches consume the whole match, keep the fixed input endpoint, reset
the match counter and prime the next hash. Physical storage and resource
effects are exact for the same source run, including short EOF matches. -/
theorem fast_match_advance_frontier_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (selected : 3 ≤ d.match_length.toNat) (bounded : d.match_length.toNat ≤ 258)
    (consumed : d.match_length.toNat ≤ d.lookahead.toNat)
    (range : fillEnd d ≤ d.window_size.toNat) (room : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h) (head : UInt32) :
    ∃ candidate after result,
      fastMatchAdvance (some (.tab ds)) head h = .ok (candidate, after) ∧
      DGood after r ds z result ∧ HeapChains after result result.strstart.toNat ∧ EndFrontier after result ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧ result.match_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + d.match_length.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat - d.match_length.toNat ∧ fillEnd result = fillEnd d ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      result = {d with strstart := result.strstart, ins_h := result.ins_h, match_length := 0, lookahead := d.lookahead - d.match_length} ∧
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  let looked := {d with lookahead := d.lookahead - d.match_length}
  let hl := setD h ds looked
  have first : wr (some (.tab ds)) (fun d => {d with lookahead := d.lookahead - d.match_length}) h = .ok ((), hl) := by
    simp [wrD_eq, good.live.hs, hl, looked]
  have getLook : hl.dstates ds = some looked := by simp [hl]
  by_cases insert : (d.match_length ≤ d.max_lazy_match && (d.lookahead - d.match_length) ≥ MIN_MATCH_u) = true
  · have remaining : d.match_length.toNat + 3 ≤ d.lookahead.toNat := by
      have conditions := insert
      simp only [Bool.and_eq_true, decide_eq_true_eq] at conditions
      have enough := UInt32.le_iff_toNat_le.mp conditions.2
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact consumed)] at enough
      change 3 ≤ d.lookahead.toNat - d.match_length.toNat at enough
      omega
    obtain ⟨candidate, after, result, run, goodA, chainsA, winA, bytesA, zeroA, startA, lookA, endA,
        formA, fieldsA, bytesEqA, storageA, shapeA, fullA, liveA, allocA, nextA⟩ :=
      fast_match_inserting_full_storage good chains win get selected bounded remaining range form head
    have source : fastMatchAdvance (some (.tab ds)) head h =
        (do wr (some (.tab ds)) (fun d => {d with lookahead := d.lookahead - d.match_length})
            wr (some (.tab ds)) (fun d => {d with match_length := d.match_length - 1})
            let hh ← cdoWhile (fastInsertBody (some (.tab ds))) (fastInsertCond (some (.tab ds))) head
            wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + 1})
            pure hh) h := by
      unfold fastMatchAdvance
      simp only [bind_app, first, ldDeflateState_tab getLook, looked, insert, ite_true]
    have endFrontier := end_frontier_of_two chainsA (by rw [lookA]; omega)
    exact ⟨candidate, after, result, source.trans run, goodA, chainsA, endFrontier, winA, bytesA, zeroA,
      startA, lookA, endA, formA, fieldsA, bytesEqA, storageA, shapeA, fullA, liveA, allocA, nextA⟩
  · obtain ⟨after, result, run, goodA, chainsA, endFrontier, winA, bytesA, zeroA, startA, lookA, endA,
        formA, fieldsA, bytesEqA, _wordsEqA, storageA, shapeA, fullA, liveA, allocA, nextA⟩ :=
      fast_match_skipping_frontier_full_storage good chains win get selected bounded consumed range room
    have source : fastMatchAdvance (some (.tab ds)) head h =
        (do (do wr (some (.tab ds)) (fun d => {d with lookahead := d.lookahead - d.match_length})
                wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + d.match_length, match_length := 0})
                let next ← ldDeflateState (some (.tab ds))
                fillInsertSeed (some (.tab ds)) next.window next.strstart)
            pure head) h := by
      unfold fastMatchAdvance
      simp only [M_bind_assoc, bind_app, first, ldDeflateState_tab getLook, looked, insert, Bool.false_eq_true, ite_false]
      cases answer : wr (some (.tab ds)) (fun d => {d with strstart := d.strstart + d.match_length, match_length := 0}) hl with
      | error fault => simp only [answer]
      | ok pair =>
          obtain ⟨unit, heap⟩ := pair
          simp only [answer]
          cases next : ldDeflateState (some (.tab ds)) heap with
          | error fault => simp only [next]
          | ok pair =>
              obtain ⟨state, middle⟩ := pair
              simp only [next]
    refine ⟨head, after, result, ?_, goodA, chainsA, endFrontier, winA, bytesA, zeroA, startA, lookA, endA,
      formA, fieldsA, bytesEqA, storageA, shapeA, fullA, liveA, allocA, nextA⟩
    rw [source, bind_app, run]
    rfl

/-- Projection retaining the earlier physical contract. The stronger
execution also preserves the EOF hash frontier needed by whole loops. -/
theorem fast_match_advance_full_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (selected : 3 ≤ d.match_length.toNat) (bounded : d.match_length.toNat ≤ 258)
    (consumed : d.match_length.toNat ≤ d.lookahead.toNat)
    (range : fillEnd d ≤ d.window_size.toNat) (room : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h) (head : UInt32) :
    ∃ candidate after result,
      fastMatchAdvance (some (.tab ds)) head h = .ok (candidate, after) ∧
      DGood after r ds z result ∧ HeapChains after result result.strstart.toNat ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧ result.match_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + d.match_length.toNat ∧
      result.lookahead.toNat = d.lookahead.toNat - d.match_length.toNat ∧ fillEnd result = fillEnd d ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      result = {d with strstart := result.strstart, ins_h := result.ins_h, match_length := 0, lookahead := d.lookahead - d.match_length} ∧
      after.bytes = h.bytes ∧ ByteFrame h after (fun i => i = ds) ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨candidate, after, result, run, goodA, chainsA, _endA, winA, bytesA, zeroA, startA, lookA, endpoint,
      formA, fieldsA, bytesEqA, storageA, shapeA, frameA, liveA, countA, nextA⟩ :=
    fast_match_advance_frontier_full_storage good chains win get selected bounded consumed range room form head
  exact ⟨candidate, after, result, run, goodA, chainsA, winA, bytesA, zeroA, startA, lookA, endpoint,
    formA, fieldsA, bytesEqA, storageA, shapeA, frameA, liveA, countA, nextA⟩

end Zlib.Deflate.Engine.Proofs
