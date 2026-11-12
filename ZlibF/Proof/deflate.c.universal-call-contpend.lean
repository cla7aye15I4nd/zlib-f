import ZlibF.Proof.«deflate.c.universal-call-cont»
import ZlibF.Proof.«deflate.c.universal-flush-cursor»

/-!
# deflate.c: the entry phase with output pending, at any cursor

Owner 2 of the deflate split (`deflate_call`). With output pending, the entry phase stores
`last_flush := flush` and runs `flush_pending` at whatever cursor the previous call left. Then it
returns `Z_OK` on a full output, refuses new input after `Z_FINISH`, or continues. This module
evaluates the entry phase in terms of the flush's run (no cursor premise).
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- **The entry phase with output pending**, given the run of its flush. -/
theorem entry_pending_eval {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {flush : Int32} (good : DGood h r ds z d) (accepted : ¬ DeflateRefuses z d flush)
    (avail : z.avail_out ≠ 0) (pending : d.pending ≠ 0) {after : Heap} {z' : ZStream} {d' : DeflateState}
    (run : flush_pending (some r) (setD h ds { d with last_flush := flush }) = .ok ((), after))
    (hz : r.get after = some z') (hs : after.dstates ds = some d') (k : DeflateStatePtr → M Int32) :
    entryPhase (some r) flush k h =
      if z'.avail_out = 0 then .ok (Z_OK, setD after ds { d' with last_flush := -1 })
      else if d'.status = FINISH_STATE ∧ z'.avail_in ≠ 0 then ERR_RETURN (some r) Z_BUF_ERROR after
      else k (some (.tab ds)) after := by
  unfold DeflateRefuses at accepted
  have flushLow : 0 ≤ flush.toInt := by omega
  have flushHigh : flush.toInt ≤ 5 := by omega
  have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
  have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
    by_cases empty : z.avail_in = 0
    · simp [empty]
    · have : z.next_in ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, empty⟩))))
      simp [this]
  have fin : ¬ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH) :=
    fun e => accepted (Or.inr (Or.inr (Or.inr (Or.inr e))))
  have finTest : (d.status == FINISH_STATE && flush != Z_FINISH) = false := by
    by_cases st : d.status = FINISH_STATE
    · have : flush = Z_FINISH := Classical.byContradiction fun ne => fin ⟨st, ne⟩
      simp [st, this]
    · simp [st]
  have checked := stateCheck_live good.live
  obtain ⟨high, low⟩ := entry_valid_flags flushLow flushHigh
  unfold entryPhase
  simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
    high, low, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
    zrd_eq, good.live.hz, good.live.zst, castDeflateState,
    ldZStream_ok good.live.hz, ldDeflateState_tab good.live.hs,
    show (z.next_out == .null) = false from beq_eq_false_iff_ne.mpr out,
    inputs, Bool.or_false, finTest,
    show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr avail,
    wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pending, ite_true, run]
  by_cases full : z'.avail_out = 0
  · simp [zrd_eq, hz, full, wrD_eq, hs, bind_app]
  · by_cases c : d'.status = FINISH_STATE ∧ z'.avail_in ≠ 0
    · simp [zrd_eq, hz, full, rdD_eq, hs, bind_app, c.1, c.2]
    · rw [if_neg full, if_neg c]
      simp [zrd_eq, hz, full, rdD_eq, hs, bind_app]
      split
      · rename_i t
        exact absurd ⟨t.1, t.2⟩ c
      · rfl

/-- **The state after the entry flush keeps the invariant** from the state before the call, with
`last_flush := v` for a value in range that is a reset value in the header states that need one.
The flush wrote the output and moved the cursor (`pendingState`); `pending_buf` is unchanged. -/
theorem pend_lift {h after : Heap} {r : ZStreamRef} {ds pb po produced : Nat} {z z' : ZStream}
    {d d1 : DeflateState} {flush : Int32} {n : UInt32}
    (inv : DInv h r ds z d) (pbuf : d.pending_buf = .ref (.blk pb) 0) (cursor0 : d.pending_out = .ref (.blk pb) po)
    (good1 : DGood (setD h ds { d with last_flush := flush }) r ds z { d with last_flush := flush })
    (buffers1 : StreamBuffers (setD h ds { d with last_flush := flush }) r) (out : z.next_out ≠ .null)
    (good' : DGood after r ds z' d1) (buffers' : StreamBuffers after r)
    (frame : StageFrame (setD h ds { d with last_flush := flush }) after r ds pb { d with last_flush := flush } z z' produced)
    (bytesPb : after.bytes pb = h.bytes pb)
    (stateEq : d1 = pendingState { d with last_flush := flush } (.ref (.blk pb) (po + n.toNat)) n)
    (nle : n.toNat ≤ d.pending.toNat) (v : Int32) (vRange : -2 ≤ v.toInt ∧ v.toInt ≤ 5)
    (vHeader : d.status = INIT_STATE ∨ d.status = GZIP_STATE → v = -2 ∨ v = -1) :
    DInv (setD after ds { d1 with status := d1.status, last_flush := v }) r ds z'
      { d1 with status := d1.status, last_flush := v } := by
  obtain ⟨_, _, _, static, win, prv, hd, _⟩ := StageFrame.call_facts frame good1 buffers1 pbuf out
  have stEq : d1.status = d.status := by rw [stateEq]; rfl
  have st : GoodStatus d1.status := by rw [stEq]; exact inv.good.live.status
  obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
  have key : b0 = pb := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst key
  obtain ⟨buf, get, _⟩ := blocks.ba
  have pbuf1 : d1.pending_buf = .ref (.blk b0) 0 := by rw [stateEq]; exact pbuf
  have trees' := trees_at_of_good good' pbuf1 (by rw [bytesPb]; exact get)
  obtain ⟨good'', _, _⟩ := good_status_flush good' trees' buffers' d1.status v st
  have fields : HeaderFields d { d1 with status := d1.status, last_flush := v } := by
    unfold HeaderFields; rw [stateEq]; rfl
  have pendEq : d1.pending = d.pending - n.toUInt64 := by rw [stateEq]; rfl
  have outEq : d1.pending_out = if d.pending - n.toUInt64 == 0 then d.pending_buf else .ref (.blk b0) (po + n.toNat) := by
    rw [stateEq]; rfl
  have pendNat : (d.pending - n.toUInt64).toNat = d.pending.toNat - n.toNat := by
    rw [UInt64.toNat_sub_of_le]
    · simp
    · rw [UInt64.le_iff_toNat_le]; simp; omega
  have shape' : Shape { d1 with status := d1.status, last_flush := v } :=
    Shape.of_fields inv.shape fields vRange (fun hs => vHeader (by rw [← stEq]; exact hs))
      (fun neg => by
        have w : d1.wrap = d.wrap := by rw [stateEq]; rfl
        show d1.status = FINISH_STATE
        rw [stEq]; exact inv.shape.trailer (by rw [← w]; exact neg))
      (by show d1.bi_valid.toInt ≤ 7; rw [stateEq]; exact inv.shape.biValid)
      (fun zero => by
        show d1.pending_out = d1.pending_buf
        change d1.pending = 0 at zero
        rw [outEq, pbuf1, ← pendEq, zero]
        simp [pbuf])
  refine inv.lift good'' (by obtain ⟨za, zf⟩ := inv.alloc; exact ⟨frame.1.1.1.2.2.2.2.2.2.2.1.trans za,
      frame.1.1.1.2.2.2.2.2.2.2.2.1.trans zf⟩) (static.trans rfl) shape' fields win prv hd
    (fun b a e g => ⟨a, ?_, fun _ _ => rfl⟩) ?_
  · have be : b = b0 := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using e.symm
    subst be
    show after.bytes b = some a
    rw [bytesPb]; exact g
  · intro b off e nz
    change d1.sym_next ≠ 0 at nz
    have symEq : d1.sym_next = d.sym_next := by rw [stateEq]; rfl
    change d1.pending_out = _ at e
    change off + d1.pending.toNat ≤ d1.lit_bufsize.toNat
    have litEq : d1.lit_bufsize = d.lit_bufsize := by rw [stateEq]; rfl
    rw [litEq, pendEq, pendNat]
    have old := inv.symbols.below b0 po cursor0 (by rw [← symEq]; exact nz)
    rw [outEq] at e
    split at e
    · rename_i z0
      have : d.pending.toNat - n.toNat = 0 := by
        rw [← pendNat, show d.pending - n.toUInt64 = 0 by simpa using z0]; rfl
      rw [pbuf] at e
      simp only [Ptr.ref.injEq] at e
      omega
    · simp only [Ptr.ref.injEq, BRef.blk.injEq] at e
      omega

end Zlib.Deflate.Universal.Call
