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

/-- **T2** (offered to batch 1): an entry flush at any cursor keeps the caller's bytes outside the
output range, `pending_buf` and the state, and the `gz_header` records. -/
def EntryKeep : Prop :=
  ∀ {h after : Heap} {r : ZStreamRef} {ds pb produced : Nat} {z z' : ZStream} {d : DeflateState},
    DGood h r ds z d → StreamBuffers h r → d.pending_buf = .ref (.blk pb) 0 → d.bi_valid.toInt < 8 →
    z.next_out ≠ .null → flush_pending (some r) h = .ok ((), after) → r.get after = some z' →
    StreamAccounting z z' 0 produced → CallerKeep h after z ds pb ∧ after.gzheaders = h.gzheaders

/-- What the entry flush of an accepted call with output pending gives, by outcome. -/
def PendOut (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState) (flush : Int32) : Prop :=
  ∃ (after : Heap) (z1 : ZStream) (d1 : DeflateState) (produced : Nat),
    flush_pending (some r) (setD h ds { d with last_flush := flush }) = .ok ((), after) ∧
    r.get after = some z1 ∧ after.dstates ds = some d1 ∧ 1 ≤ produced ∧ StreamAccounting z z1 0 produced ∧
    Seg h after r ds d z z1 d1 ∧ d1.status = d.status ∧
    (z1.avail_out = 0 →
      DInv (setD after ds { d1 with status := d1.status, last_flush := -1 }) r ds z1
        { d1 with status := d1.status, last_flush := -1 } ∧
      HeaderInv { d1 with status := d1.status, last_flush := -1 } ∧
      CallFacts { d1 with status := d1.status, last_flush := -1 } ∧
      StreamBuffers (setD after ds { d1 with status := d1.status, last_flush := -1 }) r ∧
      Seg h (setD after ds { d1 with status := d1.status, last_flush := -1 }) r ds d z z1
        { d1 with status := d1.status, last_flush := -1 }) ∧
    (d1.status = FINISH_STATE → DInv after r ds z1 d1 ∧ HeaderInv d1 ∧ CallFacts d1 ∧ StreamBuffers after r) ∧
    (z1.avail_out ≠ 0 → ¬ (d1.status = FINISH_STATE ∧ z1.avail_in ≠ 0) →
      TailOut h r ds z d flush
        (headerPhase (some r) (some (.tab ds)) flush
          (strategyPhase (some r) (some (.tab ds)) flush (trailerPhase (some r) (some (.tab ds)) flush)) after))

/-- **The entry flush of an accepted call with output pending**, and what follows it. -/
theorem cont_pending (t2 : EntryKeep) {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {flush : Int32}
    (inv : DInv h r ds z d) (ov : Block.OverlayAt d.lit_bufsize.toNat) (header : HeaderInv d) (facts : CallFacts d) (buffers : StreamBuffers h r)
    (active : ActiveHeader h r) (pend : d.pending ≠ 0) (accepted : ¬ DeflateRefuses z d flush)
    (room : z.avail_out ≠ 0) : PendOut h r ds z d flush := by
  unfold DeflateRefuses at accepted
  have valid : 0 ≤ flush.toInt ∧ flush.toInt ≤ 5 := by omega
  have out : z.next_out ≠ .null := fun e => accepted (Or.inr (Or.inr (Or.inl e)))
  have input : z.avail_in ≠ 0 → z.next_in ≠ .null :=
    fun ne e => accepted (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, ne⟩))))
  have lfNot : flush ≠ -2 := by
    intro e; rw [e] at valid; exact absurd valid.1 (by decide)
  have lfRange : -2 ≤ flush.toInt ∧ flush.toInt ≤ 5 := ⟨by omega, valid.2⟩
  obtain ⟨pb, buf, trees⟩ := inv_trees inv
  have pbuf := trees.base.pbuf
  obtain ⟨good1, trees1, buffers1⟩ := last_flush_engine (pb := pb) (buf := buf) flush inv.good trees buffers
  have low : d.bi_valid.toInt < 8 := by have := inv.shape.biValid; omega
  obtain ⟨produced, after, z1, d1, run, good', buffers', acc, count⟩ :=
    flush_cursor_run (d := { d with last_flush := flush }) good1 buffers1 low out
  obtain ⟨w0, p0, q0, b0, blocks⟩ := inv.good.inv.blocks
  have key : b0 = pb := by simpa only [pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst key
  obtain ⟨po, cursor0, _⟩ := blocks.pout
  have nval := pendingLen_value d.pending z.avail_out
  have pendPos : d.pending.toNat ≠ 0 := by
    intro e; apply pend; exact UInt64.toNat_inj.mp (by rw [e]; rfl)
  have roomPos : z.avail_out.toNat ≠ 0 := by
    intro e; apply room; exact UInt32.toNat_inj.mp (by rw [e]; rfl)
  have nonzero : pendingLen d.pending z.avail_out ≠ 0 := by
    intro e; have := congrArg UInt32.toNat e; rw [nval] at this; simp at this; omega
  have stateEq := flush_cursor_state (d := { d with last_flush := flush }) good1 buffers1 pbuf cursor0 low out
    nonzero run good'
  have frame := StageFrame.of_flush_low good1 buffers1 pbuf low out run good'.live.hz acc
  have bytesPb : after.bytes b0 = h.bytes b0 := by
    have e := flush_low_pending_buf good1 buffers1 low pbuf out run
    exact e
  have nle : (pendingLen d.pending z.avail_out).toNat ≤ d.pending.toNat := by rw [nval]; omega
  have count' : produced = min d.pending.toNat z.avail_out.toNat := count
  have one : 1 ≤ produced := by rw [count']; omega
  have stEq : d1.status = d.status := by rw [stateEq]; rfl
  have own : ∀ b, DeflateOwned ds d1 b ↔ DeflateOwned ds d b := by
    intro b; rw [stateEq]; exact Iff.rfl
  have seg0 : Seg h (setD h ds { d with last_flush := flush }) r ds d z z { d with last_flush := flush } :=
    ⟨0, 0, strat_frame_setD inv.good _ rfl, fun _ => Iff.rfl⟩
  have seg1 : Seg h after r ds d z z1 d1 := seg0.trans ⟨0, produced, frame.1, own⟩ inv.good buffers
  have lift := fun (v : Int32) (vr : -2 ≤ v.toInt ∧ v.toInt ≤ 5)
      (vh : d.status = INIT_STATE ∨ d.status = GZIP_STATE → v = -2 ∨ v = -1) =>
    pend_lift inv pbuf cursor0 good1 buffers1 out good' buffers' frame bytesPb stateEq nle v vr vh
  have keepH : ∀ v : Int32, HeaderInv { d1 with status := d1.status, last_flush := v } := fun v =>
    header.keep stEq (by rw [stateEq]; rfl) (by rw [stateEq]; rfl)
  have keepF : ∀ v : Int32, v ≠ -2 → CallFacts { d1 with status := d1.status, last_flush := v } := by
    intro v nv
    have sym : d1.sym_next = d.sym_next := by rw [stateEq]; rfl
    have look : d1.lookahead = d.lookahead := by rw [stateEq]; rfl
    have bits : d1.bi_valid = d.bi_valid := by rw [stateEq]; rfl
    exact { fresh := fun e => absurd e nv, freshStart := fun e => absurd e nv,
            finishSym := fun e => by show d1.sym_next = 0; rw [sym]; exact facts.finishSym (stEq ▸ e),
            finishLook := fun e => by show d1.lookahead = 0; rw [look]; exact facts.finishLook (stEq ▸ e),
            finishBits := fun e => by show d1.bi_valid = 0; rw [bits]; exact facts.finishBits (stEq ▸ e) }
  have lfEq : d1.last_flush = flush := by rw [stateEq]; rfl
  have eqd : ({ d1 with status := d1.status, last_flush := flush } : DeflateState) = d1 := by rw [← lfEq]
  have selfAfter : setD after ds { d1 with status := d1.status, last_flush := flush } = after := by
    rw [eqd]; exact setD_self good'.live.hs
  -- the state after the flush, at `after`, when the status is not a fresh header
  have atAfter : ¬ (d.status = INIT_STATE ∨ d.status = GZIP_STATE) →
      DInv after r ds z1 d1 ∧ HeaderInv d1 ∧ CallFacts d1 := by
    intro nh
    have i := lift flush lfRange (fun e => absurd e nh)
    rw [selfAfter, eqd] at i
    have hi := keepH flush
    have fi := keepF flush lfNot
    rw [eqd] at hi fi
    exact ⟨i, hi, fi⟩
  refine ⟨after, z1, d1, produced, run, good'.live.hz, good'.live.hs, one, acc, seg1, stEq, ?_, ?_, ?_⟩
  · -- full output: Z_OK with last_flush := -1
    intro _
    have i := lift (-1) (by decide) (fun _ => Or.inr rfl)
    obtain ⟨good2, _, buffers2⟩ := good_status_flush good' (trees_at_of_good good' (by rw [stateEq]; exact pbuf)
      (by rw [bytesPb]; exact blocks.ba.choose_spec.1)) buffers' d1.status (-1) (by rw [stEq]; exact inv.good.live.status)
    refine ⟨i, keepH (-1), keepF (-1) (by decide), buffers2, ?_⟩
    exact seg1.trans ⟨0, 0, strat_frame_setD good' _ rfl, fun _ => Iff.rfl⟩ inv.good buffers
  · -- a finished stream
    intro fin
    obtain ⟨i, hi, fi⟩ := atAfter (by rw [← stEq, fin]; intro e; rcases e with e | e <;> exact absurd e (by decide))
    exact ⟨i, hi, fi, buffers'⟩
  · -- continue
    intro notFull notFin
    have pendZero : d1.pending = 0 := by
      have l := acc.2.2.2.1
      have p0 : d1.pending = d.pending - (pendingLen d.pending z.avail_out).toUInt64 := by rw [stateEq]; rfl
      have small : produced < z.avail_out.toNat := by
        have : z1.avail_out.toNat ≠ 0 := fun e => notFull (UInt32.toNat_inj.mp (by rw [e]; rfl))
        omega
      have eqn : (pendingLen d.pending z.avail_out).toNat = d.pending.toNat := by rw [nval]; rw [count'] at small; omega
      rw [p0]
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_sub_of_le]
      · simp [eqn]
      · rw [UInt64.le_iff_toNat_le]; simp; omega
    have cursor1 : d1.pending_out = d1.pending_buf := by
      have : d1.pending_out = if d.pending - (pendingLen d.pending z.avail_out).toUInt64 == 0 then d.pending_buf
          else .ref (.blk b0) (po + (pendingLen d.pending z.avail_out).toNat) := by rw [stateEq]; rfl
      have p0 : d1.pending = d.pending - (pendingLen d.pending z.avail_out).toUInt64 := by rw [stateEq]; rfl
      rw [this, ← p0, pendZero]
      simp only [beq_self_eq_true, ite_true]
      rw [stateEq]; rfl
    have input1 : z1.avail_in ≠ 0 → z1.next_in ≠ .null := by
      intro ne
      have ain : z1.avail_in = z.avail_in := UInt32.toNat_inj.mp (by have := acc.2.2.1; omega)
      have nin : z1.next_in = z.next_in := by rw [acc.2.2.2.2.1]; cases z.next_in <;> rfl
      rw [nin]; exact input (ain ▸ ne)
    have out1 : z1.next_out ≠ .null := by
      rw [acc.2.2.2.2.2.1]; exact Zlib.Deflate.Universal.advance_ne_null _ out
    rcases status_cases inv.good.live.status with writing | busy
    · -- a header state: the header phase from the pre-call invariant
      obtain ⟨keep1, records⟩ := t2 good1 buffers1 pbuf low out run good'.live.hz acc
      have keep : CallerKeep h after z ds b0 :=
        (CallerKeep.of_frame (HeaderFrame.state (r := r) b0 inv.good.live.hs { d with last_flush := flush } rfl)).trans
          keep1 (stream_accounting_zero z)
      have trees' := trees_at_of_good good' (by rw [stateEq]; exact pbuf) (by rw [bytesPb]; exact blocks.ba.choose_spec.1)
      have entry : HeaderEntry after z1 d1 ds b0 blocks.ba.choose := by
        rcases writing with e | e | e | e | e | e
        · exact fresh_header_entry inv.good trees active keep acc records stEq (by rw [stateEq]; rfl) (Or.inl e)
            pendZero notFull
        · exact fresh_header_entry inv.good trees active keep acc records stEq (by rw [stateEq]; rfl) (Or.inr e)
            pendZero notFull
        all_goals
          have size : 0 < blocks.ba.choose.size := by
            have := trees'.base.size; have := trees'.base.lit_lo; omega
        · exact resumed_header_entry inv.good trees active header keep acc records stEq (by rw [stateEq]; rfl)
            (by rw [stateEq]; rfl) (Or.inl e) pendZero size
        · exact resumed_header_entry inv.good trees active header keep acc records stEq (by rw [stateEq]; rfl)
            (by rw [stateEq]; rfl) (Or.inr (Or.inl e)) pendZero size
        · exact resumed_header_entry inv.good trees active header keep acc records stEq (by rw [stateEq]; rfl)
            (by rw [stateEq]; rfl) (Or.inr (Or.inr (Or.inl e))) pendZero size
        · exact resumed_header_entry inv.good trees active header keep acc records stEq (by rw [stateEq]; rfl)
            (by rw [stateEq]; rfl) (Or.inr (Or.inr (Or.inr e))) pendZero size
      obtain ⟨_, _, _, static, win, prv, hd, _⟩ := StageFrame.call_facts frame good1 buffers1 pbuf out
      have fields0 : HeaderFields d d1 := by unfold HeaderFields; rw [stateEq]; rfl
      obtain ⟨a2, z2, d2, p2, inv2, header2, buffers2, acc2, frame2, own2, out2, litEq2, branch⟩ :=
        header_step_mid inv header good' trees' (by rw [stateEq]; exact pbuf) buffers' cursor1 out1
          (by obtain ⟨za, zf⟩ := inv.alloc; exact ⟨acc.2.2.2.2.2.2.2.1.trans za, acc.2.2.2.2.2.2.2.2.1.trans zf⟩)
          fields0 stEq (by rw [stateEq]; rfl) static win prv hd (by rw [stateEq]; exact low)
          (by rw [lfEq]; exact lfRange) (by rw [lfEq]; exact lfNot) (by unfold Writing; rw [stEq]; exact writing)
          entry flush (strategyPhase (some r) (some (.tab ds)) flush (trailerPhase (some r) (some (.tab ds)) flush))
      have seg12 : Seg after a2 r ds d1 z1 z2 d2 := ⟨0, p2, frame2.1, own2⟩
      have seg2 := seg1.trans seg12 inv.good buffers
      have c2 : Changed z z2 := seg_changed seg1 seg12 (Or.inl (changed_produced acc one))
      rcases branch with ⟨run2, _, _, facts2, full2⟩ | ⟨run2, busy2, pend2, _, lf2, facts2⟩
      · exact ⟨Z_OK, a2, z2, d2, run2, inv2, header2, facts2, buffers2, seg2, Or.inl rfl, fun e => absurd e (by decide),
          fun _ _ => Or.inr c2, fun _ _ => c2⟩
      · rw [run2]
        have input2 : z2.avail_in ≠ 0 → z2.next_in ≠ .null := by
          intro ne
          have ain : z2.avail_in = z1.avail_in := UInt32.toNat_inj.mp (by have := acc2.2.2.1; omega)
          have nin : z2.next_in = z1.next_in := by rw [acc2.2.2.2.2.1]; cases z1.next_in <;> rfl
          rw [nin]; exact input1 (ain ▸ ne)
        obtain ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg3, rcs, endF, _, _⟩ :=
          tail_step inv2 (by rw [litEq2, stateEq]; exact ov) header2 facts2 buffers2 out2 input2 pend2 (Or.inl busy2)
            (by rw [lf2, lfEq]; exact lfNot) (fun e => absurd (busy2.symm.trans e) (by decide)) flush
        exact ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg2.trans seg3 inv.good buffers, rcs, endF,
          fun _ _ => Or.inr (seg_changed seg2 seg3 (Or.inl c2)), fun _ _ => seg_changed seg2 seg3 (Or.inl c2)⟩
    · -- BUSY_STATE or FINISH_STATE: no header
      have hs1 := good'.live.hs
      rw [header_skip hs1 (by rw [stEq]; exact busy)]
      obtain ⟨i, hi, fi⟩ := atAfter (by
        intro e; rcases busy with b | b <;> rcases e with e | e <;> rw [b] at e <;> exact absurd e (by decide))
      have finIn : d1.status = FINISH_STATE → z1.avail_in = 0 := fun e =>
        Classical.byContradiction fun ne => notFin ⟨e, ne⟩
      obtain ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg3, rcs, endF, _, _⟩ :=
        tail_step i (by rw [stateEq]; exact ov) hi fi buffers' out1 input1 pendZero (by rw [stEq]; exact busy)
          (by rw [lfEq]; exact lfNot) finIn flush
      exact ⟨rc, a3, z3, d3, run3, inv3, header3, facts3, buffers3, seg1.trans seg3 inv.good buffers, rcs, endF,
        fun _ _ => Or.inr (seg_changed seg1 seg3 (Or.inl (changed_produced acc one))),
        fun _ _ => seg_changed seg1 seg3 (Or.inl (changed_produced acc one))⟩

end Zlib.Deflate.Universal.Call
