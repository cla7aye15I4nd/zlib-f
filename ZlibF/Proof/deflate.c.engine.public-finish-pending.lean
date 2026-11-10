import ZlibF.Proof.«deflate.c.engine.public-finish»

/-! # Completing an already-queued zlib trailer without writing it twice -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (queued finish).
The actual public entry drains the old pending suffix at its advanced
cursor. With caller room left, it returns STREAM_END through the negative
wrapper branch. It emits no second trailer and retains all pending bits.
The exhausted-capacity case is covered by public_pending_exhausted_allowed. -/
theorem public_finished_pending_drained {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {before : List Bool}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (status : d.status = FINISH_STATE)
    (empty : z.avail_in = 0) (look : d.lookahead = 0) (wrap : d.wrap = -1)
    (pendingPositive : 0 < d.pending.toNat) (room : d.pending.toNat < z.avail_out.toNat)
    (low : d.bi_valid.toInt < 8) (pending : PendingBits h d before) :
    ∃ pb after z' result written remaining,
      d.pending_buf = .ref (.blk pb) 0 ∧
      deflate (some r) Z_FINISH h = .ok (Z_STREAM_END, after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 d.pending.toNat ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      0 < z'.avail_out.toNat ∧ z'.avail_in = 0 ∧ result.last_flush = Z_FINISH ∧
      result.pending.toNat = 0 ∧ result.pending_out = result.pending_buf ∧ result.bi_valid.toInt < 8 ∧
      result = { d with pending := result.pending, pending_out := result.pending_out, last_flush := Z_FINISH } ∧
      Bytes after z.next_out d.pending.toNat written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before := by
  have good0 := last_flush_good good Z_FINISH
  have buffers0 := last_flush_buffers good buffers Z_FINISH
  have pending0 := last_flush_pending_bits good pending Z_FINISH
  obtain ⟨pb, produced, after, z', result, written, remaining, base, run, goodA, buffersA, account,
    sizesA, storageA, count, pendingCount, lowA, fields, reset, bytes, pendingA, bits⟩ :=
    flush_pending_resume_raw_bits good0 buffers0 pointer low pending0
  have amount : produced = d.pending.toNat := by
    rw [count]
    change min d.pending.toNat z.avail_out.toNat = d.pending.toNat
    exact Nat.min_eq_left (by omega)
  rw [amount] at account pendingCount reset bytes
  change result.pending.toNat + d.pending.toNat = d.pending.toNat at pendingCount
  have noPending : result.pending.toNat = 0 := by omega
  have cursor : result.pending_out = result.pending_buf := reset pendingPositive noPending
  have left : 0 < z'.avail_out.toNat := by have output := account.2.2.2.1; omega
  have noInput : z'.avail_in = 0 := UInt32.toNat_inj.mp (by
    have input := account.2.2.1
    rw [empty] at input
    change z'.avail_in.toNat + 0 = 0 at input
    change z'.avail_in.toNat = 0
    omega)
  have statusA : result.status = FINISH_STATE := by rw [fields]; exact status
  have lookA : result.lookahead = 0 := by rw [fields]; exact look
  have wrapA : result.wrap = -1 := by rw [fields]; exact wrap
  have tail := public_finished_headers goodA statusA noInput lookA wrapA
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  have baseD : d.pending_buf = .ref (.blk pb) 0 := base
  have key : b = pb := by simpa only [baseD, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst b
  obtain ⟨buf, get, _size⟩ := blocks.ba
  have storage := (last_flush_storage (ob := ob) good get Z_FINISH).trans storageA
  have sizes := (last_flush_sizes good.live.hs Z_FINISH).trans sizesA
  have fieldsA : result = { d with
      pending := result.pending, pending_out := result.pending_out, last_flush := Z_FINISH } := by rw [fields]
  have publicRun : deflate (some r) Z_FINISH h = .ok (Z_STREAM_END, after) := by
    have checked := stateCheck_live good.live
    have outNonzero : z.avail_out ≠ 0 := by intro zero; rw [zero] at room; contradiction
    have pendingNonzero : d.pending ≠ 0 := by intro zero; rw [zero] at pendingPositive; contradiction
    have outAfter : (z'.avail_out == 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro zero
      rw [zero] at left
      contradiction
    simp only [status] at run
    rw [public_deflate_source]
    simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
      show (Z_FINISH > Z_BLOCK) = False from by decide,
      show (Z_FINISH < 0) = False from by decide, decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
      zrd_eq, good.live.hz, good.live.zst, castDeflateState, ldZStream_ok good.live.hz,
      ldDeflateState_tab good.live.hs, empty, show ((0 : UInt32) != 0) = false from rfl,
      BEq.rfl, Bool.not_true, Bool.and_false, Bool.false_and, Bool.or_false,
      show (z.next_out == .null) = false from by rw [pointer]; rfl,
      status, show (Z_FINISH != Z_FINISH) = false from rfl,
      show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr outNonzero,
      wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pendingNonzero,
      ite_true, run, goodA.live.hz, outAfter, rdD_eq, goodA.live.hs, statusA, noInput, tail]
  exact ⟨pb, after, z', result, written, remaining, baseD, publicRun, goodA, buffersA,
    account, sizes, storage, left, noInput, by rw [fields], noPending, cursor, lowA,
    fieldsA, bytes, pendingA, bits⟩

end Zlib.Deflate.Engine.Proofs
