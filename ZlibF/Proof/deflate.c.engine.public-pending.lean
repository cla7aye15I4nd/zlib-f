import ZlibF.Proof.«deflate.c.engine.pending-resume»

/-! # Actual public deflate calls that exhaust output while draining pending

This is the public entry path before new compression starts. It consumes
pending bytes at their actual cursor and returns without touching input.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem last_flush_good {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (flush : Int32) :
    DGood (setD h ds { d with last_flush := flush }) r ds z { d with last_flush := flush } := by
  have inv : DStInv h ds { d with last_flush := flush } :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact good.setD' rfl good.live.status inv (by trkeep)

theorem last_flush_sizes {h : Heap} {ds : Nat} {d : DeflateState}
    (state : h.dstates ds = some d) (flush : Int32) :
    ByteSizes h (setD h ds { d with last_flush := flush }) := by
  refine ⟨?_, fun _ => rfl⟩
  intro ref a get
  exact ⟨a, (byte_view_setD_depth (result := { d with last_flush := flush }) state rfl ref).trans get, rfl⟩

theorem last_flush_buffers {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (flush : Int32) :
    StreamBuffers (setD h ds { d with last_flush := flush }) r := by
  have goodA := last_flush_good good flush
  have owned : ∀ b, StreamOwned (setD h ds { d with last_flush := flush }) r b ↔ StreamOwned h r b := by
    intro b
    rw [stream_owned_deflate goodA, stream_owned_deflate good]
    rfl
  exact stream_buffers_sizes good.live.hz goodA.live.hz buffers (last_flush_sizes good.live.hs flush)
    owned (stream_accounting_zero z)

theorem last_flush_pending_bits {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {bits : List Bool}
    (good : DGood h r ds z d) (pending : PendingBits h d bits) (flush : Int32) :
    PendingBits (setD h ds { d with last_flush := flush }) { d with last_flush := flush } bits := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨po, cursor, bound⟩ := blocks.pout
  rw [pending_bits_cursor_value cursor get pending]
  exact pending_bits_slice (d := { d with last_flush := flush }) cursor get
    (by rw [size, ← blocks.psize]; exact bound)

theorem last_flush_storage {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (get : h.bytes pb = some buf) (flush : Int32) :
    OutputStorage h (setD h ds { d with last_flush := flush }) r ds pb ob := by
  have storage := output_bits_storage (r := r) (ob := ob) (result := { d with last_flush := flush })
    (next := buf) good.live.hs get
  rw [Zlib.Trees.Proofs.Out.setB_self get] at storage
  exact storage

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (pending output).
Every accepted flush flag is included. When existing pending bytes fill
all positive raw output capacity, the actual public call returns Z_OK,
records last_flush = -1, consumes no input and preserves the complete
pending sequence, caller ranges, ownership and allocation ledger. The
FINISH_STATE entry is included exactly for Z_FINISH, as the source requires.
Fewer than eight residual bits is the resumed-publication phase premise.
This internal path does not replace the public Goal.deflate. -/
theorem public_pending_exhausted_allowed {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {before : List Bool} (flush : Int32)
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (input : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (status : d.status = FINISH_STATE → flush = Z_FINISH) (positive : 0 < z.avail_out.toNat)
    (enough : z.avail_out.toNat ≤ d.pending.toNat) (low : d.bi_valid.toInt < 8)
    (pending : PendingBits h d before) :
    ∃ pb after z' result written remaining,
      d.pending_buf = .ref (.blk pb) 0 ∧
      deflate (some r) flush h = .ok (Z_OK, after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 z.avail_out.toNat ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      z'.avail_out = 0 ∧ result.last_flush = -1 ∧
      result.pending.toNat + z.avail_out.toNat = d.pending.toNat ∧ result.bi_valid.toInt < 8 ∧
      result = { d with pending := result.pending, pending_out := result.pending_out, last_flush := -1 } ∧
      Bytes after z.next_out z.avail_out.toNat written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before := by
  let d0 := { d with last_flush := flush }
  let h0 := setD h ds d0
  have good0 := last_flush_good good flush
  have buffers0 := last_flush_buffers good buffers flush
  have pending0 := last_flush_pending_bits good pending flush
  obtain ⟨pb, produced, middle, z', result, written, remaining, base, run, goodM, buffersM, account,
    sizesM, storageM, count, pendingCount, lowM, fields, _reset, bytes, pendingM, bits⟩ :=
    flush_pending_resume_raw_bits good0 buffers0 pointer low pending0
  have amount : produced = z.avail_out.toNat := by rw [count]; exact Nat.min_eq_right enough
  rw [amount] at account pendingCount bytes
  have outputZero : z'.avail_out = 0 := UInt32.toNat_inj.mp (by
    have balance := account.2.2.2.1
    change z'.avail_out.toNat = 0
    omega)
  let final := setD middle ds { result with last_flush := -1 }
  have goodF := last_flush_good goodM (-1)
  have buffersF := last_flush_buffers goodM buffersM (-1)
  have pendingF := last_flush_pending_bits goodM pendingM (-1)
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  have baseD : d.pending_buf = .ref (.blk pb) 0 := base
  have key : b = pb := by simpa only [baseD, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst b
  obtain ⟨buf, get, _size⟩ := blocks.ba
  have baseM : result.pending_buf = .ref (.blk pb) 0 := by rw [fields]; exact base
  obtain ⟨wM, pM, qM, bM, blocksM⟩ := goodM.inv.blocks
  have keyM : bM = pb := by simpa only [baseM, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocksM.pbuf.symm
  subst bM
  obtain ⟨bufM, getM, _sizeM⟩ := blocksM.ba
  have storage := ((last_flush_storage (ob := ob) good get flush).trans storageM).trans
    (last_flush_storage (ob := ob) goodM getM (-1))
  have sizes := ((last_flush_sizes good.live.hs flush).trans sizesM).trans (last_flush_sizes goodM.live.hs (-1))
  have fieldsF : { result with last_flush := -1 } =
      { d with pending := result.pending, pending_out := result.pending_out, last_flush := -1 } := by rw [fields]
  have dataF : Bytes final z.next_out z.avail_out.toNat written := by
    have kept := byte_view_setD_depth (d := result) (result := { result with last_flush := -1 }) goodM.live.hs rfl
    rcases bytes with null | ⟨ref, off, array, ptr, read, bound, value⟩
    · exact Or.inl null
    · exact Or.inr ⟨ref, off, array, ptr, (kept ref).trans read, bound, value⟩
  have publicRun : deflate (some r) flush h = .ok (Z_OK, final) := by
    have checked := stateCheck_live good.live
    have inputs : (z.avail_in != 0 && z.next_in == .null) = false := by
      by_cases empty : z.avail_in = 0
      · simp [empty]
      · simp [input empty]
    have outNonzero : z.avail_out ≠ 0 := by intro zero; rw [zero] at positive; contradiction
    have pendingNonzero : d.pending ≠ 0 := by intro zero; rw [zero] at enough; change z.avail_out.toNat ≤ 0 at enough; omega
    have flagUpper : ¬ flush > Z_BLOCK := by
      change ¬ Z_BLOCK < flush
      rw [Int32.lt_iff_toInt_lt]
      omega
    have flagLower : ¬ flush < 0 := by
      rw [Int32.lt_iff_toInt_lt]
      change ¬ flush.toInt < 0
      omega
    have finishAllowed : (d.status == FINISH_STATE && flush != Z_FINISH) = false := by
      by_cases finished : d.status = FINISH_STATE
      · simp [finished, status finished]
      · simp [finished]
    rw [public_deflate_source]
    simp only [bind_app, pure_app, checked, show ((0 : Int32) != 0) = false from rfl,
      flagUpper, flagLower,
      decide_false, Bool.false_or, Bool.false_eq_true, ite_false,
      zrd_eq, good.live.hz, good.live.zst, castDeflateState, ldZStream_ok good.live.hz,
      ldDeflateState_tab good.live.hs, inputs,
      show (z.next_out == .null) = false from by rw [pointer]; rfl,
      finishAllowed, show (z.avail_out == 0) = false from beq_eq_false_iff_ne.mpr outNonzero,
      wrD_eq, good.live.hs, show (d.pending != 0) = true from bne_iff_ne.mpr pendingNonzero,
      ite_true, run, goodM.live.hz, outputZero, BEq.rfl, goodM.live.hs]
    rfl
  exact ⟨pb, final, z', { result with last_flush := -1 }, written, remaining,
    base, publicRun, goodF, buffersF, account, sizes, storage, outputZero, rfl,
    pendingCount, lowM, fieldsF, dataF, pendingF, bits⟩

/-- The non-finished public pending path retains its exact statement. -/
theorem public_pending_exhausted {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {before : List Bool} (flush : Int32)
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (input : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flagLo : 0 ≤ flush.toInt) (flagHi : flush.toInt ≤ Z_BLOCK.toInt)
    (status : d.status ≠ FINISH_STATE) (positive : 0 < z.avail_out.toNat)
    (enough : z.avail_out.toNat ≤ d.pending.toNat) (low : d.bi_valid.toInt < 8)
    (pending : PendingBits h d before) :
    ∃ pb after z' result written remaining,
      d.pending_buf = .ref (.blk pb) 0 ∧
      deflate (some r) flush h = .ok (Z_OK, after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 z.avail_out.toNat ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      z'.avail_out = 0 ∧ result.last_flush = -1 ∧
      result.pending.toNat + z.avail_out.toNat = d.pending.toNat ∧ result.bi_valid.toInt < 8 ∧
      result = { d with pending := result.pending, pending_out := result.pending_out, last_flush := -1 } ∧
      Bytes after z.next_out z.avail_out.toNat written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before := by
  exact public_pending_exhausted_allowed flush good buffers pointer input flagLo flagHi
    (fun finished => False.elim (status finished)) positive enough low pending

end Zlib.Deflate.Engine.Proofs
