import ZlibF.Proof.«deflate.c.engine.empty-output-prepared»
import ZlibF.Proof.«trees.c.empty-stored-marker»
import ZlibF.Proof.«trees.c.align»
import ZlibF.Proof.«deflate.c.engine.pending-buffered»

/-! # Actual partial and sync markers publish their exact bit streams -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff outBits natBits storedHeaderBits)
set_option autoImplicit false

/-- Actual PARTIAL/SYNC marker generation followed by pending publication
retains the initialized empty-block boundary and losslessly splits the
concrete emitted bits into caller bytes and the remaining pending bits.
The room bound is an internal pending-buffer bound, not caller capacity;
publication includes zero, partial and complete caller output. -/
theorem empty_partial_sync_publish {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (room : 8 ≤ buf.size) (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH) :
    ∃ produced after z' result written remaining,
      (do
        let _ ← (if flush == Z_PARTIAL_FLUSH then Zlib.Trees.«_tr_align» (some (.tab ds))
          else Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0)
        flush_pending (some r)) h = .ok ((), after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      ConfigFrame d result ∧ result.status = d.status ∧ result.last_flush = d.last_flush ∧
      (0 < z'.avail_out.toNat → PublishReady result) ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = outBits buf d ++
        (if flush == Z_PARTIAL_FLUSH then natBits 2 3 ++ (natBits 0 7 ++ [])
          else storedHeaderBits d 0 false) := by
  have marker : ∃ next result,
      (if flush == Z_PARTIAL_FLUSH then Zlib.Trees.«_tr_align» (some (.tab ds))
        else Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0) h =
          .ok ((), setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) ∧
      TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) ds result pb next ∧
      outBits next result = outBits buf d ++
        (if flush == Z_PARTIAL_FLUSH then natBits 2 3 ++ (natBits 0 7 ++ []) else storedHeaderBits d 0 false) ∧
      next.size = buf.size ∧ result.pending.toNat ≤ 6 ∧ BitsDiff d result := by
    rcases flag with partialFlag | sync
    · subst flush
      obtain ⟨next, result, run, treesA, output, size, _frame, _lower, upper, fields⟩ :=
        Zlib.Trees.Proofs.Out.tr_align_emit trees (by
          have zero := publish.1; have low := publish.2.2
          have lower := trees.run.bi_lo
          rw [zero]; change 8 * 0 + _ + 10 ≤ _; omega)
      exact ⟨next, result, by simpa only [BEq.rfl, ite_true, Zlib.Trees.Proofs.Out.setD, setD] using run, treesA,
        by simpa only [BEq.rfl, ite_true] using output, size,
        by rw [publish.1] at upper; exact upper, fields⟩
    · subst flush
      obtain ⟨next, result, run, treesA, output, size, _aligned, upper, fields⟩ :=
        Zlib.Trees.Proofs.Out.stored_zero_null_emit trees (by have low := publish.2.2; omega)
          (by rw [publish.1]; change 0 + 6 ≤ _; omega)
      exact ⟨next, result, by simpa only [show (Z_SYNC_FLUSH == Z_PARTIAL_FLUSH) = false from rfl, Bool.false_eq_true, ite_false, Zlib.Trees.Proofs.Out.setD, setD] using run,
        treesA, by simpa only [show (Z_SYNC_FLUSH == Z_PARTIAL_FLUSH) = false from rfl, Bool.false_eq_true, ite_false] using output,
        size, by rw [publish.1] at upper; exact upper, fields⟩
  obtain ⟨next, middle, markerRun, treesM, outputM, sizeM, pendingM, fieldsM⟩ := marker
  have bitRoom : 8 * middle.pending.toNat + middle.bi_valid.toInt.toNat ≤ 8 * next.size := by
    have upper := treesM.run.bi_hi
    have lower := treesM.run.bi_lo
    rw [sizeM]
    omega
  obtain ⟨preparedHeap, prepared, sourceP, stateP, buffersP, sizesP, storageP, bitsP, fieldsP⟩ :=
    prepare_empty_bit_output (ob := ob) boundary buffers trees publish.2.1 sizeM fieldsM treesM bitRoom
  obtain ⟨pb', produced, after, z', result, written, remaining, pbufP, run, stateA, buffersA, account,
      sizes, storage, _amount, _left, controls, ready, bytes, pending, bits⟩ :=
    flush_pending_buffered_boundary stateP buffersP pointer bitsP
  have pbEq : pb' = pb := by
    obtain ⟨_, _, _, _, equal⟩ := fieldsP
    rw [equal] at pbufP
    simpa only [trees.base.pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using pbufP.symm
  subst pb'
  have frameA : ConfigFrame prepared result := by rw [controls]; rfl
  have controlsA : result.status = d.status ∧ result.last_flush = d.last_flush := by
    obtain ⟨_, _, _, _, equal⟩ := fieldsP
    rw [controls, equal]
    exact ⟨rfl, rfl⟩
  refine ⟨produced, after, z', result, written, remaining, ?_, stateA, buffersA, account,
    sizesP.trans sizes, storageP.trans storage, (ConfigFrame.bits fieldsP).trans frameA,
    controlsA.1, controlsA.2, ready, bytes, pending, ?_⟩
  · simp only [bind_app, markerRun]
    exact sourceP.trans run
  · exact bits.trans outputM

end Zlib.Deflate.Engine.Proofs
