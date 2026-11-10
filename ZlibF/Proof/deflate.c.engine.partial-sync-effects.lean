import ZlibF.Proof.«deflate.c.engine.bit-output-effects»
import ZlibF.Proof.«deflate.c.engine.partial-sync-publication»

/-! # Actual PARTIAL and SYNC publication have exact counters and footprint -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff outBits natBits storedHeaderBits)
set_option autoImplicit false

/-- Actual PARTIAL/SYNC marker generation and publication have exact
wrapping totals, caller output interval and complete object footprint.
Marker room follows from the real initialized pending buffer. -/
theorem partial_sync_publication_effects {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH) :
    ∃ produced after z' result,
      (do
        let _ ← (if flush == Z_PARTIAL_FLUSH then Zlib.Trees.«_tr_align» (some (.tab ds))
          else Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0)
        flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧ Shape h after ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  have room : 8 ≤ buf.size := by
    have extent := trees.base.size
    have lower := trees.base.lit_lo
    omega
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
  obtain ⟨next, middle, markerRun, treesM, _bitsM, sizeM, pendingM, fieldsM⟩ := marker
  have bitRoom : 8 * middle.pending.toNat + middle.bi_valid.toInt.toNat ≤ 8 * next.size := by
    have upper := treesM.run.bi_hi
    have lower := treesM.run.bi_lo
    rw [sizeM]; omega
  obtain ⟨produced, after, z', result, run, goodA, buffersA, account, inputA, outputA,
      interval, shape, frame, live, alloc, nextKey⟩ :=
    bit_output_pending_effects good trees buffers pointer publish.2.1 sizeM fieldsM treesM bitRoom
  refine ⟨produced, after, z', result, ?_, goodA, buffersA, account, inputA, outputA,
    interval, shape, frame, live, alloc, nextKey⟩
  rw [bind_app, markerRun]
  exact run

end Zlib.Deflate.Engine.Proofs
