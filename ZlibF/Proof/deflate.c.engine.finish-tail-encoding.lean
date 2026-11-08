import ZlibF.Proof.«deflate.c.engine.flush-content-encoding»
import ZlibF.Proof.«deflate.c.engine.final-control»

/-! # The real final-block tail retains independent meaning and exact bits -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual FINISH tail executes its computed final encoding, state
update and publication, and returns the real output-full control. Exact
written/pending bits retain the final block and padding even for zero or
short caller output. This is the settled zero-credit block cutpoint. -/
theorem finish_tail_final_content_encoding {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (wrap : d.wrap = 1) :
    ∃ produced after z' result before written remaining kind body padding,
      finish_tail (some (.tab ds)) Z_FINISH h =
        .ok ((if z'.avail_out == 0 then finish_started else finish_done), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt.toNat = 0 ∧ PendingBits h d before ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      kind < 3 ∧ padding.length < 8 ∧ (kind = 0 → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 1 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body ++ padding) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  obtain ⟨produced, after, z', result, before, written, remaining, kind, body, padding,
      run, stateA, buffersA, accountA, clearA, frameA, pendingBefore, bytesA, pendingA,
      _drained, finalA, kindA, padBound, _padNone, storedPad, wire, grammar⟩ :=
    flush_block_only_content_encoding boundary buffers positive pointer cursor memory pending bits clear available true
  have run1 : FLUSH_BLOCK_ONLY (some (.tab ds)) 1 h = .ok ((), after) := run
  have wrapA : result.wrap = 1 := by rw [frameA]; exact wrap
  have macroRun : FLUSH_BLOCK (some (.tab ds)) 1 h =
      .ok ((if z'.avail_out == 0 then some finish_started else none), after) := by
    unfold FLUSH_BLOCK
    simp only [bind_app, run1, ldDeflateState_tab stateA.good.live.hs,
      stateA.good.live.back, zrd_eq, stateA.good.live.hz]
    by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app, wrapA]
  refine ⟨produced, after, z', result, before, written, remaining, kind, body, padding,
    ?_, stateA, buffersA, accountA, clearA, frameA, finalA rfl, pendingBefore,
    bytesA, pendingA, kindA, padBound, storedPad, wire, grammar⟩
  unfold finish_tail
  simp only [beq_self_eq_true, ite_true, bind_app, macroRun]
  by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]

end Zlib.Deflate.Engine.Proofs
