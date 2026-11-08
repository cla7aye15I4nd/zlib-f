import ZlibF.Proof.«trees.c.flush-source»
import ZlibF.Proof.«deflate.c.engine.block-reset»
import ZlibF.Math.DeflateFixedBlock

/-! # The actual fixed block header establishes payload entry bits -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff fixedTag)
set_option autoImplicit false

/-- Actual fixed-tag arithmetic is checked for both flags produced by
compressor call sites. The value is 2 or 3, written in three bits. -/
theorem fixed_header_arithmetic (last : Bool) :
    Zlib.Trees.iadd (C.STATIC_TREES <<< 1) (if last then 1 else 0) =
      pure (if last then 3 else 2) := by
  cases last <;> rfl

/-- The actual fixed block tag fits the entry bit buffer without a byte
write. It preserves packed symbol data and establishes at most ten bits
for the complete fixed payload. The full source equality identifies this
header at the actual _tr_flush_block fixed branch. -/
theorem fixed_header_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (last : Bool) :
    ∃ result,
      Zlib.Trees.Proofs.fixedBlockHeader (some (.tab ds)) (if last then 1 else 0) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧
      BitsDiff d result ∧ result.pending = 0 ∧ result.bi_valid.toInt ≤ 10 ∧
      result.pending_out = result.pending_buf ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d ++ fixedTag last := by
  obtain ⟨result, run, treesA, output, pendingA, word, valid, fields⟩ :=
    Zlib.Trees.Proofs.Out.send_bits_spec_B trees (if last then 3 else 2) 3 (by decide) (by decide)
      (by cases last <;> decide +kernel) (by change d.bi_valid.toInt + 3 ≤ 16; omega)
  have diff : BitsDiff d result := by rw [fields]; exact ⟨d.pending, word, valid, d.bi_used, rfl⟩
  have treesB : TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb buf) ds result) ds result pb buf := by
    rw [Zlib.Trees.Proofs.Out.setB_self trees.base.bytes]
    exact treesA
  have goodA := output_bits_good good cursor trees.base.bytes rfl diff treesB
  have buffersA := output_bits_buffers good buffers cursor trees.base.bytes rfl diff treesB
  rw [Zlib.Trees.Proofs.Out.setB_self trees.base.bytes] at goodA buffersA
  have sizes := block_record_sizes good.live.hs (show result.depth = d.depth by rw [fields])
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := buf)
    good.live.hs trees.base.bytes
  rw [Zlib.Trees.Proofs.Out.setB_self trees.base.bytes] at storage
  have length := congrArg List.length output
  simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append,
    Zlib.Trees.Proofs.Out.natBits_length, pendingA] at length
  have lower := treesA.run.bi_lo
  have cursorA : result.pending_out = result.pending_buf := by rw [fields]; exact cursor
  have stream : Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d ++ fixedTag last := by
    have tag : Zlib.Trees.Proofs.Out.natBits (Zlib.Trees.Proofs.Out.v16 (if last then 3 else 2))
        (3 : Int32).toInt.toNat = fixedTag last := by cases last <;> decide +kernel
    exact output.trans (congrArg (Zlib.Trees.Proofs.Out.outBits buf d ++ ·) tag)
  refine ⟨result, ?_, goodA, treesA, buffersA, sizes, storage, diff,
    pendingA.trans pending, by
      change 8 * d.pending.toNat + result.bi_valid.toInt.toNat = 8 * d.pending.toNat + d.bi_valid.toInt.toNat + 3 at length
      omega, cursorA, stream⟩
  unfold Zlib.Trees.Proofs.fixedBlockHeader
  simp only [fixed_header_arithmetic, bind_app, pure_app, run]
  rfl

end Zlib.Deflate.Engine.Proofs
