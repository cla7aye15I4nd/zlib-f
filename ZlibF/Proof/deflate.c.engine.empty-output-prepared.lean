import ZlibF.Proof.«deflate.c.engine.empty-bits-boundary»
import ZlibF.Proof.«deflate.c.engine.pending-bits»

/-! # Actual bit preparation preserves the completed-block boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff outBits)
set_option autoImplicit false

/-- The actual complete-byte preparation after an empty-block bit writer
retains the input history and produces the pending-bit sequence of that
writer. This is a heap transformation lemma; callers prove the real
marker execution and its room bound separately. -/
theorem prepare_empty_bit_output {h : Heap} {r : ZStreamRef} {ds pb ob origin base : Nat}
    {z : ZStream} {d result : DeflateState} {buf next : Array UInt8}
    {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (cursor : d.pending_out = d.pending_buf) (size : next.size = buf.size)
    (fields : BitsDiff d result)
    (treesA : TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) ds result pb next)
    (room : 8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size) :
    ∃ after prepared,
      flush_pending (some r) (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) =
        flush_pending (some r) after ∧
      BufferedBoundary after r ds z prepared input origin base [] config ∧
      StreamBuffers after r ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      PendingBits after prepared (outBits next result) ∧ BitsDiff d prepared := by
  have goodA := output_bits_good boundary.good cursor trees.base.bytes size fields treesA
  have buffersA := output_bits_buffers boundary.good buffers cursor trees.base.bytes size fields treesA
  have sizesA := output_bits_sizes boundary.good trees.base.bytes size fields
  have storageA := output_bits_storage (r := r) (ob := ob) (result := result) (next := next)
    boundary.good.live.hs trees.base.bytes
  have cursorA : result.pending_out = result.pending_buf := by
    obtain ⟨_, _, _, _, equal⟩ := fields
    rw [equal]; exact cursor
  obtain ⟨nextP, prepared, _runP, goodP, treesP, outputP, lowP, sizeP, fieldsP,
      _pendingP, _validP, sourceP⟩ := flush_pending_prepare goodA treesA cursorA room
  have buffersP := output_bits_buffers goodA buffersA cursorA treesA.base.bytes sizeP fieldsP treesP
  have sizesP := output_bits_sizes goodA treesA.base.bytes sizeP fieldsP
  have storageP := output_bits_storage (r := r) (ob := ob) (result := prepared) (next := nextP)
    goodA.live.hs treesA.base.bytes
  have allFields := fields.trans fieldsP
  have cursorP : prepared.pending_out = prepared.pending_buf := by
    obtain ⟨_, _, _, _, equal⟩ := allFields
    rw [equal]; exact cursor
  have privateWindow : ∀ w, d.window = .ref (.blk w) 0 →
      (setD (Zlib.Trees.Proofs.Out.setB
        (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) pb nextP) ds prepared).bytes w = h.bytes w := by
    intro w win
    obtain ⟨wid, p, q, bid, blocks⟩ := boundary.good.inv.blocks
    have widEq : wid = w := by
      simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    have bidEq : bid = pb := by
      simpa only [trees.base.pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
    subst wid bid
    simp only [setD_bytes, Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ blocks.wb]
  have boundaryP := empty_buffered_bits_transfer boundary goodP privateWindow rfl allFields lowP cursorP
  have bitsP := pending_bits_base treesP cursorP
  rw [outputP] at bitsP
  exact ⟨_, prepared, sourceP, boundaryP, buffersP, sizesA.trans sizesP,
    storageA.trans storageP, bitsP, allFields⟩

end Zlib.Deflate.Engine.Proofs
