import ZlibF.Proof.«deflate.c.engine.full-reset-boundary»
import ZlibF.Proof.«trees.c.empty-stored-marker»
import ZlibF.Proof.«deflate.c.engine.empty-bits-boundary»
import ZlibF.Proof.«deflate.c.engine.pending-buffered»

/-! # Actual FULL marker and reset publish the exact stored bit sequence -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt outBits storedHeaderBits)
set_option autoImplicit false

/-- The actual FULL marker, hash reset and publication retain the input
endpoint while publishing exactly the empty stored-block bits. The reset
premises are established by a completed actual nonfinal strategy call. -/
theorem empty_full_marker_publish {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (look : d.lookahead = 0) (available : d.match_available = 0) :
    ∃ produced after z' result written remaining,
      (do
        Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0
        let _ ← (do
          CLEAR_HASH (some (.tab ds))
          if (← rd (some (.tab ds)) (·.lookahead)) == 0 then
            wr (some (.tab ds)) (fun d => { d with strstart := 0, block_start := 0, insert := 0 }))
        flush_pending (some r)) h = .ok ((), after) ∧
      BufferedBoundary after r ds z' result input base base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ConfigFrame d result ∧
      result.status = d.status ∧ result.last_flush = d.last_flush ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = outBits buf d ++ storedHeaderBits d 0 false := by
  have room : d.pending.toNat + 6 ≤ buf.size := by
    have extent := trees.base.size
    have lower := trees.base.lit_lo
    rw [publish.1]
    change 0 + 6 ≤ _
    omega
  obtain ⟨next, middle, markerRun, treesM, outputM, sizeM, alignedM, _pendingM, fieldsM⟩ :=
    Zlib.Trees.Proofs.Out.stored_zero_null_emit trees (by have low := publish.2.2; omega) room
  let markerHeap := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds middle
  have goodM := output_bits_good boundary.good publish.2.1 trees.base.bytes sizeM fieldsM treesM
  have buffersM := output_bits_buffers boundary.good buffers publish.2.1 trees.base.bytes sizeM fieldsM treesM
  obtain ⟨w, p, q, pb0, blocks⟩ := boundary.good.inv.blocks
  obtain ⟨qa, getH, sizeH⟩ := blocks.qa
  have pbEq : pb0 = pb := by
    simpa only [trees.base.pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.pbuf.symm
  subst pb0
  have privateWindow : ∀ winBlock, d.window = .ref (.blk winBlock) 0 → markerHeap.bytes winBlock = h.bytes winBlock := by
    intro winBlock win
    have wid : w = winBlock := by
      simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    subst winBlock
    simp only [markerHeap, setD_bytes, Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ blocks.wb]
  have diffM := fieldsM
  obtain ⟨_, _, _, _, fields⟩ := fieldsM
  have cursorM : middle.pending_out = middle.pending_buf := by rw [fields]; exact publish.2.1
  have stateM := empty_buffered_bits_transfer boundary goodM privateWindow rfl diffM (by omega) cursorM
  have headM : middle.head = .ref (.blk q) 0 := by rw [fields]; exact blocks.head
  have getM : markerHeap.words q = some qa := getH
  have lookM : middle.lookahead = 0 := by rw [fields]; exact look
  have availableM : middle.match_available = 0 := by rw [fields]; exact available
  let resetD : DeflateState := { middle with slid := 0, strstart := 0, block_start := 0, insert := 0 }
  let resetHeap := setD (setW markerHeap q (clearHead qa middle.hash_size.toNat)) ds resetD
  obtain ⟨resetRun, stateR, _endpoint⟩ := full_clear_reset_boundary stateM headM getM lookM availableM
  obtain ⟨buffersR, _sizesR, configR, _shapeR, _frameR, _allocR, _nextR, pendingR⟩ :=
    full_clear_reset_effects stateM buffersM headM getM lookM availableM
  have bitsM := pending_bits_base treesM cursorM
  have bitsR := pendingR _ bitsM
  obtain ⟨_pb, produced, after, z', result, written, remaining, _pbuf, publishRun,
      stateA, buffersA, account, _sizes, _storage, _amount, _left, controls, _ready, data, pending, bits⟩ :=
    flush_pending_buffered_boundary stateR buffersR pointer bitsR
  have configA : ConfigFrame resetD result := by rw [controls]; rfl
  have statusA : result.status = d.status := by rw [controls]; change middle.status = d.status; rw [fields]
  have lastA : result.last_flush = d.last_flush := by rw [controls]; change middle.last_flush = d.last_flush; rw [fields]
  refine ⟨produced, after, z', result, written, remaining, ?_, stateA, buffersA, account,
    ((ConfigFrame.bits diffM).trans configR).trans configA, statusA, lastA, data, pending, bits.trans outputM⟩
  have markerSource : Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0 h = .ok ((), markerHeap) := markerRun
  rw [bind_app, markerSource]
  simp only []
  rw [bind_app, resetRun]
  simp only []
  exact publishRun

end Zlib.Deflate.Engine.Proofs
