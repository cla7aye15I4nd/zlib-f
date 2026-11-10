import ZlibF.Proof.«deflate.c.engine.full-marker-publication»
import ZlibF.Proof.«deflate.c.engine.bit-output-effects»

/-! # Actual FULL hash reset and publication have exact effects -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- Actual FULL marker/reset publication retains exact counters, caller
output interval and the complete heap footprint. Hash clearing is included
in the private frame, rather than hidden in a bit-writer footprint. -/
theorem full_publication_effects {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (look : d.lookahead = 0) (available : d.match_available = 0) :
    ∃ produced after z' result,
      (do
        Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0
        let _ ← (do
          CLEAR_HASH (some (.tab ds))
          if (← rd (some (.tab ds)) (·.lookahead)) == 0 then
            wr (some (.tab ds)) (fun d => { d with strstart := 0, block_start := 0, insert := 0 }))
        flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧ Shape h after ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
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
  obtain ⟨buffersR, _sizesR, configR, shapeR, frameR, allocR, nextR, pendingR⟩ :=
    full_clear_reset_effects stateM buffersM headM getM lookM availableM
  have bitsM := pending_bits_base treesM cursorM
  have bitsR := pendingR _ bitsM
  obtain ⟨_pb, produced, after, z', result, written, remaining, _pbuf, publishRun,
      stateA, buffersA, account, _sizes, storageA, _amount, _left, controls, _ready, data, pending, bits⟩ :=
    flush_pending_buffered_boundary stateR buffersR pointer bitsR
  have totals := flush_pending_low_run_counter_effects stateR.good buffersR pointer stateR.bits
    publishRun stateA.good.live.hz account
  have intervalA := flush_pending_low_run_output_effect stateR.good buffersR pointer stateR.bits
    publishRun stateA.good.live.hz account
  obtain ⟨_caller, _getOut, _writable, _boundOut, outside⟩ := caller_raw_output boundary.good buffers pointer
  have separate : ob ≠ pb := by
    intro same; subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  have intervalR : RawOutputInterval h resetHeap ob oo 0 := .of_same (by
    simp only [resetHeap, markerHeap, setD_bytes, setW_bytes, Zlib.Trees.Proofs.Out.setB,
      upd_ne _ _ _ _ separate])
  have interval : RawOutputInterval h after ob oo produced := by
    simpa only [Nat.add_zero, Nat.zero_add] using intervalR.trans intervalA
  have storageM := output_bits_storage (r := r) (ob := ob) (result := middle) (next := next)
    boundary.good.live.hs trees.base.bytes
  have frameM := storageM.private_frame trees.base.pbuf
  have frameReset : Frame markerHeap resetHeap (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) := by
    apply full_frame_weaken frameR
    intro b changed
    rcases changed with state | headKey
    · exact Or.inr (Or.inl (Or.inl state))
    · subst b
      exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl blocks.head)))))
  have configReset := (ConfigFrame.bits diffM).trans configR
  have frameA : Frame resetHeap after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) := by
    apply full_frame_weaken (storageA.private_frame _pbuf)
    intro b changed
    rcases changed with root | owned | output
    · exact Or.inl root
    · rw [configReset.owned] at owned
      exact Or.inr (Or.inl owned)
    · exact Or.inr (Or.inr output)
  have shapePrefix := storageM.shape.trans shapeR
  have shape := shapePrefix.trans storageA.shape
  have frame := full_frame_trans_shape
    (full_frame_trans_shape frameM frameReset storageM.shape) frameA shapePrefix
  refine ⟨produced, after, z', result, ?_, stateA.good, buffersA, account, totals.1, totals.2,
    interval, shape, frame, full_shape_live_change shape, ?_, ?_⟩
  · have markerSource : Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0 h = .ok ((), markerHeap) := markerRun
    rw [bind_app, markerSource]
    simp only []
    rw [bind_app, resetRun]
    exact publishRun
  · exact storageA.nalloc.trans (allocR.trans storageM.nalloc)
  · exact storageA.nextBlk.trans (nextR.trans storageM.nextBlk)

end Zlib.Deflate.Engine.Proofs
