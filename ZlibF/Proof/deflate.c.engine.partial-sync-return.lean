import ZlibF.Proof.«deflate.c.engine.partial-sync-publication»
import ZlibF.Proof.«deflate.c.engine.public-positive-source»
import ZlibF.Proof.«deflate.c.engine.public-buffered-pending»

/-! # Actual partial and sync public return paths preserve the boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual PARTIAL/SYNC public return contains exactly its real marker,
pending publication and output-exhaustion retry store. -/
theorem public_strategy_partial_sync_source (strm : ZStreamPtr) (s : DeflateStatePtr)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH) :
    publicStrategyReturn strm s flush block_done = (do
      let _ ← (do
        let _ ← (if flush == Z_PARTIAL_FLUSH then Zlib.Trees.«_tr_align» s
          else Zlib.Trees.«_tr_stored_block» s .null 0 0)
        flush_pending strm)
      if (← zrd strm (·.avail_out)) == 0 then
        wr s (fun d => { d with last_flush := -1 })
        return Z_OK
      return Z_OK) := by
  rcases flag with rfl | rfl <;>
    simp only [publicStrategyReturn, publicFinishTail,
      show (block_done == finish_started) = false from rfl,
      show (block_done == finish_done) = false from rfl,
      show (block_done == need_more) = false from rfl,
      show (Z_PARTIAL_FLUSH == Z_PARTIAL_FLUSH) = true from rfl,
      show (Z_SYNC_FLUSH == Z_PARTIAL_FLUSH) = false from rfl,
      show (Z_SYNC_FLUSH != Z_BLOCK) = true from rfl,
      show (Z_SYNC_FLUSH == Z_FULL_FLUSH) = false from rfl,
      show (Z_PARTIAL_FLUSH != Z_FINISH) = true from rfl,
      show (Z_SYNC_FLUSH != Z_FINISH) = true from rfl,
      beq_self_eq_true, Bool.false_or, Bool.false_eq_true, ite_false, ite_true, M_bind_assoc]

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt outBits natBits storedHeaderBits)
set_option autoImplicit false

/-- Actual PARTIAL/SYNC block-done return preserves the caller-independent
boundary, exact accounting, output bits and allocation footprint. Marker
room follows from the initialized tree buffer; caller capacity may be zero.
This proves the concrete public return cutpoint, not the full entry. -/
theorem public_strategy_partial_sync_done {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (flush : Int32) (flag : flush = Z_PARTIAL_FLUSH ∨ flush = Z_SYNC_FLUSH) :
    ∃ produced after z' result written remaining,
      publicStrategyReturn (some r) (some (.tab ds)) flush block_done h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      ConfigFrame d result ∧ result.status = d.status ∧
      (result.last_flush = d.last_flush ∨ result.last_flush = -1) ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = outBits buf d ++
        (if flush == Z_PARTIAL_FLUSH then natBits 2 3 ++ (natBits 0 7 ++ [])
          else storedHeaderBits d 0 false) := by
  have room : 8 ≤ buf.size := by
    have extent := trees.base.size
    have lower := trees.base.lit_lo
    omega
  obtain ⟨produced, middle, z', result, written, remaining, run, stateA, buffersA, account,
      sizes, storage, frame, statusA, lastA, _ready, data, pending, bits⟩ :=
    empty_partial_sync_publish boundary buffers trees pointer publish room flush flag
  have fields : result.status = d.status ∧ result.last_flush = d.last_flush := ⟨statusA, lastA⟩
  have source : publicStrategyReturn (some r) (some (.tab ds)) flush block_done h =
      (if z'.avail_out == 0 then
        .ok (Z_OK, setD middle ds { result with last_flush := -1 }) else .ok (Z_OK, middle)) := by
    rw [public_strategy_partial_sync_source _ _ flush flag, bind_app, run]
    simp only [bind_app, zrd_eq, stateA.good.live.hz]
    split <;> simp only [wrD_eq, stateA.good.live.hs, bind_app, pure_app]
  by_cases exhausted : (z'.avail_out == 0) = true
  · have stateF := last_flush_buffered_boundary stateA (-1)
    have dataF : Bytes (setD middle ds { result with last_flush := -1 }) z.next_out produced written := by
      have kept : ∀ ref : BRef, Space.get (setD middle ds { result with last_flush := -1 }) ref = Space.get middle ref :=
        byte_view_setD_depth stateA.good.live.hs rfl
      rcases data with zero | ⟨ref, off, array, ptr, read, bound, value⟩
      · exact Or.inl zero
      · exact Or.inr ⟨ref, off, array, ptr, (kept ref).trans read, bound, value⟩
    obtain ⟨oldD, pba, ba, treesA⟩ := stateA.good.trees
    have sameD : oldD = result := Option.some.inj (treesA.base.dstate.symm.trans stateA.good.live.hs)
    subst oldD
    have pbEq : pba = pb := by
      have pendingA : result.pending_buf = d.pending_buf := congrArg EngineConfig.pending frame
      simpa only [pendingA, trees.base.pbuf, Ptr.ref.injEq, BRef.blk.injEq, and_true] using treesA.base.pbuf.symm
    subst pba
    refine ⟨produced, _, z', _, written, remaining, by simpa only [exhausted, ite_true] using source,
      stateF, last_flush_buffers stateA.good buffersA (-1), account,
      sizes.trans (last_flush_sizes stateA.good.live.hs (-1)),
      storage.trans (last_flush_storage stateA.good treesA.base.bytes (-1)), ?_, fields.1, Or.inr rfl,
      dataF, last_flush_pending_bits stateA.good pending (-1), bits⟩
    exact frame.trans (by rfl)
  · exact ⟨produced, middle, z', result, written, remaining,
      by simpa only [exhausted, Bool.false_eq_true, ite_false] using source,
      stateA, buffersA, account, sizes, storage, frame, fields.1, Or.inl fields.2, data, pending, bits⟩

end Zlib.Deflate.Engine.Proofs
