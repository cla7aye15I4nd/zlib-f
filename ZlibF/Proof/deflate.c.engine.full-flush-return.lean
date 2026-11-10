import ZlibF.Proof.«deflate.c.engine.full-marker-publication»
import ZlibF.Proof.«deflate.c.engine.public-positive-source»
import ZlibF.Proof.«deflate.c.engine.public-buffered-pending»

/-! # Actual FULL public return includes hash reset and exhausted output -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The exact FULL public return retains the source order marker, hash
clear, position reset, pending publication and exhaustion retry store. -/
theorem public_strategy_full_source (strm : ZStreamPtr) (s : DeflateStatePtr) :
    publicStrategyReturn strm s Z_FULL_FLUSH block_done = (do
      let _ ← (do
        Zlib.Trees.«_tr_stored_block» s .null 0 0
        let _ ← (do
          CLEAR_HASH s
          if (← rd s (·.lookahead)) == 0 then
            wr s (fun d => { d with strstart := 0, block_start := 0, insert := 0 }))
        flush_pending strm)
      if (← zrd strm (·.avail_out)) == 0 then
        wr s (fun d => { d with last_flush := -1 })
        return Z_OK
      return Z_OK) := by
  have liftIf {α β : Type} (c : Prop) [Decidable c] (a b : M α) (k : α → M β) :
      ((if c then a else b) >>= k) = (if c then a >>= k else b >>= k) := by
    by_cases yes : c <;> simp only [yes, ite_true, ite_false]
  simp only [publicStrategyReturn, publicFinishTail,
    show (block_done == finish_started) = false from rfl,
    show (block_done == finish_done) = false from rfl,
    show (block_done == need_more) = false from rfl,
    show (Z_FULL_FLUSH == Z_PARTIAL_FLUSH) = false from rfl,
    show (Z_FULL_FLUSH != Z_BLOCK) = true from rfl,
    show (Z_FULL_FLUSH != Z_FINISH) = true from rfl,
    beq_self_eq_true, Bool.false_or, Bool.false_eq_true, ite_false, ite_true, M_bind_assoc,
    liftIf, M_pure_bind]

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt outBits storedHeaderBits)
set_option autoImplicit false

/-- Complete FULL block-done return, including hash reset and every output
capacity. The next boundary uses the same absolute input block endpoint. -/
theorem public_strategy_full_done {h : Heap} {r : ZStreamRef} {ds pb ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (publish : PublishReady d)
    (look : d.lookahead = 0) (available : d.match_available = 0) :
    ∃ produced after z' result written remaining,
      publicStrategyReturn (some r) (some (.tab ds)) Z_FULL_FLUSH block_done h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input base base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ConfigFrame d result ∧ result.status = d.status ∧
      (result.last_flush = d.last_flush ∨ result.last_flush = -1) ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = outBits buf d ++ storedHeaderBits d 0 false := by
  obtain ⟨produced, middle, z', result, written, remaining, run, stateA, buffersA, account,
      frame, statusA, lastA, data, pending, bits⟩ :=
    empty_full_marker_publish boundary buffers trees pointer publish look available
  have source : publicStrategyReturn (some r) (some (.tab ds)) Z_FULL_FLUSH block_done h =
      (if z'.avail_out == 0 then
        .ok (Z_OK, setD middle ds { result with last_flush := -1 }) else .ok (Z_OK, middle)) := by
    rw [public_strategy_full_source, bind_app, run]
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
    exact ⟨produced, _, z', _, written, remaining, by simpa only [exhausted, ite_true] using source,
      stateF, last_flush_buffers stateA.good buffersA (-1), account, frame.trans (by rfl),
      statusA, Or.inr rfl, dataF, last_flush_pending_bits stateA.good pending (-1), bits⟩
  · exact ⟨produced, middle, z', result, written, remaining,
      by simpa only [exhausted, Bool.false_eq_true, ite_false] using source,
      stateA, buffersA, account, frame, statusA, Or.inl lastA, data, pending, bits⟩

end Zlib.Deflate.Engine.Proofs
