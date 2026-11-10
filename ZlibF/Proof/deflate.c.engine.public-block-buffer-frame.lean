import ZlibF.Proof.«deflate.c.engine.public-block-effects»
import ZlibF.Proof.«deflate.c.engine.public-output-bytes»

/-! # Precise caller byte slice and BufferFrame for the BLOCK data path -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual BUSY default BLOCK data path returns its produced-byte
slice, exact public BufferFrame, counters and unchanged allocation ledger.
The initialized engine and raw caller buffers are explicit. Public entry,
first headers, old pending bytes, other markers and complete call histories
are separate obligations; this does not prove Goal.deflate. -/
theorem public_busy_slow_block_buffer_frame {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ used written after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_BLOCK h = .ok (Z_OK, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧ z'.total_out = z.total_out + UInt64.ofNat written.length ∧
      Shape h after ∧ BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨used, produced, after, z', result, run, goodA, buffersA, account, inputA, outputA,
      interval, shape, frame, live, alloc, next⟩ :=
    public_busy_slow_block_effect_execution boundary frontier buffers status level strategy pointer memory wrap publish inputValid
  obtain ⟨written, data, length⟩ := accounted_output_bytes goodA.live.hz buffersA pointer account
  have exactFrame := interval.buffer_frame boundary.good goodA buffers buffersA pointer account shape frame
  rw [← length] at account data outputA exactFrame
  exact ⟨used, written, after, z', result, run, goodA, buffersA, account, data,
    inputA, outputA, shape, exactFrame, live, alloc, next⟩

end Zlib.Deflate.Engine.Proofs
