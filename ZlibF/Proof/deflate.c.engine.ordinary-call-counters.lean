import ZlibF.Proof.«deflate.c.engine.finish-call-counters»
import ZlibF.Proof.«deflate.c.engine.no-flush-call-counters»

/-! # Both complete actual ordinary strategy calls have exact totals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual complete ordinary strategy calls have exact public wrapping totals. -/
theorem deflate_slow_ordinary_run_counter_effects {h after : Heap} {r : ZStreamRef} {ds ob oo origin base accepted delivered : Nat}
    {z returnedZ : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state} {flush : Int32}
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) flush h = .ok (ret, after))
    (live : r.get after = some returnedZ) (account : StreamAccounting z returnedZ accepted delivered) :
    returnedZ.total_in = z.total_in + UInt64.ofNat accepted ∧
      returnedZ.total_out = z.total_out + UInt64.ofNat delivered := by
  rcases flag with rfl | rfl
  · exact deflate_slow_no_flush_run_counter_effects boundary frontier buffers positive pointer memory wrap publish inputValid run live account
  · exact deflate_slow_finish_run_counter_effects boundary frontier buffers positive pointer memory wrap publish inputValid run live account

end Zlib.Deflate.Engine.Proofs
