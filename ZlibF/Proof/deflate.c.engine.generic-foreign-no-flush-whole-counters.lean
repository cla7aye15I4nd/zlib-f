import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-counters»
import ZlibF.Proof.«deflate.c.engine.no-flush-call-counters»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Exact totals on any actual complete NO_FLUSH strategy return. -/
theorem default_foreign_deflate_slow_no_flush_run_counter_effects {h after : Heap} {r : ZStreamRef} {ds owner oo origin base accepted delivered : Nat}
    {z returnedZ : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_NO_FLUSH h = .ok (ret, after))
    (live : r.get after = some returnedZ) (account : StreamAccounting z returnedZ accepted delivered) :
    returnedZ.total_in = z.total_in + UInt64.ofNat accepted ∧
      returnedZ.total_out = z.total_out + UInt64.ofNat delivered := by
  rw [deflate_slow_eof_tail_source] at run
  cases loop : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h with
  | error fault => simp only [bind_app,loop] at run; cases run
  | ok pair =>
    obtain ⟨final,middle⟩ := pair
    have returned := default_foreign_slow_no_flush_ready_loop_run_control boundary frontier buffers positive pointer memory wrap publish inputValid loop
    simp only [bind_app,loop,returned,pure_app] at run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact default_foreign_slow_loop_run_counter_effects boundary frontier buffers positive pointer memory wrap publish inputValid loop live account

end Zlib.Deflate.Engine.Proofs
