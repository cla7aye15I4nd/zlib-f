import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-content»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-literal-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-search-prefix»
import ZlibF.Proof.«deflate.c.engine.strategy-controls»
import ZlibF.Proof.«deflate.c.engine.finish-ready-step»
import ZlibF.Proof.«deflate.c.engine.positive-flush-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-body-controls»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_slow_body_run_controls {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d result : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after))
    (live : after.dstates ds = some result) : StrategyControls d result := by
  by_cases waiting : flush = Z_NO_FLUSH
  · subst flush
    exact (default_foreign_slow_no_flush_body_run_end_controls boundary frontier buffers positive pointer
      memory wrap publish inputValid run live).2
  · rw [slow_positive_body_source _ _ waiting _] at run
    exact default_foreign_slow_finish_body_run_controls boundary frontier buffers positive pointer
      memory wrap publish inputValid run live

end Zlib.Deflate.Engine.Proofs
