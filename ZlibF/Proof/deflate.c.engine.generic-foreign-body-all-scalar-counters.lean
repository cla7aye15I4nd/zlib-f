import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-counters»
import ZlibF.Proof.«deflate.c.engine.positive-flush-loop»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Exact wrapping total counters for the actual default-memory foreign-output slow
body, for every signed flush scalar. Comparison room is derived internally, and no
callee execution, counter or effect contract is a caller premise. -/
theorem default_foreign_slow_body_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds owner oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    returned.total_in=z.total_in+UInt64.ofNat used ∧ returned.total_out=z.total_out+UInt64.ofNat produced := by
  by_cases waiting : flush = Z_NO_FLUSH
  · subst flush
    exact default_foreign_slow_no_flush_body_run_counter_effects boundary frontier buffers positive pointer memory wrap publish inputValid run live account
  · rw [slow_positive_body_source _ _ waiting _] at run
    exact default_foreign_slow_finish_body_run_counter_effects boundary frontier buffers positive pointer memory wrap publish inputValid run live account

end Zlib.Deflate.Engine.Proofs
