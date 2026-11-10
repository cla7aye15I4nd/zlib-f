import ZlibF.Proof.«deflate.c.engine.positive-flush-loop»

/-! # Every signed request scalar has the same exact body output footprint -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The exact actual body output interval holds for every signed flush
scalar. This extends the separately proved NO_FLUSH/FINISH effects by an
exact source equality, without assuming the output behavior of a callee. -/
theorem slow_body_all_scalar_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS} {flush : Int32}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow_body (some (.tab ds)) flush st h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    RawOutputInterval h after ob oo produced := by
  by_cases waiting : flush = Z_NO_FLUSH
  · subst flush
    exact slow_no_flush_body_run_output_effect boundary frontier buffers positive pointer memory wrap publish inputValid run live account
  · rw [slow_positive_body_source _ _ waiting _] at run
    exact slow_finish_body_run_output_effect boundary frontier buffers positive pointer memory wrap publish inputValid run live account

end Zlib.Deflate.Engine.Proofs
