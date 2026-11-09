import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-tail-phase»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-finishing-tail-encoding»
import ZlibF.Proof.«deflate.c.engine.generic-output-append»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual finishing tail changes only its produced foreign-depth output interval.
Every output capacity is included; no extra owner or raw-storage condition is assumed. -/
theorem public_foreign_finishing_tail_run_output_interval {h after : Heap} {r : ZStreamRef}
    {ds owner oo produced : Nat} {z z' : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (phase : FinishingPhase d config)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (empty : z.avail_in=0) (pending : d.pending=0)
    (run : publicZlibHeader (some r) (some (.tab ds))
      (publicDataTail (some r) (some (.tab ds)) Z_FINISH) h=.ok (rc,after))
    (live : r.get after=some z') (account : StreamAccounting z z' 0 produced) :
    ByteOutputInterval h after (.dstate_depth owner) oo produced := by
  rcases phase.wrapper with wrap|wrap
  · obtain ⟨otherD,pb,buf,trees⟩ := good.trees
    have states : otherD=d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
    subst otherD
    obtain ⟨amount,other,otherZ,result,_written,_remaining,trailer,goodA,_buffersA,accountA,
      _sizes,_amount,_left,_wrap,_bits,_fields,_bytes,_pending,_wire,_adler,_input,_output,
      _alloc,_next,frame,_rest⟩ :=
      foreign_zlib_trailer_publish_encoding good trees buffers pointer wrap pending (phase.cursor wrap pending) phase.bits
    have actual := (public_finishing_header_source good phase empty).trans trailer
    have heaps : other=after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    rw [heaps] at goodA frame
    have streams : otherZ=z' := Option.some.inj (goodA.live.hz.symm.trans live)
    rw [streams] at accountA
    have amounts : amount=produced := (stream_accounting_counts_unique accountA account).2
    rw [amounts,pointer] at frame
    exact ByteOutputInterval.of_buffer_frame frame
  · have actual := public_finished_headers good phase.status empty phase.lookahead wrap
    have heaps : h=after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    have streams : z=z' := by
      have get := live
      rw [← heaps] at get
      exact Option.some.inj (good.live.hz.symm.trans get)
    rw [← streams] at account
    have count := account.2.2.2.1
    have amount : produced=0 := by omega
    rw [amount,← heaps]
    exact ByteOutputInterval.of_same rfl

end Zlib.Deflate.Engine.Proofs
