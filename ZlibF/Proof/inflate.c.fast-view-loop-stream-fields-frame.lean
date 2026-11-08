import ZlibF.Proof.«inffast.c.stream-fields-frame»
import ZlibF.Proof.«inflate.c.fast-view-loop-ready-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- The actual fast-loop condition only reads its byte views. -/
theorem streamFastFrameM_loop_cond (ctx : FastLoopContext)
    (q : Zlib.Inffast.L) :
    StreamFastFrameM ctx.r (fastLoopCond ctx q) := by
  unfold fastLoopCond
  repeat'
    first
    | exact streamFastFrameM_pure ctx.r _
    | exact streamFastFrameM_ptr_lt ctx.r _ _
    | apply streamFastFrameM_ite (r := ctx.r)
    | refine streamFastFrameM_bind (r := ctx.r) ?_ (fun value => ?_)

/-- Every successful actual fast-loop run preserves the whole stream
record except its error-message pointer, including broken exits. -/
theorem fast_loop_stream_fields_of_run
    {ctx : FastLoopContext} {h after : Heap}
    {q result : Zlib.Inffast.L}
    (run : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, after)) :
    StreamFastFrame ctx.r h after := by
  have frame : StreamFastFrameM ctx.r
      (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) := by
    apply streamFastFrameM_cdoWhile
    · intro state
      exact streamFastFrameM_body ctx.r ctx.zs ctx.c state
        ctx.streamPtr ctx.statePtr
    · intro state
      exact streamFastFrameM_loop_cond ctx state
  exact frame h result after run

/-- The stream counters, cursors, allocator fields and state pointer at a
fast-loop exit are those from its actual entry. Only `msg` may change. -/
theorem FastLoopReady.stream_fields_of_run
    {ctx : FastLoopContext} {h after : Heap}
    {q result : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q)
    (run : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, after))
    (final : FastLoopExit ctx after result) :
    ∃ zNext sNext,
      DefaultStateJ after ctx.r ctx.zs zNext sNext ∧
      streamFastFields zNext = streamFastFields ctx.z := by
  obtain ⟨_, _, _, _, _, _, invariant, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _⟩ := ready
  obtain ⟨_, _, zNext, sNext, _, nextJ, _⟩ := final
  have frame := fast_loop_stream_fields_of_run run
  have before := invariant.good.live.hz
  have afterGet := nextJ.good.live.hz
  simp only [StreamFastFrame, before, afterGet,
    Option.map_some, Option.some.injEq] at frame
  exact ⟨zNext, sNext, nextJ, frame⟩

#print axioms fast_loop_stream_fields_of_run
#print axioms FastLoopReady.stream_fields_of_run
end Zlib.Inflate.Proofs
