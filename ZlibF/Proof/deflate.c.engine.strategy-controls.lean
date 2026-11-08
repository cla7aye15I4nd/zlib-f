import ZlibF.Proof.«deflate.c.engine.loop-phase»

/-! # Control fields retained by a compression strategy -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- Strategy execution retains the public status and last flush request,
and resets its pending cursor whenever no complete output remains. -/
structure StrategyControls (before after : DeflateState) : Prop where
  empty_cursor : after.pending = 0 → after.pending_out = after.pending_buf
  status : after.status = before.status
  last_flush : after.last_flush = before.last_flush

theorem StrategyControls.slow {before after : DeflateState}
    (ready : PublishReady before) (frame : SlowRecordFrame before after) :
    StrategyControls before after := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    rw [frame]
    exact ready.2.1
  · rw [frame]
  · rw [frame]

theorem StrategyControls.fill {before after : DeflateState}
    (ready : PublishReady before) (frame : FillRecordFrame before after) :
    StrategyControls before after := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    rw [frame]
    exact ready.2.1
  · rw [frame]
  · rw [frame]

end Zlib.Deflate.Engine.Proofs
