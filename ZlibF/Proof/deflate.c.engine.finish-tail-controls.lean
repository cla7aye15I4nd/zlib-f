import ZlibF.Proof.«deflate.c.engine.finish-loop-controls»
import ZlibF.Proof.«deflate.c.engine.eof-zero»

/-! # The final control tail retains strategy controls -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Real final-block publication and the actual finishing return retain
the empty-cursor phase and public status/request fields. -/
theorem finish_tail_run_controls {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (wrap : d.wrap = 1)
    (run : finish_tail (some (.tab ds)) Z_FINISH h = .ok (ret, after))
    (live : after.dstates ds = some result) : StrategyControls d result := by
  obtain ⟨produced, other, otherZ, otherD, controlRun, boundaryA, _buffersA, _accountA, _clearA, frameA, _lowA, _phaseA⟩ :=
    flush_final_loop_boundary boundary buffers positive pointer cursor memory pending bits clear available wrap
  have cursorA := flush_control_run_empty_cursor boundary buffers positive pointer cursor memory pending bits clear available true
    controlRun boundaryA.good.live.hs
  have actualRun : finish_tail (some (.tab ds)) Z_FINISH h =
      .ok ((if otherZ.avail_out == 0 then finish_started else finish_done), other) := by
    unfold finish_tail
    simp only [beq_self_eq_true, ite_true, bind_app, controlRun]
    by_cases empty : (otherZ.avail_out == 0) = true <;> simp [empty, pure_app]
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
  rw [heaps] at boundaryA
  have states : otherD = result := Option.some.inj (boundaryA.good.live.hs.symm.trans live)
  rw [← states]
  exact ⟨cursorA, by rw [frameA], by rw [frameA]⟩

end Zlib.Deflate.Engine.Proofs
