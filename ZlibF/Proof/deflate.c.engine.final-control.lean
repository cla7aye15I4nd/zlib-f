import ZlibF.Proof.«deflate.c.engine.flush-loop-phase»

/-! # Actual final-block control and strategy finish tail -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The default zlib wrapper still needs its trailer after final block
publication. Exhausted output therefore returns finish_started, even if
the block bytes themselves were fully copied. -/
theorem flush_final_loop_boundary {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (wrap : d.wrap = 1) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK (some (.tab ds)) 1 h =
        .ok ((if z'.avail_out == 0 then some finish_started else none), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨produced, after, z', result, run, boundaryA, buffersA, accountA, clearA, frameA⟩ :=
    flush_block_only_content_boundary boundary buffers positive pointer cursor memory pending bits clear available true
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, window, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have accounted0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  have phase := flush_macro_run_loop boundary.good trees buffers positive pointer cursor memory pending bits
    ledger clear boundary.trace win get boundary.range balance0 accounted0 view true run
    boundaryA.good.live.hs boundaryA.good.live.hz
  refine ⟨produced, after, z', result, ?_, boundaryA, buffersA, accountA, clearA, frameA, phase.2.1, phase.2.2⟩
  have run1 : FLUSH_BLOCK_ONLY (some (.tab ds)) 1 h = .ok ((), after) := run
  have wrapA : result.wrap = 1 := by rw [frameA]; exact wrap
  unfold FLUSH_BLOCK
  simp only [bind_app, run1, ldDeflateState_tab boundaryA.good.live.hs,
    boundaryA.good.live.back, zrd_eq, boundaryA.good.live.hz]
  by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app, wrapA]

/-- The actual Z_FINISH tail obeys the final macro return on the same heap. -/
theorem finish_tail_final_boundary {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (wrap : d.wrap = 1) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      finish_tail (some (.tab ds)) Z_FINISH h =
        .ok ((if z'.avail_out == 0 then finish_started else finish_done), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨produced, after, z', result, run, boundaryA, buffersA, accountA, clearA, frameA, lowA, phaseA⟩ :=
    flush_final_loop_boundary boundary buffers positive pointer cursor memory pending bits clear available wrap
  refine ⟨produced, after, z', result, ?_, boundaryA, buffersA, accountA, clearA, frameA, lowA, phaseA⟩
  unfold finish_tail
  simp only [beq_self_eq_true, ite_true, bind_app, run]
  by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]

end Zlib.Deflate.Engine.Proofs
