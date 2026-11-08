import ZlibF.Proof.«deflate.c.engine.positive-nonfinal-call»

/-! # Nonfinal completion supplies actual marker publication room -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A completed nonfinal tail has an empty pending buffer even at zero
caller output capacity. This follows from the actual empty-symbol branch
or the nonfinal macro's output test, not a callee contract assumption. -/
theorem finish_tail_nonfinal_run_block_ready {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0)
    (flush : Int32) (nonfinal : flush ≠ Z_FINISH)
    (run : finish_tail (some (.tab ds)) flush h = .ok (block_done, after))
    (live : after.dstates ds = some result) : PublishReady result := by
  by_cases empty : d.sym_next = 0
  · have actual : finish_tail (some (.tab ds)) flush h = .ok (block_done, h) := by
      unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, empty, bne_self_eq_false, pure_app]
    have heaps : h = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    rw [← heaps] at live
    have states : d = result := Option.some.inj (boundary.good.live.hs.symm.trans live)
    rw [← states]
    exact ⟨pending, cursor, by omega⟩
  · obtain ⟨produced, other, otherZ, otherD, control, stateA, _buffersA, _accountA,
        _clearA, _fieldsA, _lowA, readyA⟩ :=
      flush_nonfinal_loop_boundary boundary buffers positive pointer cursor memory pending bits clear available
    have actual : finish_tail (some (.tab ds)) flush h =
        .ok ((if otherZ.avail_out == 0 then need_more else block_done), other) := by
      unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, bne_iff_ne.mpr empty, ite_true, control]
      by_cases exhausted : (otherZ.avail_out == 0) = true <;> simp [exhausted, pure_app]
    obtain ⟨returned, heaps⟩ := Prod.mk.inj (Except.ok.inj (actual.symm.trans run))
    have room : 0 < otherZ.avail_out.toNat := by
      by_cases zero : otherZ.avail_out = 0
      · simp [zero, show need_more ≠ block_done from by decide] at returned
      · have nonzero : otherZ.avail_out.toNat ≠ 0 := fun eq => zero (UInt32.toNat_inj.mp eq)
        omega
    have ready := readyA room
    rw [heaps] at stateA
    have states : otherD = result := Option.some.inj (stateA.good.live.hs.symm.trans live)
    rw [← states]
    exact ready

/-- Actual nonfinal tail execution retains the public status, last request
and empty pending cursor through either symbol-buffer branch. -/
theorem finish_tail_nonfinal_run_controls {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {ret : block_state} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0)
    (flush : Int32) (nonfinal : flush ≠ Z_FINISH)
    (run : finish_tail (some (.tab ds)) flush h = .ok (ret, after))
    (live : after.dstates ds = some result) : StrategyControls d result := by
  by_cases empty : d.sym_next = 0
  · have actual : finish_tail (some (.tab ds)) flush h = .ok (block_done, h) := by
      unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, empty, bne_self_eq_false, pure_app]
    have heaps : h = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    rw [← heaps] at live
    have states : d = result := Option.some.inj (boundary.good.live.hs.symm.trans live)
    rw [← states]
    exact ⟨fun _ => cursor, rfl, rfl⟩
  · obtain ⟨produced, other, otherZ, otherD, control, stateA, _buffersA, _accountA,
        _clearA, fieldsA, _lowA, _readyA⟩ :=
      flush_nonfinal_loop_boundary boundary buffers positive pointer cursor memory pending bits clear available
    have actual : finish_tail (some (.tab ds)) flush h =
        .ok ((if otherZ.avail_out == 0 then need_more else block_done), other) := by
      unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, bne_iff_ne.mpr empty, ite_true, control]
      by_cases exhausted : (otherZ.avail_out == 0) = true <;> simp [exhausted, pure_app]
    have cursorA := flush_control_run_empty_cursor boundary buffers positive pointer cursor memory pending bits clear available false
      control stateA.good.live.hs
    have heaps : other = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    rw [heaps] at stateA
    have states : otherD = result := Option.some.inj (stateA.good.live.hs.symm.trans live)
    rw [← states]
    exact ⟨cursorA, by rw [fieldsA], by rw [fieldsA]⟩

end Zlib.Deflate.Engine.Proofs
