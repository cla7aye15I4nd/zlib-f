import ZlibF.Proof.«deflate.c.engine.eof-output-interval»
import ZlibF.Proof.«deflate.c.engine.nonfinal-eof-control»

/-! # Exact accounting and storage effects of a nonfinal strategy tail -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual nonfinal publication, including the empty-symbol no-op,
retains exact wrapping totals, the caller output interval, all other heap
objects and the live/allocation ledger on the same returned heap. -/
theorem finish_tail_nonfinal_run_effects {h after : Heap} {r : ZStreamRef} {ds ob oo origin base produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0)
    (flush : Int32) (nonfinal : flush ≠ Z_FINISH)
    (run : finish_tail (some (.tab ds)) flush h = .ok (ret, after))
    (live : r.get after = some z') (account : StreamAccounting z z' 0 produced) :
    z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      RawOutputInterval h after ob oo produced ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases empty : d.sym_next = 0
  · have actual : finish_tail (some (.tab ds)) flush h = .ok (block_done, h) := by
      unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, empty, bne_self_eq_false, pure_app]
    have heaps : h = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    rw [← heaps] at live ⊢
    have streams : z' = z := Option.some.inj (live.symm.trans boundary.good.live.hz)
    subst z'
    have count : produced = 0 := (stream_accounting_counts_unique account (stream_accounting_zero z)).2
    subst produced
    exact ⟨rfl, by simp, RawOutputInterval.of_same rfl, full_storage_refl h _⟩
  · obtain ⟨amount, other, otherZ, otherD, control, stateA, _buffersA, accountA,
        _clearA, _fieldsA, _lowA, _readyA⟩ :=
      flush_nonfinal_loop_boundary boundary buffers positive pointer cursor memory pending bits clear available
    have totals := flush_control_run_counter_effects boundary buffers positive pointer cursor memory pending bits clear available false
      control stateA.good.live.hz accountA
    have interval := flush_control_run_output_effect boundary buffers positive pointer cursor memory pending bits clear available false
      control stateA.good.live.hz accountA
    have storage := flush_control_run_full_storage boundary buffers positive pointer cursor memory pending bits clear available false control
    have actual : finish_tail (some (.tab ds)) flush h =
        .ok ((if otherZ.avail_out == 0 then need_more else block_done), other) := by
      unfold finish_tail
      simp only [beq_eq_false_iff_ne.mpr nonfinal, Bool.false_eq_true, ite_false,
        bind_app, rdD_eq, boundary.good.live.hs, bne_iff_ne.mpr empty, ite_true, control]
      by_cases exhausted : (otherZ.avail_out == 0) = true <;> simp [exhausted, pure_app]
    have heaps : other = after := (Prod.mk.inj (Except.ok.inj (actual.symm.trans run))).2
    rw [heaps] at stateA storage interval
    have streams : otherZ = z' := Option.some.inj (stateA.good.live.hz.symm.trans live)
    subst otherZ
    have count : amount = produced := (stream_accounting_counts_unique accountA account).2
    rw [count] at totals interval
    exact ⟨totals.1, totals.2, interval, storage⟩

end Zlib.Deflate.Engine.Proofs
