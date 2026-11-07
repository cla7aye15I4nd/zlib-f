import ZlibF.Proof.«deflate.c.engine.strategy-finish»

/-! # Actual final publication leaves no residual buffered bits -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real final encoding winds up its bit buffer before publication.
This holds for all three computed encodings and every output capacity. -/
theorem finish_tail_zero_execution {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (wrap : d.wrap = 1) :
    ∃ ret after z' result, finish_tail (some (.tab ds)) Z_FINISH h = .ok (ret, after) ∧
      DGood after r ds z' result ∧ result.bi_valid.toInt = 0 := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, wa, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have accounted0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨produced, after, z', result, written, remaining, kind, body, padding, macroRun,
      goodA, _buffers, _account, _sizes, _storage, _clear, _frequencies, _position, _low,
      _bytes, _pending, _drained, zeroNat, _rest⟩ :=
    flush_block_only_publish boundary.good trees buffers positive pointer cursor memory pending bits
      ledger clear boundary.trace win get boundary.range balance0 accounted0 view true
  have frame := flush_macro_run_frame boundary.good trees buffers positive pointer cursor memory pending bits
    ledger clear boundary.trace win get boundary.range balance0 accounted0 view true macroRun goodA.live.hs
  have zero : result.bi_valid.toInt = 0 := by
    have value := zeroNat rfl
    have lower := goodA.inv.bits.1
    omega
  have wrapA : result.wrap = 1 := by rw [frame]; exact wrap
  have macro1 : FLUSH_BLOCK_ONLY (some (.tab ds)) 1 h = .ok ((), after) := macroRun
  have controlRun : FLUSH_BLOCK (some (.tab ds)) 1 h =
      .ok ((if z'.avail_out == 0 then some finish_started else none), after) := by
    unfold FLUSH_BLOCK
    simp only [bind_app, macro1, ldDeflateState_tab goodA.live.hs, goodA.live.back, zrd_eq, goodA.live.hz]
    by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, wrapA, pure_app]
  refine ⟨if z'.avail_out == 0 then finish_started else finish_done, after, z', result, ?_, goodA, zero⟩
  unfold finish_tail
  simp only [beq_self_eq_true, ite_true, bind_app, controlRun]
  by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]

/-- Determinism attaches final zero bits to an established actual tail
execution and its actual state record. -/
theorem finish_tail_run_zero {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d result : DeflateState} {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (wrap : d.wrap = 1)
    (run : finish_tail (some (.tab ds)) Z_FINISH h = .ok (ret, after)) (live : after.dstates ds = some result) :
    result.bi_valid.toInt = 0 := by
  obtain ⟨otherRet, other, otherZ, otherD, otherRun, otherGood, zero⟩ :=
    finish_tail_zero_execution boundary buffers positive pointer cursor memory pending bits clear available wrap
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heaps] at otherGood
  have states : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans live)
  rw [← states]
  exact zero

end Zlib.Deflate.Engine.Proofs
