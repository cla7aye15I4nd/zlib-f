import ZlibF.Proof.«deflate.c.engine.short-match-emit-boundary»

/-! # Actual block publication retains the earlier EOF chain frontier -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual block encoding and publication preserve every hash node below
the last real input keys, including when caller output is exhausted. -/
theorem flush_macro_run_end_frontier {h after : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
    {z : ZStream} {d result : DeflateState} {buf wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i)) (last : Bool)
    (frontier : EndFrontier h d)
    (run : FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after))
    (live : after.dstates ds = some result) : EndFrontier after result := by
  obtain ⟨produced, other, otherZ, otherD, written, remaining, kind, body, padding, otherRun,
      otherGood, _buffers, _account, _sizes, storage, _rest⟩ :=
    flush_block_only_publish good trees buffers positive pointer cursor memory pending bits
      ledger clear trace win get range balance accounted view last
  have frame := flush_macro_run_frame good trees buffers positive pointer cursor memory pending bits
    ledger clear trace win get range balance accounted view last otherRun otherGood.live.hs
  have kept := flush_frames_chains storage good buffers pointer trees.base.pbuf frame frontier
  have start : otherD.strstart = d.strstart := by rw [frame]
  have endpoint : fillEnd otherD = fillEnd d := by rw [frame]; rfl
  have endOther : EndFrontier other otherD := by
    unfold EndFrontier
    simpa only [start, endpoint] using kept
  have heapEq : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heapEq] at otherGood endOther
  have stateEq : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans live)
  rw [← stateEq]
  exact endOther

/-- The actual nonfinal control wrapper preserves the content and EOF
boundaries on the same returned heap and stream. -/
theorem flush_nonfinal_end_boundary {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs) (frontier : EndFrontier h d)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) :
    ∃ produced after z' result,
      FLUSH_BLOCK (some (.tab ds)) 0 h =
        .ok ((if z'.avail_out == 0 then some need_more else none), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨produced, after, z', result, run, boundaryA, buffersA, accountA, clearA, frameA⟩ :=
    flush_block_only_content_boundary boundary buffers positive pointer cursor memory pending bits clear available false
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, wa, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have accounted0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  have endA := flush_macro_run_end_frontier boundary.good trees buffers positive pointer cursor memory pending bits
    ledger clear boundary.trace win get boundary.range balance0 accounted0 view false frontier run boundaryA.good.live.hs
  have phase := flush_macro_run_loop boundary.good trees buffers positive pointer cursor memory pending bits
    ledger clear boundary.trace win get boundary.range balance0 accounted0 view false run boundaryA.good.live.hs boundaryA.good.live.hz
  refine ⟨produced, after, z', result, ?_, boundaryA, endA, buffersA, accountA, clearA, frameA, phase.2.1, phase.2.2⟩
  have run0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 h = .ok ((), after) := run
  unfold FLUSH_BLOCK
  simp only [bind_app, run0, ldDeflateState_tab boundaryA.good.live.hs,
    boundaryA.good.live.back, zrd_eq, boundaryA.good.live.hz]
  by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]

end Zlib.Deflate.Engine.Proofs
