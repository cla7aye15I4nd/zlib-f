import ZlibF.Proof.«deflate.c.engine.pending-loop-phase»
import ZlibF.Proof.«deflate.c.engine.flush-control»

/-! # Actual flush macros retain the continuing strategy phase -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual computed encoding, reset, block-start store and publication
retain the input/configuration footprint and the low-bit phase. If caller
output remains, pending storage is ready for the next strategy iteration. -/
theorem flush_macro_loop_execution {h : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) :
    ∃ (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) := by
  have arguments := default_flush_arguments good trees memory ledger win get range balance
  obtain ⟨ze, ready, emitted, outputBuf, kind, body, padding, run, goodE, treesE, buffersE,
    accountE, _sizesE, _storageE, _ledgerE, _clearE, sizeE, boundE, cursorE, _finalE, _kindBound,
    _padBound, _padNone, _storedPad, _outputE, _grammar⟩ :=
    flush_default_ready (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  have frame := flush_default_run_frame (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
    win get range balance accounted view last run goodE.live.hs
  have start : emitted.strstart = d.strstart := by rw [frame]
  let updated : DeflateState := { emitted with block_start := emitted.strstart.toUInt64.toInt64 }
  obtain ⟨updateRun, goodU, treesU, buffersU, _sizesU, _storageU⟩ :=
    flush_block_start_engine (ob := ob) goodE treesE buffersE
  have frameU : FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } updated := by
    simpa only [updated, start] using (frame.block_start emitted.strstart.toUInt64.toInt64)
  have nextOut : ze.next_out = z.next_out := by rw [accountE.2.2.2.2.2.1, advance_zero]
  have pointerE : ze.next_out = .ref (.blk ob) oo := nextOut.trans pointer
  have roomU : 8 * updated.pending.toNat + updated.bi_valid.toInt.toNat ≤ 8 * outputBuf.size := by
    rw [sizeE]
    have high := treesE.run.bi_hi
    have low := treesE.run.bi_lo
    change 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 524288
    omega
  obtain ⟨produced, after, z', result, written, remaining, flush, goodA, _buffersA, _accountA,
    _sizesA, _storageA, _copied, _left, _low, _validA, fieldsA, _bytes, _pendingA, _outputA⟩ :=
    flush_pending_raw_bits goodU treesU buffersU pointerE cursorE roomU
  have phase := pending_publication_run_phase goodU treesU buffersU pointerE cursorE roomU
    flush goodA.live.hs goodA.live.hz
  refine ⟨after, z', result, ?_, goodA, ?_, phase.2.1, phase.2.2⟩
  · have streamRead : rd (some (.tab ds)) (·.strm) (setD ready ds updated) =
        .ok (some r, setD ready ds updated) := by
      simp only [rdD_eq, setD_dstates_same]
      rw [show updated.strm = some r from goodE.live.back]
    rw [flush_block_only_arguments_source, bind_app, arguments]
    simp only [bind_app, run, updateRun]
    change (rd (some (.tab ds)) (·.strm) >>= fun strm => flush_pending strm)
      (setD ready ds updated) = .ok ((), after)
    rw [bind_app, streamRead]
    exact flush
  · rw [fieldsA]
    exact frameU.output _ _ _ _ _

/-- Determinism transfers the proved loop phase to an established actual
macro run, including the exact returned stream rather than its input view. -/
theorem flush_macro_run_loop {h after : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
    {z z' : ZStream} {d result : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) 
    (run : FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after))
    (live : after.dstates ds = some result) (stream : r.get after = some z') :
    FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨otherHeap, otherZ, otherD, otherRun, otherGood, frame, low, phase⟩ :=
    flush_macro_loop_execution good trees buffers positive pointer cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  have heapEq : otherHeap = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heapEq] at otherGood
  have stateEq : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans live)
  have streamEq : otherZ = z' := Option.some.inj (otherGood.live.hz.symm.trans stream)
  rw [← stateEq, ← streamEq]
  exact ⟨frame, low, phase⟩

/-- The real nonfinal control wrapper retains the initialized content
boundary and the publication phase needed for another loop iteration.
Its need_more test uses the same returned stream as the phase conclusion. -/
theorem flush_nonfinal_loop_boundary {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK (some (.tab ds)) 0 h =
        .ok ((if z'.avail_out == 0 then some need_more else none), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨produced, after, z', result, run, boundaryA, buffersA, accountA, clearA, frameA⟩ :=
    flush_block_only_content_boundary boundary buffers positive pointer cursor memory pending bits clear available false
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, window, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have accounted0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  have phase := flush_macro_run_loop boundary.good trees buffers positive pointer cursor memory pending bits
    ledger clear boundary.trace win get boundary.range balance0 accounted0 view false run
    boundaryA.good.live.hs boundaryA.good.live.hz
  refine ⟨produced, after, z', result, ?_, boundaryA, buffersA, accountA, clearA, frameA, phase.2.1, phase.2.2⟩
  have run0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 h = .ok ((), after) := run
  unfold FLUSH_BLOCK
  simp only [bind_app, run0, ldDeflateState_tab boundaryA.good.live.hs,
    boundaryA.good.live.back, zrd_eq, boundaryA.good.live.hz]
  by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]

end Zlib.Deflate.Engine.Proofs
