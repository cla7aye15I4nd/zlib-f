import ZlibF.Proof.«deflate.c.engine.flush-checksum»
import ZlibF.Proof.«deflate.c.engine.flush-macro-frame»
import ZlibF.Proof.«deflate.c.engine.control-empty-cursor»

/-! # Actual block macros and control returns retain the checksum -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual macro retains the checksum while publishing its bytes. -/
theorem flush_macro_adler_execution {h : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ z'.adler = z.adler := by
  have arguments := default_flush_arguments good trees memory ledger win get range balance
  obtain ⟨ze, ready, emitted, outputBuf, kind, body, padding, run, goodE, treesE, buffersE,
    accountE, _sizesE, _storageE, _ledgerE, _clearE, sizeE, boundE, cursorE, _finalE, _kindBound,
    _padBound, _padNone, _storedPad, _outputE, _grammar⟩ :=
    flush_default_ready (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  have effectsE := flush_default_run_adler (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
    win get range balance accounted view last run goodE.live.hz
  let updated : DeflateState := { emitted with block_start := emitted.strstart.toUInt64.toInt64 }
  obtain ⟨updateRun, goodU, treesU, buffersU, _sizesU, _storageU⟩ :=
    flush_block_start_engine (ob := ob) goodE treesE buffersE
  have nextOut : ze.next_out = z.next_out := by rw [accountE.2.2.2.2.2.1, advance_zero]
  have pointerE : ze.next_out = .ref (.blk ob) oo := nextOut.trans pointer
  have roomU : 8 * updated.pending.toNat + updated.bi_valid.toInt.toNat ≤ 8 * outputBuf.size := by
    rw [sizeE]
    have high := treesE.run.bi_hi
    have low := treesE.run.bi_lo
    change 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 524288
    omega
  obtain ⟨produced, after, z', result, written, remaining, flush, goodA, _buffersA, accountA,
    _sizesA, _storageA, _copied, _left, _low, _validA, fieldsA, _bytes, _pendingA, _outputA⟩ :=
    flush_pending_raw_bits goodU treesU buffersU pointerE cursorE roomU
  have effectsA := flush_pending_run_adler goodU treesU buffersU pointerE cursorE roomU flush goodA.live.hz accountA
  have account := stream_accounting_trans accountE accountA
  refine ⟨produced, after, z', result, ?_, goodA, by simpa only [Nat.zero_add] using account, ?_⟩
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
  · exact effectsA.trans effectsE

/-- Checksum preservation for any successful actual macro run. -/
theorem flush_macro_run_adler {h after : Heap} {r : ZStreamRef} {ds pb ob oo w origin base produced : Nat}
    {z z' : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool)
    (run : FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after))
    (live : r.get after = some z') (account : StreamAccounting z z' 0 produced) :
    z'.adler = z.adler := by
  obtain ⟨amount, other, ze, _stateE, runE, goodE, accountE, checksumE⟩ :=
    flush_macro_adler_execution good trees buffers positive pointer cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  have same := actual_run_stream_unique runE run goodE.live.hz live
  exact same ▸ checksumE

/-- Reading control fields after publication does not change the checksum. -/
theorem flush_control_run_adler {h after : Heap} {r : ZStreamRef} {ds ob oo origin base produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {ret : Option block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (last : Bool)
    (run : FLUSH_BLOCK (some (.tab ds)) (if last then 1 else 0) h = .ok (ret, after))
    (live : r.get after = some z') (account : StreamAccounting z z' 0 produced) :
    z'.adler = z.adler := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, wa, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have accounted0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨amount, other, otherZ, otherD, macroRun, goodA, accountA, checksumA⟩ :=
    flush_macro_adler_execution boundary.good trees buffers positive pointer cursor memory pending bits
      ledger clear boundary.trace win get boundary.range balance0 accounted0 view last
  let control : Option block_state :=
    if otherZ.avail_out == 0 then
      if last then
        if otherD.pending != 0 || otherD.wrap != 0 then some finish_started else none
      else some need_more
    else none
  have controlRun : FLUSH_BLOCK (some (.tab ds)) (if last then 1 else 0) h = .ok (control, other) := by
    unfold FLUSH_BLOCK
    simp only [bind_app, macroRun, ldDeflateState_tab goodA.live.hs, goodA.live.back, zrd_eq, goodA.live.hz]
    by_cases empty : (otherZ.avail_out == 0) = true <;>
      by_cases queued : (otherD.pending != 0 || otherD.wrap != 0) = true <;>
      cases last <;> simp [control, empty, queued, pure_app]
  have same := actual_run_stream_unique controlRun run goodA.live.hz live
  exact same ▸ checksumA

end Zlib.Deflate.Engine.Proofs
