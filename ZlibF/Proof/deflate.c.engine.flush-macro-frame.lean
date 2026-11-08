import ZlibF.Proof.«deflate.c.engine.flush-default-frame»

/-! # The real flush macro keeps window, hashes, positions and match history -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- All actual macro stages preserve the strategy/history state except
the explicit block_start reset. This includes full computed encoding
selection and arbitrary caller output capacity, not a chosen encoder. -/
theorem flush_macro_frame_execution {h : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
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
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result := by
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
  refine ⟨after, z', result, ?_, goodA, ?_⟩
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

/-- The independently checked macro frame applies to any established
actual successful macro run, by heap/result determinism. -/
theorem flush_macro_run_frame {h after : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
    {z : ZStream} {d result : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool)
    (run : FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after))
    (live : after.dstates ds = some result) :
    FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result := by
  obtain ⟨frameHeap, z', frameState, frameRun, frameGood, frame⟩ :=
    flush_macro_frame_execution (ob := ob) good trees buffers positive pointer cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  have sameHeap : frameHeap = after := (Prod.mk.inj (Except.ok.inj (frameRun.symm.trans run))).2
  rw [sameHeap] at frameGood
  have sameState : frameState = result := Option.some.inj (frameGood.live.hs.symm.trans live)
  rw [← sameState]
  exact frame

end Zlib.Deflate.Engine.Proofs
