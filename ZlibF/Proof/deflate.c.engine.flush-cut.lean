import ZlibF.Proof.«deflate.c.engine.flush-storage-frame»

/-! # The actual flush macro returns to the no-deferred-byte content boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual macro leaves zero packed symbols even when publication
is partial. This strengthens the reset data without changing the earlier
publication theorem or assuming a reset contract. -/
theorem flush_macro_empty_symbols_execution {h : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
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
      result.sym_next = 0 := by
  have arguments := default_flush_arguments good trees memory ledger win get range balance
  obtain ⟨ze, ready, emitted, outputBuf, kind, body, padding, run, goodE, treesE, buffersE,
    accountE, _sizesE, _storageE, _ledgerE, _clearE, sizeE, boundE, cursorE, _finalE, _kindBound,
    _padBound, _padNone, _storedPad, _outputE, _grammar⟩ :=
    flush_default_ready (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
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
    change emitted.sym_next = 0
    apply UInt32.toNat_inj.mp
    change emitted.sym_next.toNat = 0
    simpa only [List.length_nil, Nat.mul_zero] using _ledgerE.count


/-- A real flush at an ordinary content boundary with no deferred byte
returns to the same initialized boundary with an empty block. All actual
encoding choices and zero/short caller output are included. The new base
is the end of the old represented block. The literal branch's half-step
with a deferred byte needs its own subsequent advance proof. -/
theorem flush_block_only_content_boundary {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (last : Bool) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, window, win, get, view, form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have account0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨produced, after, z', result, written, remaining, kind, body, padding,
    run, goodA, buffersA, accountA, _sizesA, storageA, clearA, frequenciesA, positionA,
    _lowA, _bytesA, _pendingA, _drainedA, _finalA, _kindA, _padBound, _padNone, _storedPad,
    _outputA, _grammarA⟩ :=
    flush_block_only_publish boundary.good trees buffers positive pointer cursor memory pending bits
      ledger clear boundary.trace win get boundary.range balance0 account0 view last
  have frame := flush_macro_run_frame boundary.good trees buffers positive pointer cursor memory pending bits
    ledger clear boundary.trace win get boundary.range balance0 account0 view last run goodA.live.hs
  have startA : result.strstart = d.strstart := by rw [frame]
  have insertA : result.insert = d.insert := by rw [frame]
  have availableA : result.match_available = 0 := by rw [frame]; exact available
  obtain ⟨emptyHeap, emptyZ, emptyState, emptyRun, emptyGood, count⟩ :=
    flush_macro_empty_symbols_execution boundary.good trees buffers positive pointer cursor memory pending bits
      ledger clear boundary.trace win get boundary.range balance0 account0 view last
  have heapEq : emptyHeap = after := (Prod.mk.inj (Except.ok.inj (emptyRun.symm.trans run))).2
  rw [heapEq] at emptyGood
  have stateEq : emptyState = result := Option.some.inj (emptyGood.live.hs.symm.trans goodA.live.hs)
  rw [stateEq] at count
  obtain ⟨stateA, blockA, bufA, treesA⟩ := goodA.trees
  have resultEq : stateA = result := Option.some.inj (treesA.base.dstate.symm.trans goodA.live.hs)
  subst stateA
  have emptyLedger : SymbolLedger bufA result [] := empty_symbol_ledger count frequenciesA
  have cast : result.strstart.toUInt64.toInt64.toInt = (result.strstart.toNat : Int) := by
    have bound := result.strstart.toNat_lt
    rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
    · simp
    · simp; omega
  have balanceA : BlockBalance result [] (deferredCredit result) := by
    simp only [BlockBalance, positionA, cast, represented, deferredCredit, availableA, ite_true]
    omega
  have chainsA := flush_frames_chains storageA boundary.good buffers pointer trees.base.pbuf frame boundary.chains
  have frontierA := flush_frames_chains storageA boundary.good buffers pointer trees.base.pbuf frame boundary.frontier
  obtain ⟨wc, p, q, wa, pa, qa, winC, prev, head, getC, getPrev, getHead, _chainC⟩ := boundary.chains
  have windowEq : wc = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using winC.symm
  subst wc
  have arrayEq : wa = window := Option.some.inj (getC.symm.trans get)
  subst wa
  have kept := storageA.private_arrays boundary.good buffers pointer win get prev getPrev head getHead trees.base.pbuf
  refine ⟨produced, after, z', result, run, ?_, buffersA, accountA, clearA, frame⟩
  refine ⟨⟨⟨goodA, ?_, ?_, ?_, ?_, ⟨blockA, bufA, treesA, emptyLedger, balanceA⟩, ?_⟩,
    ?_, ?_, ?_⟩, Trace.empty, ?_⟩
  · simpa only [startA] using chainsA
  · rw [frame]; exact boundary.range
  · rw [frame]; exact boundary.history
  · rw [frame]; exact boundary.deferred
  · refine ⟨w, window, ?_, kept.1, ?_, ?_⟩
    · rw [frame]; exact win
    · rw [frame]; exact view
    · rw [frame]; exact form
  · rw [startA, insertA]; exact boundary.insert_le
  · simpa only [startA, insertA] using frontierA
  · rw [frame]; exact boundary.ready
  · simpa only [represented, pendingCredit, availableA, ite_true, Nat.add_zero, startA] using account0

end Zlib.Deflate.Engine.Proofs
