import ZlibF.Proof.«deflate.c.engine.raw-output-frame»

/-! # Exact caller output intervals through actual computed block publication -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Specializing an encoder's arbitrary output key to its pending key gives its private footprint. -/
theorem OutputStorage.pending_private_frame {h g : Heap} {r : ZStreamRef} {ds pb : Nat} {d : DeflateState}
    (storage : OutputStorage h g r ds pb pb) (pending : d.pending_buf = .ref (.blk pb) 0) :
    Frame h g (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
  apply full_frame_weaken (storage.private_frame pending)
  intro b changed
  rcases changed with root | owned | same
  · exact Or.inl root
  · exact Or.inr owned
  · subst b
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr pending))))

/-- The actual macro preserves every caller byte outside its accounted interval.
All stored/fixed/dynamic choices and zero/short publication are included. -/
theorem flush_macro_run_output_interval {h after : Heap} {r : ZStreamRef}
    {ds pb ob oo w origin base produced : Nat} {z z' : ZStream} {d : DeflateState}
    {buf window before : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool)
    (run : FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after))
    (live : r.get after = some z') (account : StreamAccounting z z' 0 produced) (getBefore : h.bytes ob = some before) :
    ∃ next, after.bytes ob = some next ∧ next.size = before.size ∧
      ∀ j, j < before.size → ¬ (oo ≤ j ∧ j < oo + produced) → next[j]? = before[j]? := by
  have arguments := default_flush_arguments good trees memory ledger win get range balance
  obtain ⟨ze, ready, emitted, outputBuf, _kind, _body, _padding, encodeRun, goodE, treesE, buffersE,
    accountE, _sizesE, storageE, _ledgerE, _clearE, sizeE, _boundE, cursorE, _rest⟩ :=
    flush_default_ready (ob := pb) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  let updated : DeflateState := { emitted with block_start := emitted.strstart.toUInt64.toInt64 }
  obtain ⟨updateRun, goodU, treesU, buffersU, _sizesU, storageU⟩ :=
    flush_block_start_engine (ob := pb) goodE treesE buffersE
  have privateFrame := (storageE.trans storageU).pending_private_frame trees.base.pbuf
  have outputSame := private_frame_raw_output_same good buffers pointer privateFrame
  have getPrepared : (setD ready ds updated).bytes ob = some before := outputSame.1.trans getBefore
  have nextOut : ze.next_out = z.next_out := by rw [accountE.2.2.2.2.2.1, advance_zero]
  have pointerE : ze.next_out = .ref (.blk ob) oo := nextOut.trans pointer
  have roomU : 8 * updated.pending.toNat + updated.bi_valid.toInt.toNat ≤ 8 * outputBuf.size := by
    rw [sizeE]
    have high := treesE.run.bi_hi
    have low := treesE.run.bi_lo
    change 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 524288
    omega
  obtain ⟨amount, outputHeap, outputZ, result, _written, _remaining, flushRun, goodA, _buffersA, accountA, _restA⟩ :=
    flush_pending_raw_bits goodU treesU buffersU pointerE cursorE roomU
  have macroRun : FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), outputHeap) := by
    have streamRead : rd (some (.tab ds)) (·.strm) (setD ready ds updated) =
        .ok (some r, setD ready ds updated) := by
      simp only [rdD_eq, setD_dstates_same]
      rw [show updated.strm = some r from goodE.live.back]
    rw [flush_block_only_arguments_source, bind_app, arguments]
    simp only [bind_app, encodeRun, updateRun]
    change (rd (some (.tab ds)) (·.strm) >>= fun strm => flush_pending strm)
      (setD ready ds updated) = .ok ((), outputHeap)
    rw [bind_app, streamRead]
    exact flushRun
  have heaps := (Prod.mk.inj (Except.ok.inj (macroRun.symm.trans run))).2
  have getA := goodA.live.hz
  rw [heaps] at getA
  have streamEq : outputZ = z' := Option.some.inj (getA.symm.trans live)
  have totalAccount : StreamAccounting z z' 0 amount := by
    simpa only [streamEq, Nat.zero_add] using stream_accounting_trans accountE accountA
  have count : amount = produced := (stream_accounting_counts_unique totalAccount account).2
  rw [← heaps, ← count]
  exact flush_pending_run_output_interval goodU treesU buffersU pointerE cursorE roomU flushRun goodA.live.hz accountA getPrepared

/-- Complete computed block publication has the exact public caller byte-region frame. -/
theorem flush_macro_run_buffer_frame {h after : Heap} {r : ZStreamRef}
    {ds pb ob oo w origin base produced : Nat} {z z' : ZStream} {d : DeflateState}
    {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
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
    BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, produced⟩] := by
  obtain ⟨_amount, other, _ze, _de, _written, _remaining, _kind, _body, _padding,
      tested, _goodA, _buffersA, _accountA, sizes, storage, _rest⟩ :=
    flush_block_only_publish good trees buffers positive pointer cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [eq] at sizes storage
  obtain ⟨before, getBefore, _writable, _bound, _outside⟩ := caller_raw_output good buffers pointer
  obtain ⟨next, getNext, size, untouched⟩ := flush_macro_run_output_interval good trees buffers positive pointer
    cursor memory pending bits ledger clear trace win get range balance accounted view last run live account getBefore
  have frame : Frame h after (fun b => (StreamRoot r b ∨ DeflateOwned ds d b) ∨ b = ob) := by
    apply full_frame_weaken (storage.private_frame trees.base.pbuf)
    intro b changed
    rcases changed with root | owned | output
    · exact Or.inl (Or.inl root)
    · exact Or.inl (Or.inr owned)
    · exact Or.inr output
  have readonly : after.ro ob = h.ro ob := sizes.ro (.blk ob)
  rw [pointer]
  exact raw_buffer_frame_of_interval frame storage.shape good.uniq getBefore getNext readonly size untouched

end Zlib.Deflate.Engine.Proofs
