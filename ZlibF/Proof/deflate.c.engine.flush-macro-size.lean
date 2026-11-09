import ZlibF.Proof.«deflate.c.engine.flush-size»
import ZlibF.Proof.«deflate.c.engine.flush-arguments»

/-! # Tight block costs survive actual pending publication -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt outBits outBits_length)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- The actual macro's written bytes plus its remaining rounded pending
bits fit the same tight block budget for every caller capacity. Argument
arithmetic, all encoding choices, block-start update and publication are
real executions. The observed run and accounting identify that execution;
no abstract encoder contract or capacity sufficiency is assumed. -/
theorem flush_macro_run_byte_count {h after : Heap} {r : ZStreamRef}
    {ds pb ob oo w origin base produced : Nat} {z z' : ZStream} {d result : DeflateState}
    {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (strategy : d.strategy = Z_DEFAULT_STRATEGY)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) (floor : StoredSourceFloor d)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool)
    (run : FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after))
    (live : after.dstates ds = some result) (stream : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) :
    produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
      ((outBits buf d).length + 7) / 8 + represented xs + 5 := by
  have arguments := default_flush_arguments good trees memory ledger win get range balance
  obtain ⟨ze, ready, emitted, outputBuf, _kind, _body, _padding, encodeRun, goodE, treesE, buffersE,
    accountE, _sizesE, _storageE, _ledgerE, _clearE, sizeE, _boundE, cursorE, _rest⟩ :=
    flush_default_ready (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  obtain ⟨costZ, costHeap, costD, costBuf, costRun, costGood, costTrees, cost⟩ :=
    flush_default_byte_count good trees buffers positive cursor memory strategy pending bits ledger clear quality floor
      win get range balance accounted view last
  have sameHeap : costHeap = ready := (Prod.mk.inj (Except.ok.inj (costRun.symm.trans encodeRun))).2
  rw [sameHeap] at costGood costTrees
  have sameState : costD = emitted := Option.some.inj (costGood.live.hs.symm.trans goodE.live.hs)
  have sameBuf : costBuf = outputBuf := Option.some.inj (costTrees.base.bytes.symm.trans treesE.base.bytes)
  rw [sameState, sameBuf] at cost
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
  obtain ⟨amount, outputHeap, outputZ, finalD, _written, _remaining, flushRun, goodA, _buffersA,
    accountA, _sizesA, _storageA, _copied, left, _low, validA, _fieldsA, _bytes, _pendingA, _outputA⟩ :=
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
  rw [heaps] at goodA
  have streams : outputZ = z' := Option.some.inj (goodA.live.hz.symm.trans stream)
  have states : finalD = result := Option.some.inj (goodA.live.hs.symm.trans live)
  have total : StreamAccounting z z' 0 amount := by
    simpa only [streams, Nat.zero_add] using stream_accounting_trans accountE accountA
  have amounts : amount = produced := by
    have first := total.2.2.2.1
    have second := account.2.2.2.1
    omega
  rw [states, amounts] at left
  rw [states] at validA
  change result.pending.toNat + produced = emitted.pending.toNat + emitted.bi_valid.toInt.toNat / 8 at left
  change result.bi_valid.toInt.toNat = emitted.bi_valid.toInt.toNat % 8 at validA
  rw [outBits_length] at cost
  omega

end Zlib.Deflate.Engine.Proofs
