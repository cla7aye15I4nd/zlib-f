import ZlibF.Proof.«deflate.c.engine.dynamic-block»
import ZlibF.Math.DeflateDynamicBlock

/-! # Actual dynamic output publication and independent terminal raw-stream validity -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (dynamicTag)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual dynamic construction, output, reset and optional alignment,
followed by actual pending publication, retain exact bytes plus PendingBits
for arbitrary caller capacity. No whole-output-capacity restriction is
needed. The complete independent body and real terminal padding remain.
Actual flush branch selection and the public engine are still separate. -/
theorem dynamic_block_publish {h : Heap} {r : ZStreamRef} {ds pb ob oo base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs) (last : Bool) :
    ∃ produced after z' result written remaining body padding,
      (do dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)
          flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BlockInit.BlockClear result ∧
      Zlib.Trees.Proofs.Out.InitialFrequencies result.dyn_ltree result.dyn_dtree ∧ result.bi_valid.toInt < 8 ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      (63488 + (if last then 0 else 2) ≤ z.avail_out.toNat → result.pending.toNat = 0) ∧
      (last = true → result.bi_valid.toInt.toNat = 0) ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ++
        (dynamicTag last ++ body ++ padding) ∧
      ∀ suffix, ZlibF.Spec.Body [] 2 (inputPrefix input base) (body ++ suffix) suffix
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨readyHeap, emitted, outputBuf, body, padding, run, goodE, treesE, buffersE, sizesE, storageE,
    ledgerE, clearE, _sizeE, boundE, cursorE, roomE, finalE, padBound, padNone, outputE, grammar⟩ :=
    dynamic_prepared_block_ready (ob := ob) good trees buffers cursor memory pending bits ledger clear trace last
  obtain ⟨produced, after, z', result, written, remaining, flush, goodA, buffersA, account, sizesA, storageA,
    copied, left, low, validA, fieldsA, bytes, pendingA, outputA⟩ :=
    flush_pending_raw_bits goodE treesE buffersE pointer cursorE roomE
  have ledgerA : SymbolLedger outputBuf result [] := by
    rw [fieldsA]
    exact ledgerE.keep rfl rfl rfl rfl
  have clearA : BlockInit.BlockClear result := by
    rw [fieldsA]
    exact ⟨clearE.bl, clearE.opt, clearE.fixed⟩
  have frequencies : Zlib.Trees.Proofs.Out.InitialFrequencies result.dyn_ltree result.dyn_dtree := by
    constructor
    · intro k bound
      simpa only [literalFrequency, countKey, Nat.add_zero] using ledgerA.literal k bound
    · intro k bound
      simpa only [distanceFrequency, countKey] using ledgerA.distance k bound
  have final : last = true → result.bi_valid.toInt.toNat = 0 := by
    intro flag
    rw [(finalE flag).1] at validA
    exact validA
  have drained : 63488 + (if last then 0 else 2) ≤ z.avail_out.toNat → result.pending.toNat = 0 := by
    intro capacity
    by_cases flag : last = true
    · have total : emitted.pending.toNat + emitted.bi_valid.toInt.toNat / 8 ≤ 63488 := by
        rw [(finalE flag).1]
        change emitted.pending.toNat + 0 / 8 ≤ 63488
        omega
      simp [flag] at capacity
      omega
    · have total : emitted.pending.toNat + emitted.bi_valid.toInt.toNat / 8 ≤ 63490 := by
        have high := treesE.run.bi_hi
        omega
      simp [flag] at capacity
      omega
  refine ⟨produced, after, z', result, written, remaining, body, padding, ?_, goodA, buffersA,
    account, sizesE.trans sizesA, storageE.trans storageA, clearA, frequencies, low, bytes, pendingA,
    drained, final, padBound, padNone, outputA.trans outputE, grammar⟩
  rw [← M_bind_assoc, bind_app, run]
  exact flush

/-- Starting at a byte boundary, the actual constructed final dynamic
fragment publishes a complete valid raw DEFLATE stream. The derived 63488
byte bound suffices for full output; arbitrary output capacity is covered
above. This is an internal execution result, not the public deflate goal. -/
theorem dynamic_block_final_valid {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt = 0)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input 0 xs)
    (capacity : 63488 ≤ z.avail_out.toNat) :
    ∃ produced after z' result written,
      (do dynamicPreparedPayload (some (.tab ds)) 1
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) 1
          flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BlockInit.BlockClear result ∧
      result.pending.toNat = 0 ∧ result.bi_valid.toInt.toNat = 0 ∧ Bytes after z.next_out produced written ∧
      ZlibF.Spec.Deflate.Valid (inputPrefix input (represented xs)) written := by
  obtain ⟨produced, after, z', result, written, remaining, body, padding, run, goodA, buffersA,
    account, sizes, storage, clearA, _frequencies, _low, bytes, pendingA, drained, final,
    padBound, _padNone, output, grammar⟩ :=
    dynamic_block_publish good trees buffers pointer cursor memory pending (by rw [bits]; decide +kernel)
      ledger clear trace true
  have pendingZero := drained capacity
  have validZero := final rfl
  have remainingZero := pending_bits_empty pendingA pendingZero validZero
  have before : Zlib.Trees.Proofs.Out.outBits buf d = [] := by
    simp [Zlib.Trees.Proofs.Out.outBits, Zlib.Trees.Proofs.Out.bytesBits,
      Zlib.Trees.Proofs.Out.natBits, pending, bits]
  rw [remainingZero, List.append_nil, before, List.nil_append] at output
  have encoded : ZlibF.Spec.Blocks [] [] (ZlibF.Spec.bytesToBits written) padding
      (inputPrefix input (represented xs)) := by
    rw [output]
    simpa only [inputPrefix, List.range_zero, List.map_nil, Nat.zero_add] using
      Zlib.Trees.Proofs.dynamic_last_grammar grammar padding
  refine ⟨produced, after, z', result, written, run, goodA, buffersA, account, sizes, storage,
    clearA, pendingZero, validZero, bytes, padding, encoded, ?_⟩
  rw [Nat.mod_eq_of_lt padBound, List.drop_length]
  rfl

end Zlib.Deflate.Engine.Proofs
