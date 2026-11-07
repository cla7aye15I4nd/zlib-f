import ZlibF.Proof.«deflate.c.engine.fixed-block»

/-! # Complete fixed-branch output and terminal raw-stream validity -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt fixedTag)
set_option autoImplicit false

/-- The actual fixed branch and common tail, followed by flush_pending,
preserve exact bytes plus PendingBits for arbitrary raw caller capacity.
Every publishing room condition follows from the payload bound. The
independent Body relation and the source's terminal padding are retained.
This is a selected branch of _tr_flush_block, not a selection contract. -/
theorem fixed_block_publish_frame {h : Heap} {r : ZStreamRef} {ds pb ob oo base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (trace : Trace input base xs) (last : Bool) :
    ∃ produced after z' result written remaining payload padding,
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)
          flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BlockOutputFrame d result ∧
      Zlib.Trees.Proofs.Out.InitialFrequencies result.dyn_ltree result.dyn_dtree ∧ result.bi_valid.toInt < 8 ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      (z.avail_out.toNat ≥ 63488 → result.pending.toNat = 0) ∧
      (last = true → result.bi_valid.toInt.toNat = 0) ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ++
        (fixedTag last ++ payload ++ padding) ∧
      ∀ suffix, ZlibF.Spec.Body [] 1 (inputPrefix input base) (payload ++ suffix) suffix
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨ready, emitted, outputBuf, payload, padding, run, goodE, treesE, buffersE, sizesE, storageE,
    ledgerE, frameE, _size, boundE, nonfinalE, cursorE, roomE, finalE, padBound, padNone, outputE, grammar⟩ :=
    fixed_block_ready_frame (ob := ob) good trees buffers cursor memory pending bits count packed valid trace last
  obtain ⟨produced, after, z', result, written, remaining, flush, goodA, buffersA, account, sizesA, storageA,
    copied, left, low, validA, fieldsA, bytes, pendingA, outputA⟩ :=
    flush_pending_raw_bits goodE treesE buffersE pointer cursorE roomE
  have frameA := frameE.output result.pending result.pending_out result.bi_buf result.bi_valid result.bi_used
  rw [← fieldsA] at frameA
  have ledgerA : SymbolLedger outputBuf result [] := by
    rw [fieldsA]
    exact ledgerE.keep rfl rfl rfl rfl
  have frequencies : Zlib.Trees.Proofs.Out.InitialFrequencies result.dyn_ltree result.dyn_dtree := by
    constructor
    · intro k bound
      simpa only [literalFrequency, countKey, Nat.add_zero] using ledgerA.literal k bound
    · intro k bound
      simpa only [distanceFrequency, countKey] using ledgerA.distance k bound
  have final : last = true → result.bi_valid.toInt.toNat = 0 := by
    intro lastTrue
    rw [(finalE lastTrue).1] at validA
    exact validA
  have drained : z.avail_out.toNat ≥ 63488 → result.pending.toNat = 0 := by
    intro capacity
    have total : emitted.pending.toNat + emitted.bi_valid.toInt.toNat / 8 ≤ 63488 := by
      by_cases lastTrue : last = true
      · rw [(finalE lastTrue).1]
        change emitted.pending.toNat + 0 / 8 ≤ 63488
        omega
      · have lastFalse : last = false := by
          cases last
          · rfl
          · exact (lastTrue rfl).elim
        have bound := nonfinalE lastFalse
        have high := treesE.run.bi_hi
        omega
    omega
  refine ⟨produced, after, z', result, written, remaining, payload, padding, ?_, goodA, buffersA,
    account, sizesE.trans sizesA, storageE.trans storageA, frameA, frequencies, low, bytes, pendingA, drained, final,
    padBound, padNone, outputA.trans outputE, grammar⟩
  rw [← M_bind_assoc, bind_app, run]
  exact flush


/-- The earlier complete block publication result retains its exact statement. -/
theorem fixed_block_publish {h : Heap} {r : ZStreamRef} {ds pb ob oo base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (trace : Trace input base xs) (last : Bool) :
    ∃ produced after z' result written remaining payload padding,
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)
          flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ result.bi_valid.toInt < 8 ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      (z.avail_out.toNat ≥ 63488 → result.pending.toNat = 0) ∧
      (last = true → result.bi_valid.toInt.toNat = 0) ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ++
        (fixedTag last ++ payload ++ padding) ∧
      ∀ suffix, ZlibF.Spec.Body [] 1 (inputPrefix input base) (payload ++ suffix) suffix
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨produced, after, z', result, written, remaining, payload, padding, run, goodA, buffersA,
    account, sizes, storage, _fields, _frequencies, low, bytes, pendingA, drained, final,
    padBound, padNone, output, grammar⟩ :=
    fixed_block_publish_frame good trees buffers pointer cursor memory pending bits count packed valid trace last
  exact ⟨produced, after, z', result, written, remaining, payload, padding, run, goodA, buffersA,
    account, sizes, storage, low, bytes, pendingA, drained, final, padBound, padNone, output, grammar⟩

/-- The actual selected final fixed branch produces a complete valid raw
DEFLATE stream when it starts at a byte boundary and the caller can take
the entire default-memory output. The 63488-byte capacity is a derived
conservative internal bound; partial output remains covered above.
The independent Deflate.Valid result includes the real tag, END_BLOCK,
reset and terminal alignment. Tree preparation, branch selection, zlib
wrappers and the public deflate goal are separate obligations. -/
theorem fixed_block_final_valid {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt = 0)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (trace : Trace input 0 xs) (capacity : 63488 ≤ z.avail_out.toNat) :
    ∃ produced after z' result written,
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) 1
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) 1
          flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      result.pending.toNat = 0 ∧ result.bi_valid.toInt.toNat = 0 ∧
      Bytes after z.next_out produced written ∧
      ZlibF.Spec.Deflate.Valid (inputPrefix input (represented xs)) written := by
  obtain ⟨produced, after, z', result, written, remaining, payload, padding, run, goodA, buffersA,
    account, sizes, storage, _low, bytes, pendingA, drained, final, padBound, _padNone, output, grammar⟩ :=
    fixed_block_publish good trees buffers pointer cursor memory pending (by rw [bits]; decide)
      count packed valid trace true
  have pendingZero := drained capacity
  have validZero := final rfl
  have remainingZero := pending_bits_empty pendingA pendingZero validZero
  have before : Zlib.Trees.Proofs.Out.outBits buf d = [] := by
    simp [Zlib.Trees.Proofs.Out.outBits, Zlib.Trees.Proofs.Out.bytesBits, Zlib.Trees.Proofs.Out.natBits, pending, bits]
  rw [remainingZero, List.append_nil, before, List.nil_append] at output
  have encoded : ZlibF.Spec.Blocks [] [] (ZlibF.Spec.bytesToBits written) padding
      (inputPrefix input (represented xs)) := by
    rw [output]
    simpa only [inputPrefix, List.range_zero, List.map_nil, Nat.zero_add] using
      Zlib.Trees.Proofs.Out.fixed_last_grammar grammar padding
  refine ⟨produced, after, z', result, written, ?_, goodA, buffersA, account,
    sizes, storage, pendingZero, validZero, bytes, padding, encoded, ?_⟩
  · exact run
  · rw [Nat.mod_eq_of_lt padBound, List.drop_length]
    rfl

end Zlib.Deflate.Engine.Proofs
