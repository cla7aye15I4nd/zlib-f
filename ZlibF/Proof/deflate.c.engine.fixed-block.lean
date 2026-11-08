import ZlibF.Proof.«deflate.c.engine.fixed-header»
import ZlibF.Proof.«deflate.c.engine.block-windup»

/-! # The complete actual fixed branch and common block tail

Tag arithmetic, payload, frequency reset and optional final alignment
execute in source order. The whole _tr_flush_block source equality
retains the still separate tree preparation and branch selection.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt fixedTag)
set_option autoImplicit false

/-- `void ZLIB_INTERNAL _tr_flush_block(deflate_state *s, charf *buf, ulg stored_len, int last)`
(selected fixed branch and common tail). Actual tag, complete payload,
reset and final alignment preserve the engine and restore an empty
symbol ledger. All output room is derived from default-memory geometry.
The payload has the independent fixed Body relation for the exact input
trace. Both final/non-final flags are covered. This supporting branch
result does not assume or prove the earlier builders and branch selection. -/
theorem fixed_block_ready_frame {h : Heap} {r : ZStreamRef} {ds pb ob base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (trace : Trace input base xs) (last : Bool) :
    ∃ after result next payload padding,
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ SymbolLedger next result [] ∧ BlockOutputFrame d result ∧
      next.size = 65536 ∧ result.pending.toNat ≤ 63488 ∧
      (last = false → result.pending.toNat ≤ 63486) ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size ∧
      (last = true → result.bi_valid.toInt = 0 ∧ result.bi_buf = 0) ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (fixedTag last ++ payload ++ padding) ∧
      ∀ suffix, ZlibF.Spec.Body [] 1 (inputPrefix input base) (payload ++ suffix) suffix
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨tagged, headerRun, goodH, treesH, buffersH, sizesH, storageH, diffH,
    pendingH, bitsH, cursorH, outputH⟩ := fixed_header_engine (ob := ob) good trees buffers cursor pending bits last
  obtain ⟨_p, _a, _v, _u, fieldsH⟩ := diffH
  obtain ⟨emittedBuf, emitted, payloadRun, goodE, treesE, buffersE, sizesE, storageE,
    fieldsE, sizeE, pendingE, cursorE, roomE, outputE⟩ :=
    fixed_payload_ready_fields (ob := ob) goodH treesH buffersH cursorH
      (by rw [fieldsH]; exact memory) pendingH bitsH
      (by rw [fieldsH]; exact count) (by rw [fieldsH]; exact packed) valid
  let payload := xs.flatMap (fun s => Zlib.Trees.Proofs.Out.payloadSymBits
      Zlib.Trees.Proofs.fixedLiteralWords Zlib.Trees.Proofs.fixedDistanceWords (s.distance, s.value)) ++
    Zlib.Trees.Proofs.Out.codeBits Zlib.Trees.Proofs.fixedLiteralWords 256
  have emittedBits : Zlib.Trees.Proofs.Out.outBits emittedBuf emitted =
      Zlib.Trees.Proofs.Out.outBits buf d ++ (fixedTag last ++ payload) := by
    rw [outputE, outputH, List.append_assoc]
  obtain ⟨a1, a2, a3, reset, resetRun, goodR, treesR, buffersR, sizesR, storageR, resetFields, ledgerR, resetBits⟩ :=
    init_block_engine (ob := ob) goodE treesE buffersE
  have frameR : BlockOutputFrame d reset := by
    obtain ⟨_, _, _, _, emittedFields⟩ := fieldsE
    unfold BlockOutputFrame
    rw [resetFields, emittedFields, fieldsH]
    rfl
  have pendingR : reset.pending.toNat ≤ 63486 := by rw [resetFields]; exact pendingE
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursorE
  have bitsR : Zlib.Trees.Proofs.Out.outBits emittedBuf reset =
      Zlib.Trees.Proofs.Out.outBits buf d ++ (fixedTag last ++ payload) := resetBits.trans emittedBits
  have highR := treesR.run.bi_hi
  have roomR : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    rw [sizeE]
    omega
  have sizes := (sizesH.trans sizesE).trans sizesR
  have storage := (storageH.trans storageE).trans storageR
  have grammar : ∀ suffix, ZlibF.Spec.Body [] 1 (inputPrefix input base) (payload ++ suffix) suffix
      (inputPrefix input (base + represented xs)) := by
    intro suffix
    exact ZlibF.Spec.Body.fixed (Zlib.Trees.Proofs.Out.fixed_payload_grammar trace suffix)
  cases last with
  | false =>
    change Zlib.Trees.Proofs.fixedBlockHeader (some (.tab ds)) 0 h = .ok ((), setD h ds tagged) at headerRun
    refine ⟨_, reset, emittedBuf, payload, [], ?_, goodR, treesR, buffersR, sizes, storage, ledgerR, frameR,
      sizeE, by omega, (by intro _; exact pendingR), cursorR, roomR, by simp, by decide, by simp, ?_, grammar⟩
    · unfold Zlib.Trees.Proofs.fixedBlockPayload Zlib.Trees.Proofs.flushBlockTail
      simp only [bind_app, headerRun, payloadRun, resetRun,
        show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ite_false, pure_app]
    · simpa only [List.append_nil] using bitsR
  | true =>
    change Zlib.Trees.Proofs.fixedBlockHeader (some (.tab ds)) 1 h = .ok ((), setD h ds tagged) at headerRun
    obtain ⟨next, result, windupRun, goodA, treesA, buffersA, sizesA, storageA, fieldsA,
      sizeA, pendingA, zeroA, wordA, cursorA, outputA⟩ :=
      windup_engine (ob := ob) goodR treesR buffersR cursorR roomR
    let padding := List.replicate ((8 - reset.bi_valid.toInt.toNat % 8) % 8) false
    have size : next.size = 65536 := sizeA.trans sizeE
    have upper : result.pending.toNat ≤ 63488 := by omega
    have room : 8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size := by
      rw [zeroA, size]
      change 8 * result.pending.toNat ≤ 524288
      omega
    refine ⟨_, result, next, payload, padding, ?_, goodA, treesA, buffersA, sizes.trans sizesA,
      storage.trans storageA, empty_ledger_bits ledgerR fieldsA, frameR.bits fieldsA, size, upper, (by simp), cursorA, room,
      by intro _; exact ⟨zeroA, wordA⟩, ?_, by simp, ?_, grammar⟩
    · unfold Zlib.Trees.Proofs.fixedBlockPayload Zlib.Trees.Proofs.flushBlockTail
      simp only [bind_app, headerRun, payloadRun, resetRun,
        show ((1 : Int32) != 0) = true from rfl, ite_true, windupRun]
    · simpa only [padding, List.length_replicate] using Nat.mod_lt (8 - reset.bi_valid.toInt.toNat % 8) (by decide : 0 < 8)
    · rw [outputA, bitsR]
      simp only [List.append_assoc, padding]

/-- The earlier byte-bound result retains its exact statement. -/
theorem fixed_block_ready_bounds {h : Heap} {r : ZStreamRef} {ds pb ob base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (trace : Trace input base xs) (last : Bool) :
    ∃ after result next payload padding,
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ SymbolLedger next result [] ∧
      next.size = 65536 ∧ result.pending.toNat ≤ 63488 ∧
      (last = false → result.pending.toNat ≤ 63486) ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size ∧
      (last = true → result.bi_valid.toInt = 0 ∧ result.bi_buf = 0) ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (fixedTag last ++ payload ++ padding) ∧
      ∀ suffix, ZlibF.Spec.Body [] 1 (inputPrefix input base) (payload ++ suffix) suffix
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨after, result, next, payload, padding, run, goodA, treesA, buffersA, sizes, storage,
    ledger, _fields, size, bound, nonfinal, cursorA, room, final, padBound, padNone, output, grammar⟩ :=
    fixed_block_ready_frame (ob := ob) good trees buffers cursor memory pending bits count packed valid trace last
  exact ⟨after, result, next, payload, padding, run, goodA, treesA, buffersA, sizes, storage,
    ledger, size, bound, nonfinal, cursorA, room, final, padBound, padNone, output, grammar⟩

/-- The earlier fixed-branch result retains its exact statement. -/
theorem fixed_block_ready {h : Heap} {r : ZStreamRef} {ds pb ob base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (trace : Trace input base xs) (last : Bool) :
    ∃ after result next payload padding,
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ SymbolLedger next result [] ∧
      next.size = 65536 ∧ result.pending.toNat ≤ 63488 ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size ∧
      (last = true → result.bi_valid.toInt = 0 ∧ result.bi_buf = 0) ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (fixedTag last ++ payload ++ padding) ∧
      ∀ suffix, ZlibF.Spec.Body [] 1 (inputPrefix input base) (payload ++ suffix) suffix
        (inputPrefix input (base + represented xs)) := by
  obtain ⟨after, result, next, payload, padding, run, goodA, treesA, buffersA, sizes, storage, ledger,
    size, bound, _nonfinal, cursorA, room, final, padBound, padNone, output, grammar⟩ :=
    fixed_block_ready_bounds (ob := ob) good trees buffers cursor memory pending bits count packed valid trace last
  exact ⟨after, result, next, payload, padding, run, goodA, treesA, buffersA, sizes, storage, ledger,
    size, bound, cursorA, room, final, padBound, padNone, output, grammar⟩

end Zlib.Deflate.Engine.Proofs
