import ZlibF.Proof.«deflate.c.engine.block-prepare»
import ZlibF.Proof.«deflate.c.engine.fixed-block»

/-! # Complete source execution when the real byte costs select a fixed block -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt fixedTag)
set_option autoImplicit false

/-- The actual source dispatches to the fixed encoder when its computed
rounded costs prefer static coding and the earlier stored branch is false.
Preparation is executed, including unknown hint detection and all builders.
This equation retains the computed state; it assumes no callee contract. -/
theorem flush_fixed_dispatch {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d prepared : DeflateState} {mb : Int32}
    (good : DGood h r ds z d) (positive : 0 < d.level.toInt)
    (run : blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared))
    (after : DGood (setD (r.put h z') ds prepared) r ds z' prepared)
    (source : BPtr) (stored : UInt64) (last : Int32)
    (prefer : ((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3))
    (avoid : ¬ (stored + (4 : UInt64) ≤ ((prepared.static_len + 3 + 7) >>> 3) ∧ source != .null)) :
    Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored last h =
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) last
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) last) (setD (r.put h z') ds prepared) := by
  rw [flush_block_prepare_source]
  simp only [bind_app, pure_app, Zlib.Trees.Proofs.Out.rd_run good.live.hs,
    positive, ite_true, run, Zlib.Trees.Proofs.Out.rd_run after.live.hs,
    prefer, true_or, avoid, ite_false, BEq.rfl]

/-- `void ZLIB_INTERNAL _tr_flush_block(deflate_state *s, charf *buf, ulg stored_len, int last)`.
Actual positive-level preparation determines its byte costs. If those costs
select the fixed branch, the complete function executes safely and emits
independently decodable symbols for the exact logical input. Both last flags
are included. Stored and dynamic choices remain separate obligations; fixed
coding is not forced or substituted for the default strategy. -/
theorem flush_fixed_prepared {h : Heap} {r : ZStreamRef} {ds pb ob base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (trace : Trace input base xs)
    (source : BPtr) (stored : UInt64) (last : Bool) :
    ∃ (mb : Int32) (z' : ZStream) (prepared : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) ∧
      TreePreparationFrame d prepared ∧ z' = { z with data_type := z'.data_type } ∧
      ( ((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) →
        ¬ (stored + (4 : UInt64) ≤ ((prepared.static_len + 3 + 7) >>> 3) ∧ source != .null) →
        ∃ after result next payload padding,
          Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored (if last then 1 else 0) h = .ok ((), after) ∧
          DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
          StreamAccounting z z' 0 0 ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
          SymbolLedger next result [] ∧ BlockOutputFrame prepared result ∧
          next.size = 65536 ∧ result.pending.toNat ≤ 63488 ∧ result.pending_out = result.pending_buf ∧
          (last = true → result.bi_valid.toInt = 0 ∧ result.bi_buf = 0) ∧
          padding.length < 8 ∧ (last = false → padding = []) ∧
          Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
            (fixedTag last ++ payload ++ padding) ∧
          ∀ suffix, ZlibF.Spec.Body [] 1 (inputPrefix input base) (payload ++ suffix) suffix
            (inputPrefix input (base + represented xs)) ) := by
  obtain ⟨mb, z', prepared, prepare, goodP, treesP, buffersP, account, sizesP, storageP,
    _lower, _upper, _guards, fields, outputP, fieldsZ⟩ :=
    block_prepare_engine_frame (ob := ob) good trees buffers
  refine ⟨mb, z', prepared, prepare, fields, fieldsZ, ?_⟩
  intro prefer avoid
  have record := fields
  unfold TreePreparationFrame at record
  obtain ⟨after, result, next, payload, padding, run, goodA, treesA, buffersA, sizesA, storageA,
    ledger, frame, size, bound, _nonfinal, cursorA, _room, final, padBound, padNone, output, grammar⟩ :=
    fixed_block_ready_frame (ob := ob) goodP treesP buffersP
      (by rw [record]; exact cursor) (by rw [record]; exact memory)
      (by rw [record]; exact pending) (by rw [record]; exact bits)
      (by rw [record]; exact count) (by rw [record]; exact packed) valid trace last
  have sourceRun := flush_fixed_dispatch good positive prepare goodP source stored (if last then 1 else 0) prefer avoid
  rw [outputP] at output
  exact ⟨after, result, next, payload, padding, sourceRun.trans run, goodA, treesA, buffersA,
    account, sizesP.trans sizesA, storageP.trans storageA, ledger, frame, size, bound,
    cursorA, final, padBound, padNone, output, grammar⟩

/-- The full actual _tr_flush_block, including all preparation and the
computed fixed choice, followed by actual pending publication produces an
independent complete raw stream for a final block at a byte boundary.
This is conditional on the actual returned costs selecting fixed coding;
stored/dynamic cases and public strategy completion remain separate. -/
theorem flush_fixed_final_valid {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt = 0)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (trace : Trace input 0 xs)
    (pointer : z.next_out = .ref (.blk ob) oo) (capacity : 63488 ≤ z.avail_out.toNat)
    (source : BPtr) (stored : UInt64) :
    ∃ (mb : Int32) (z' : ZStream) (prepared : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) ∧
      TreePreparationFrame d prepared ∧
      ( ((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) →
        ¬ (stored + (4 : UInt64) ≤ ((prepared.static_len + 3 + 7) >>> 3) ∧ source != .null) →
        ∃ produced after zf result written,
          (do Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored 1
              flush_pending (some r)) h = .ok ((), after) ∧
          DGood after r ds zf result ∧ StreamBuffers after r ∧ StreamAccounting z zf 0 produced ∧
          ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
          result.pending.toNat = 0 ∧ result.bi_valid.toInt.toNat = 0 ∧ Bytes after z.next_out produced written ∧
          ZlibF.Spec.Deflate.Valid (inputPrefix input (represented xs)) written ) := by
  obtain ⟨mb, z', prepared, prepare, fields, fieldsZ, selected⟩ :=
    flush_fixed_prepared (ob := ob) good trees buffers positive cursor memory pending (by rw [bits]; decide)
      count packed valid trace source stored true
  refine ⟨mb, z', prepared, prepare, fields, ?_⟩
  intro prefer avoid
  obtain ⟨ready, emitted, outputBuf, payload, padding, run, goodE, treesE, buffersE, accountE, sizesE, storageE,
    _ledger, _frame, size, bound, cursorE, finalE, padBound, _padNone, outputE, grammar⟩ := selected prefer avoid
  have pointerE : z'.next_out = .ref (.blk ob) oo := by rw [fieldsZ]; exact pointer
  have validE : emitted.bi_valid.toInt.toNat = 0 := by rw [(finalE rfl).1]; rfl
  have room : 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 8 * outputBuf.size := by
    rw [size, validE]
    omega
  obtain ⟨produced, after, zf, result, written, remaining, flush, goodA, buffersA, accountA,
    sizesA, storageA, amount, left, _low, validA, _fields, bytes, pendingA, outputA⟩ :=
    flush_pending_raw_bits goodE treesE buffersE pointerE cursorE room
  have available : 63488 ≤ z'.avail_out.toNat := by rw [fieldsZ]; exact capacity
  have drained : result.pending.toNat = 0 := by
    rw [validE] at amount left
    change produced = min emitted.pending.toNat z'.avail_out.toNat at amount
    change result.pending.toNat + produced = emitted.pending.toNat at left
    rw [Nat.min_eq_left (by omega)] at amount
    omega
  have validZero : result.bi_valid.toInt.toNat = 0 := by rw [validE] at validA; exact validA
  have remainingZero := pending_bits_empty pendingA drained validZero
  have before : Zlib.Trees.Proofs.Out.outBits buf d = [] := by
    simp [Zlib.Trees.Proofs.Out.outBits, Zlib.Trees.Proofs.Out.bytesBits, Zlib.Trees.Proofs.Out.natBits, pending, bits]
  have encoded := outputA.trans outputE
  rw [remainingZero, List.append_nil, before, List.nil_append] at encoded
  have block : ZlibF.Spec.Blocks [] [] (ZlibF.Spec.bytesToBits written) padding
      (inputPrefix input (represented xs)) := by
    rw [encoded]
    simpa only [inputPrefix, List.range_zero, List.map_nil, Nat.zero_add] using
      Zlib.Trees.Proofs.Out.fixed_last_grammar grammar padding
  change Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored 1 h = .ok ((), ready) at run
  have complete : (do
        Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored 1
        flush_pending (some r)) h = .ok ((), after) := by
    rw [bind_app, run]
    exact flush
  have account : StreamAccounting z zf 0 produced := by
    simpa only [Nat.zero_add] using stream_accounting_trans accountE accountA
  have bytesA : Bytes after z.next_out produced written := by rw [fieldsZ] at bytes; exact bytes
  exact ⟨produced, after, zf, result, written, complete, goodA, buffersA, account,
    sizesE.trans sizesA, storageE.trans storageA, drained, validZero, bytesA,
    padding, block, by rw [Nat.mod_eq_of_lt padBound, List.drop_length]; rfl⟩

end Zlib.Deflate.Engine.Proofs
