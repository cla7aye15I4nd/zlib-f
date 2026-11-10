import ZlibF.Proof.«deflate.c.engine.flush-content-encoding»
import ZlibF.Proof.«deflate.c.engine.flush-end-frontier»

/-! # Real flush encoding cutpoints retain the loop's EOF and publication frontiers -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- With no pending bytes the public pending-bit relation records exactly
its held word bits, independently of the symbol-buffer bytes. -/
theorem pending_bits_zero_value {h : Heap} {d : DeflateState} {before : List Bool}
    (zero : d.pending = 0) (pending : PendingBits h d before) :
    before = Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat := by
  obtain ⟨bytes, data, equal⟩ := pending
  have empty : bytes = [] := by
    rcases data with ⟨_null, _zero, empty⟩ | ⟨_ref, _off, _array, _pointer, _get, _bound, value⟩
    · exact empty
    · rw [zero] at value
      simpa only [UInt64.toNat_zero, List.take_zero] using value
  rw [equal, empty, pending_word_bits]
  rfl

/-- The public readable-range relation fixes the length of its exact byte list. -/
theorem public_bytes_length {h : Heap} {p : BPtr} {n : Nat} {bytes : List UInt8}
    (data : Bytes h p n bytes) : bytes.length = n := by
  rcases data with ⟨_null, rfl, rfl⟩ | ⟨_ref, off, array, _pointer, _get, bound, value⟩
  · rfl
  · rw [value]
    simp only [List.length_take, List.length_drop, Array.length_toList]
    exact Nat.min_eq_left (by omega)

/-- The same actual nonfinal flush retains independent output meaning,
restored content, the EOF hash frontier and the phase for the next loop
iteration. All real block choices and output capacities are covered. -/
theorem flush_nonfinal_end_encoding {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs) (frontier : EndFrontier h d)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) :
    ∃ produced after z' result before written remaining kind body,
      FLUSH_BLOCK (some (.tab ds)) 0 h =
        .ok ((if z'.avail_out == 0 then some need_more else none), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      kind < 3 ∧ ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  obtain ⟨produced, after, z', result, before, written, remaining, kind, body,
    run, content, buffersA, account, clearA, frame, pendingBefore, data, pendingAfter,
    kindBound, output, grammar⟩ :=
    flush_nonfinal_content_encoding boundary buffers positive pointer cursor memory pending bits clear available
  obtain ⟨_count, other, otherZ, otherD, otherRun, otherBoundary, endOther, _buffers,
    _account, _clear, _frame, low, phase⟩ :=
    flush_nonfinal_end_boundary boundary frontier buffers positive pointer cursor memory pending bits clear available
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heaps] at otherBoundary endOther
  have streams : otherZ = z' := Option.some.inj (otherBoundary.good.live.hz.symm.trans content.good.live.hz)
  have states : otherD = result := Option.some.inj (otherBoundary.good.live.hs.symm.trans content.good.live.hs)
  rw [states] at endOther low
  rw [streams, states] at phase
  exact ⟨produced, after, z', result, before, written, remaining, kind, body,
    run, content, endOther, buffersA, account, clearA, frame, low, phase,
    pendingBefore, data, pendingAfter, kindBound, output, grammar⟩

end Zlib.Deflate.Engine.Proofs
