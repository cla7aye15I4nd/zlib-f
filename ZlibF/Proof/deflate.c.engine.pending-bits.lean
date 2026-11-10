import ZlibF.Proof.«deflate.c.engine.output-storage»
import ZlibF.Proof.«deflate.c.engine.public-first»

/-! # Publishing pending bytes preserves their complete bit sequence -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

theorem pending_bits_slice {h : Heap} {d : DeflateState} {pb off : Nat} {buf : Array UInt8}
    (pointer : d.pending_out = .ref (.blk pb) off) (get : h.bytes pb = some buf)
    (bound : off + d.pending.toNat ≤ buf.size) :
    PendingBits h d (ZlibF.Spec.bytesToBits ((buf.toList.drop off).take d.pending.toNat) ++
      Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat) := by
  refine ⟨(buf.toList.drop off).take d.pending.toNat,
    Or.inr ⟨.blk pb, off, buf, pointer, get, bound, rfl⟩, ?_⟩
  rw [pending_word_bits]

theorem pending_bits_base {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h ds d pb buf) (cursor : d.pending_out = d.pending_buf) :
    PendingBits h d (Zlib.Trees.Proofs.Out.outBits buf d) := by
  have bound : d.pending.toNat ≤ buf.size := by have small := trees.base.pending_le; rw [trees.base.psize] at small; exact small
  have result := pending_bits_slice (cursor.trans trees.base.pbuf) trees.base.bytes (by omega)
  simpa only [List.drop_zero, Zlib.Trees.Proofs.Out.outBits, bytes_bits_format buf _ bound] using result

/-- A concrete pending-copy heap has exactly the written byte prefix and
remaining public PendingBits. Concatenating both reproduces its input bits.
The pending cursor may reset only when its remaining count is zero. -/
theorem pending_copy_bits {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (trees : TreesInvAt h ds d pb buf) (cursor : d.pending_out = d.pending_buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (separate : ob ≠ pb)
    (outBound : oo + z.avail_out.toNat ≤ output.size) :
    let n := pendingLen d.pending z.avail_out
    let after := pendingCopyHeap h r ds pb 0 ob oo z d buf output n
    let result := pendingState d (.ref (.blk pb) n.toNat) n
    ∃ written remaining,
      Bytes after z.next_out n.toNat written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d := by
  let n := pendingLen d.pending z.avail_out
  let after := pendingCopyHeap h r ds pb 0 ob oo z d buf output n
  let result := pendingState d (.ref (.blk pb) n.toNat) n
  let off := if d.pending - n.toUInt64 == 0 then 0 else n.toNat
  let remainingBytes := (buf.toList.drop off).take result.pending.toNat
  let tailBits := Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat
  change ∃ written remaining, Bytes after z.next_out n.toNat written ∧ PendingBits after result remaining ∧
    ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d
  have count := (pending_copy_counts d.pending z.avail_out).1
  have length : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  have sourceBound : d.pending.toNat ≤ buf.size := by have small := trees.base.pending_le; rw [trees.base.psize] at small; exact small
  have remainingCount : result.pending.toNat + n.toNat = d.pending.toNat := count
  have getPending : after.bytes pb = some buf := by
    simpa only [after, pendingCopyHeap, setD_bytes, ZStreamRef.put_bytes, upd_ne _ _ _ _ (Ne.symm separate)] using trees.base.bytes
  have getOutput : after.bytes ob = some (copyRange output buf oo 0 n.toNat) := by
    simp [after, pendingCopyHeap]
  have resultPtr : result.pending_out = .ref (.blk pb) off := by
    dsimp only [result, pendingState, off]
    split <;> simp only [trees.base.pbuf]
  have remainingBound : off + result.pending.toNat ≤ buf.size := by
    dsimp only [off]
    split <;> omega
  have kept := pending_bits_slice resultPtr getPending remainingBound
  have copied : ((copyRange output buf oo 0 n.toNat).toList.drop oo).take n.toNat = buf.toList.take n.toNat := by
    rw [← seg_eq_take_drop _ _ _ (by rw [size_copyRange]; omega),
      seg_copyRange output buf oo 0 n.toNat (by omega), seg_eq_take_drop buf 0 n.toNat (by omega), List.drop_zero]
  have slice : remainingBytes = (buf.toList.drop n.toNat).take result.pending.toNat := by
    dsimp only [remainingBytes, off]
    split
    · rename_i empty
      have zero : result.pending.toNat = 0 := by
        have value : d.pending - n.toUInt64 = 0 := beq_iff_eq.mp empty
        simpa only [result, pendingState, value, UInt64.toNat_zero]
      simp only [zero, List.take_zero]
    · rfl
  have splitBytes : buf.toList.take d.pending.toNat = buf.toList.take n.toNat ++ remainingBytes := by
    rw [slice, ← List.take_add, show n.toNat + result.pending.toNat = d.pending.toNat by omega]
  refine ⟨buf.toList.take n.toNat, ZlibF.Spec.bytesToBits remainingBytes ++ tailBits,
    Or.inr ⟨.blk ob, oo, copyRange output buf oo 0 n.toNat, pointer, getOutput,
      by rw [size_copyRange]; omega, copied.symm⟩, kept, ?_⟩
  rw [Zlib.Trees.Proofs.Out.outBits, bytes_bits_format buf _ sourceBound, splitBytes]
  simp only [ZlibF.Spec.bytesToBits, List.flatMap_append, List.append_assoc, tailBits]

/-- `local void flush_pending(z_streamp strm)` (low-bit copy).
This combines actual source execution with DGood, exact public accounting,
byte-range sizes and lossless bit-stream transfer. Arbitrary output
capacity, including zero, is included. The output is a distinct raw object.
-/
theorem flush_pending_low_raw_bits_storage {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (low : d.bi_valid.toInt < 8) (cursor : d.pending_out = d.pending_buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (writable : h.ro ob = false) (separate : ob ≠ pb) (outBound : oo + z.avail_out.toNat ≤ output.size) :
    ∃ produced after z' result written remaining,
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧ result.pending.toNat + produced = d.pending.toNat ∧
      result = { d with pending := result.pending, pending_out := result.pending_out } ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ∧ OutputStorage h after r ds pb ob := by
  let n := pendingLen d.pending z.avail_out
  have count : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  by_cases empty : n = 0
  · have run := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low empty
    have pendingBits := pending_bits_base trees cursor
    refine ⟨0, h, z, d, [], Zlib.Trees.Proofs.Out.outBits buf d, run, good, stream_accounting_zero z,
      ⟨fun _ _ get => ⟨_, get, rfl⟩, fun _ => rfl⟩, ?_, by omega, rfl, ?_, pendingBits, rfl, OutputStorage.refl h r ds pb ob⟩
    · rw [empty] at count
      exact count
    · exact Or.inr ⟨.blk ob, oo, output, pointer, outGet, by omega, by simp⟩
  · have run := flush_pending_low_raw good.live.hz good.live.zst good.live.hs low pointer
      (cursor.trans trees.base.pbuf) outGet trees.base.bytes writable separate outBound
      (by have small := trees.base.pending_le; rw [trees.base.psize] at small; omega) empty
    obtain ⟨written, remaining, bytes, pendingBits, bits⟩ := pending_copy_bits trees cursor pointer separate outBound
    refine ⟨n.toNat, pendingCopyHeap h r ds pb 0 ob oo z d buf output n,
      pendingStream z (.ref (.blk ob) (oo + n.toNat)) n,
      pendingState d (.ref (.blk pb) n.toNat) n, written, remaining, ?_, ?_, pending_copy_accounting pointer,
      pending_copy_sizes n good.live.hs outGet, count, (pending_copy_counts _ _).1, rfl, bytes, pendingBits, bits, pending_copy_storage n good.live.hz good.live.hs outGet⟩
    · simpa only [pendingCopyHeap, Nat.zero_add] using run
    · simpa only [Nat.zero_add] using pending_copy_good (pending := buf) (oo := oo) good trees.base.pbuf (cursor.trans trees.base.pbuf) outGet

/-- The earlier pending-bit transfer result retains its exact statement. -/
theorem flush_pending_low_raw_bits {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf output : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (low : d.bi_valid.toInt < 8) (cursor : d.pending_out = d.pending_buf)
    (pointer : z.next_out = .ref (.blk ob) oo) (outGet : h.bytes ob = some output)
    (writable : h.ro ob = false) (separate : ob ≠ pb) (outBound : oo + z.avail_out.toNat ≤ output.size) :
    ∃ produced after z' result written remaining,
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧ result.pending.toNat + produced = d.pending.toNat ∧
      result = { d with pending := result.pending, pending_out := result.pending_out } ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d := by
  obtain ⟨produced, after, z', result, written, remaining, run, goodA, account, sizes, count,
    pendingCount, fields, bytes, pendingBits, bits, _storage⟩ :=
    flush_pending_low_raw_bits_storage good trees low cursor pointer outGet writable separate outBound
  exact ⟨produced, after, z', result, written, remaining, run, goodA, account, sizes, count,
    pendingCount, fields, bytes, pendingBits, bits⟩

/-- A completely drained state with no residual bits denotes an empty
pending bit sequence in the public relation. -/
theorem pending_bits_empty {h : Heap} {d : DeflateState} {bits : List Bool}
    (pending : PendingBits h d bits) (zero : d.pending.toNat = 0) (valid : d.bi_valid.toInt.toNat = 0) : bits = [] := by
  obtain ⟨bytes, data, equal⟩ := pending
  have empty : bytes = [] := by
    rcases data with ⟨_, _, result⟩ | ⟨ref, off, array, _, _, _, result⟩
    · exact result
    · simpa only [zero, List.take_zero] using result
  rw [equal, empty, valid]
  rfl

end Zlib.Deflate.Engine.Proofs
