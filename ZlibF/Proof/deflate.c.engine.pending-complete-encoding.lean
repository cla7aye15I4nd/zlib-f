import ZlibF.Proof.«deflate.c.engine.pending-checksum»
import ZlibF.Proof.«deflate.c.engine.input-slices»
import ZlibF.Math.DeflateByteEncoding

/-! # Pending publication partitions the exact completed byte stream -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual pending publication with zero held bits partitions precisely
the old pending bytes into the written prefix and the remaining suffix.
Arbitrary caller capacity and advanced pending cursors are admitted. This
byte equality preserves any independent stream meaning already attached
to the completed output, without assuming a callee contract. -/
theorem flush_pending_complete_bytes {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {before : List UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (bits : d.bi_valid.toInt = 0)
    (pending : Bytes h d.pending_out d.pending.toNat before) :
    ∃ pb produced after z' result written remaining,
      d.pending_buf = .ref (.blk pb) 0 ∧
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ OutputStorage h after r ds pb ob ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧ result.pending.toNat + produced = d.pending.toNat ∧
      result = { d with pending := result.pending, pending_out := result.pending_out } ∧
      (0 < produced → result.pending.toNat = 0 → result.pending_out = result.pending_buf) ∧
      Bytes after z.next_out produced written ∧ Bytes after result.pending_out result.pending.toNat remaining ∧
      written ++ remaining = before ∧ z'.adler = z.adler := by
  have held : PendingBits h d (ZlibF.Spec.bytesToBits before) :=
    ⟨before, pending, by simp only [bits, Int.toNat_zero, List.range_zero, List.map_nil, List.append_nil]⟩
  have low : d.bi_valid.toInt < 8 := by rw [bits]; decide
  obtain ⟨pb, produced, after, z', result, written, remainingBits, base,
      run, goodA, buffersA, account, _sizes, storage, amount, count, _lowA, fields, reset,
      bytesA, pendingA, wire⟩ := flush_pending_resume_raw_bits good buffers pointer low held
  have bitsA : result.bi_valid.toInt = 0 := by rw [fields]; exact bits
  obtain ⟨remaining, data, remainingEq⟩ := pendingA
  have encoded : remainingBits = ZlibF.Spec.bytesToBits remaining := by
    simpa only [bitsA, Int.toNat_zero, List.range_zero, List.map_nil, List.append_nil] using remainingEq
  have splitBytes : written ++ remaining = before := by
    apply ZlibF.Math.DeflateEncoding.encoded_bytes_injective
    simpa only [ZlibF.Spec.bytesToBits, List.flatMap_append, encoded] using wire
  have adlerA := flush_pending_low_run_adler good buffers pointer low run goodA.live.hz account
  exact ⟨pb, produced, after, z', result, written, remaining, base, run, goodA, buffersA, account,
    storage, amount, count, fields, reset, bytesA, data, splitBytes, adlerA⟩

end Zlib.Deflate.Engine.Proofs
