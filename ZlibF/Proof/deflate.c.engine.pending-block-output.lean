import ZlibF.Proof.«deflate.c.engine.pending-bits»

/-! # Complete pending publication after actual block bit generation

This is the raw-output publishing phase: the pending cursor is at its
base, and complete buffered bits fit the real pending allocation.
The existing public caller-buffer domain is unchanged.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- `local void flush_pending(z_streamp strm)`.
For every legal 0..16 buffered-bit count, actual bit flushing and copying
retain the full compressor representation, caller buffers and allocation
ledger. Written caller bytes followed by remaining PendingBits are exactly
the original output bits. Output capacity may be zero or partial. Internal
publishing premises are a base pending cursor, bit room and raw caller
output; they do not replace Goal.deflate or its reachable-state domain. -/
theorem flush_pending_raw_bits {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) :
    ∃ produced after z' result written remaining,
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      produced = min (d.pending.toNat + d.bi_valid.toInt.toNat / 8) z.avail_out.toNat ∧
      result.pending.toNat + produced = d.pending.toNat + d.bi_valid.toInt.toNat / 8 ∧
      result.bi_valid.toInt < 8 ∧ result.bi_valid.toInt.toNat = d.bi_valid.toInt.toNat % 8 ∧
      result = { d with
        pending := result.pending, pending_out := result.pending_out, bi_buf := result.bi_buf,
        bi_valid := result.bi_valid, bi_used := result.bi_used } ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d := by
  obtain ⟨output, outGet, writable, outBound, outside⟩ := caller_raw_output good buffers pointer
  have separate : ob ≠ pb := by
    intro same
    subst ob
    exact outside (Or.inr (Or.inr (Or.inr (Or.inr trees.base.pbuf))))
  obtain ⟨next, prepared, bitRun, goodP, treesP, bitStream, low, size, diff, pendingCount, validCount, sameRun⟩ :=
    flush_pending_prepare good trees cursor room
  let ready := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds prepared
  have outGetP : ready.bytes ob = some output := by
    simpa only [ready, setD_bytes, Zlib.Trees.Proofs.Out.setB, upd_ne _ _ _ _ separate] using outGet
  have writableP : ready.ro ob = false := writable
  have cursorP : prepared.pending_out = prepared.pending_buf := by
    obtain ⟨_, _, _, _, equal⟩ := diff
    rw [equal]
    exact cursor
  obtain ⟨produced, after, z', result, written, remaining, run, goodA, account, sizesA, count, remainingCount,
    fields, bytes, pendingBits, bits, storageA⟩ :=
    flush_pending_low_raw_bits_storage goodP treesP low cursorP pointer outGetP writableP separate outBound
  have sizesP := output_bits_sizes good trees.base.bytes size diff
  have storageP := output_bits_storage (r := r) (ob := ob) (result := prepared) (next := next) good.live.hs trees.base.bytes
  have resultFields : result = { d with
      pending := result.pending, pending_out := result.pending_out, bi_buf := result.bi_buf,
      bi_valid := result.bi_valid, bi_used := result.bi_used } := by
    obtain ⟨p, a, v, u, preparedEq⟩ := diff
    rw [fields, preparedEq]
  have ownedKeys : ∀ b, DeflateOwned ds result b ↔ DeflateOwned ds d b := by
    intro b
    rw [resultFields]
    rfl
  have owned : ∀ b, StreamOwned after r b ↔ StreamOwned h r b := by
    intro b
    rw [stream_owned_deflate goodA, stream_owned_deflate good, ownedKeys]
  have sizes := sizesP.trans sizesA
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned account
  have validSame : result.bi_valid = prepared.bi_valid := congrArg (·.bi_valid) fields
  refine ⟨produced, after, z', result, written, remaining, sameRun.trans run, goodA, buffersA, account,
    sizes, storageP.trans storageA, ?_, by omega, ?_, ?_, resultFields, bytes, pendingBits, bits.trans bitStream⟩
  · rw [pendingCount] at count
    exact count
  · rw [validSame]
    exact low
  · rw [validSame]
    exact validCount

end Zlib.Deflate.Engine.Proofs
