import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-complete-bytes»
import ZlibF.Proof.«deflate.c.engine.finished-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual pending copy retains completed raw or wrapper meaning,
including short output, zero capacity and advanced pending cursors. -/
theorem flush_pending_foreign_finished_encoding {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {accepted published : List UInt8}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (encoding : FinishedEncoding h d accepted published) :
    ∃ pb produced after z' result written,
      d.pending_buf = .ref (.blk pb) 0 ∧
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ OutputStorage h after r ds pb owner ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧ result.pending.toNat + produced = d.pending.toNat ∧
      result = { d with pending := result.pending, pending_out := result.pending_out } ∧
      (0 < produced → result.pending.toNat = 0 → result.pending_out = result.pending_buf) ∧
      Bytes after z.next_out produced written ∧ FinishedEncoding after result accepted (published ++ written) ∧
      z'.adler = z.adler ∧
      BufferFrame h after (fun x => StreamRoot r x ∨ x=ds) [⟨z.next_out,produced⟩] := by
  obtain ⟨tailBytes, data, meaning⟩ := encoding.data
  obtain ⟨pb, produced, after, z', result, written, remaining, base, run, goodA, buffersA, account,
      storage, amount, count, fields, reset, bytesA, pendingA, splitBytes, adlerA,frameA⟩ :=
    flush_pending_complete_foreign_bytes good buffers pointer encoding.bits data
  have encodingA : FinishedEncoding after result accepted (published ++ written) := by
    refine ⟨by rw [fields]; exact encoding.bits, remaining, pendingA, ?_⟩
    rcases meaning with ⟨wrap, valid⟩ | ⟨wrap, valid⟩
    · exact Or.inl ⟨by rw [fields]; exact wrap, by simpa only [List.append_assoc, splitBytes] using valid⟩
    · exact Or.inr ⟨by rw [fields]; exact wrap, by simpa only [List.append_assoc, splitBytes] using valid⟩
  exact ⟨pb, produced, after, z', result, written, base, run, goodA, buffersA, account, storage,
    amount, count, fields, reset, bytesA, encodingA, adlerA,frameA⟩


end Zlib.Deflate.Engine.Proofs
