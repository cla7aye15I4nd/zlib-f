import ZlibF.Proof.«deflate.c.engine.generic-foreign-zlib-trailer»
import ZlibF.Proof.«deflate.c.engine.common-header-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- Independently established raw decoding and accepted-input checksum compose
with the same real foreign-output trailer execution. These are mathematical
history facts, not an assumed contract or success of a translated callee. -/
theorem foreign_zlib_trailer_publish_valid {h : Heap} {r : ZStreamRef} {ds pb owner oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {accepted raw : List UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (wrap : d.wrap = 1)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0)
    (checksum : z.adler = (ZlibF.Spec.adler32 accepted).toUInt64)
    (rawMeaning : ZlibF.Spec.Deflate.Valid accepted raw) :
    ∃ produced after z' result written tailBytes,
      publicFinishTail (some r) (some (.tab ds)) Z_FINISH h =
        .ok ((if result.pending != 0 then Z_OK else Z_STREAM_END),after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      result.wrap = -1 ∧ result.bi_valid.toInt = 0 ∧
      Bytes after z.next_out produced written ∧ Bytes after result.pending_out result.pending.toNat tailBytes ∧
      written ++ tailBytes = ZlibF.Spec.be32 (ZlibF.Spec.adler32 accepted).toNat ∧
      z'.adler = (ZlibF.Spec.adler32 accepted).toUInt64 ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] ∧
      ZlibF.Spec.Zlib.Valid accepted (levelHeaderPrefix d.level ++ raw ++ written ++ tailBytes) ∧
      (result.pending = 0 → ZlibF.Spec.Zlib.Valid accepted (levelHeaderPrefix d.level ++ raw ++ written)) := by
  obtain ⟨produced,after,z',result,written,_remaining,run,goodA,buffersA,accountA,
      _sizes,_amount,_left,wrapA,bitsA,_fields,bytesA,_pending,_wire,
      adlerA,_input,_output,allocA,frontierA,frameA,tailBytes,tailData,splitBytes,completed⟩ :=
    foreign_zlib_trailer_publish_encoding good trees buffers pointer wrap pending cursor bits
  have trailer : ZlibF.Spec.be32 z.adler.toNat = ZlibF.Spec.be32 (ZlibF.Spec.adler32 accepted).toNat := by
    simp only [checksum,UInt32.toNat_toUInt64]
  have valid : ZlibF.Spec.Zlib.Valid accepted
      (levelHeaderPrefix d.level ++ raw ++ ZlibF.Spec.be32 (ZlibF.Spec.adler32 accepted).toNat) := by
    have defaultValid := ZlibF.Math.DeflateEncoding.raw_valid_zlib_grammar rawMeaning
    have replaced := level_header_rewrap (input := accepted)
      (payload := raw ++ ZlibF.Spec.be32 (ZlibF.Spec.adler32 accepted).toNat) d.level
      (by simpa only [List.append_assoc] using defaultValid)
    simpa only [levelHeaderPrefix,List.append_assoc] using replaced
  refine ⟨produced,after,z',result,written,tailBytes,run,goodA,buffersA,accountA,wrapA,bitsA,
    bytesA,tailData,splitBytes.trans trailer,adlerA.trans checksum,allocA,frontierA,frameA,?_,?_⟩
  · simpa only [List.append_assoc,splitBytes,trailer] using valid
  · intro empty
    rw [completed empty,trailer]
    exact valid

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.foreign_zlib_trailer_publish_valid
