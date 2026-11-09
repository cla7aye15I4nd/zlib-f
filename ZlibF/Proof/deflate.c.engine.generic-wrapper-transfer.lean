import ZlibF.Proof.«deflate.c.engine.generic-wrapper-frames»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A scalar record update preserving depth leaves every public byte slice exact. -/
theorem generic_wrapper_setD_bytes {h : Heap} {ds : Nat} {d result : DeflateState}
    {pointer : BPtr} {n : Nat} {xs : List UInt8}
    (state : h.dstates ds = some d) (depth : result.depth = d.depth)
    (bytes : Bytes h pointer n xs) : Bytes (setD h ds result) pointer n xs := by
  rcases bytes with null | ⟨ref,off,array,ptr,get,bound,value⟩
  · exact Or.inl null
  · exact Or.inr ⟨ref,off,array,ptr,(byte_view_setD_depth state depth ref).trans get,bound,value⟩

/-- Scalar wrap or flush stores retain the exact unconsumed pending bits. -/
theorem generic_wrapper_setD_pending_bits {h : Heap} {ds : Nat} {d result : DeflateState} {remaining : List Bool}
    (state : h.dstates ds = some d) (depth : result.depth = d.depth)
    (pending : result.pending = d.pending) (cursor : result.pending_out = d.pending_out)
    (valid : result.bi_valid = d.bi_valid) (word : result.bi_buf = d.bi_buf)
    (bits : PendingBits h d remaining) : PendingBits (setD h ds result) result remaining := by
  obtain ⟨bytes,read,equal⟩ := bits
  refine ⟨bytes,?_,?_⟩
  · rw [pending,cursor]
    exact generic_wrapper_setD_bytes state depth read
  · simpa only [valid,word] using equal

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.generic_wrapper_setD_bytes
#print axioms Zlib.Deflate.Engine.Proofs.generic_wrapper_setD_pending_bits
