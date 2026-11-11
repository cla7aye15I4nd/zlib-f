import ZlibF.Proof.«inflate.c.default-record-resources»
import ZlibF.Proof.«inflate.c.default-public-frame»
import ZlibF.Proof.«inflate.c.old-owned»
import ZlibF.Proof.«inflate.c.default-setdict-resources»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual default inflate call returns from the original
public buffers with both initialized origins and the exact public ledger. -/
theorem inflate_default_origin_public_sequence_contract
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (before : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ rc after stream state, C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r (.inflate (some r) flush) b)
        (StreamWriteRegions h r (.inflate (some r) flush)) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨rc, after, stream, state, _used, _output, run, current, finalAllocator,
    accounting, _bytes, frame, _window, _retained, ledger⟩ :=
    inflate_default_origin_old_owned_resources before allocator buffers flush
  exact ⟨rc, after, stream, state, run, current, finalAllocator,
    inflate_default_public_buffer_frame before flush frame accounting.2.1, ledger⟩


#print axioms inflate_default_origin_public_sequence_contract
end Zlib.Inflate.Proofs
