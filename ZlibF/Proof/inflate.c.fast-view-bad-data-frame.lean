import ZlibF.Proof.«inflate.c.fast-view-bad-data-invariant»
import ZlibF.Proof.«inflate.c.fast-writeback-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The exact heap named by a fast diagnostic has no caller-byte effect. -/
theorem badHeap_buffer_frame
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (i : Nat) (regions : List Region) :
    BufferFrame h (badHeap h r zs z s i)
      (fun b => StreamRoot r b ∨ b = zs) regions ∧
    LiveChange h (badHeap h r zs z s i)
      (fun _ => False) (fun _ => False) ∧
    (badHeap h r zs z s i).nalloc = h.nalloc := by
  simpa only [badHeap] using
    fastWriteback_heap_frame hz hs
      { z with msg := .ref (.str i) 0 } { s with mode := BAD } regions

/-- The actual fast diagnostic changes only the live stream and state records.
It does not write any caller byte view, including when the two caller ranges
belong to the same byte object. -/
theorem FastInputPacket.badData_buffer_frame
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (message : String) (literal : message ∈ strTable)
    (regions : List Region) :
    ∃ after,
      C.run (Zlib.Inffast.badData c message) h = .ok ((), after) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) regions ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧
      after.nalloc = h.nalloc := by
  obtain ⟨i, after, run, heapEq, _, _, _, _⟩ :=
    packet.badData_default_state invariant buffers streamPtr statePtr message literal
  have frame := badHeap_buffer_frame invariant.good.live.hz
    invariant.good.live.hs i regions
  refine ⟨after, run, ?_⟩
  simpa only [heapEq] using frame

#print axioms badHeap_buffer_frame
#print axioms FastInputPacket.badData_buffer_frame

end Zlib.Inflate.Proofs
