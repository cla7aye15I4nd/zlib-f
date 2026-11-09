import ZlibF.Proof.«inflate.c.local-fast-state»

import ZlibF.Proof.«inflate.c.fast-view-geometry»
import ZlibF.Proof.«inflate.c.default-byte-view»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- One actual fast match-copy byte preserves the default reachable-state
invariant, even when caller input and output occupy disjoint slices of one
byte object. The exact heap update is retained for loop composition. -/
theorem FastInputPacket.copy1_local_state
    {cutoff : Nat}
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    {source dest : BRef} {saved output : Array UInt8}
    {sourceOff oo j : Nat}
    (fromPtr : l.from_ = .ref source sourceOff)
    (sourceGet : Space.get h source = some saved)
    (sourceBound : sourceOff < saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (inside : oo ≤ j ∧ j < oo + slow.left.toNat) :
    let updated := output.set! j saved[sourceOff]
    let after := Space.put h dest updated
    let next : Zlib.Inffast.L := { l with
      from_ := .ref source (sourceOff + 1),
      out := .ref dest (j + 1) }
    C.run (Zlib.Inffast.copy1 l) h = .ok (next, after) ∧
      FastInputPacket after slow bs next ∧
      LocalStateJ after cutoff r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      Space.get after dest = some updated ∧
      (∀ k, k < j ∨ j + 1 ≤ k → updated[k]? = output[k]?) ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  have executed := packet.copy1_view buffers.separate left fromPtr
    sourceGet sourceBound outPtr outputPtr outputGet outputWrite
    outputSize inside
  have privateWindow := callerRange_private_window invariant.good
    buffers.output.range outputPtr
  have updatedSize : (output.set! j saved[sourceOff]).size =
      output.size := by simp
  have current := invariant.byte_view_put outputGet outputWrite
    privateWindow _ updatedSize
  have sizes := byte_view_sizes_put outputGet outputWrite _ updatedSize
  have readonly : ∀ ref : BRef,
      Space.ro (Space.put h dest (output.set! j saved[sourceOff])) ref =
        Space.ro h ref := by
    intro ref
    exact byte_view_ro_write h dest _ ref
  have inputRange := callerRange_capacity_local invariant.good current.good
    rfl sizes readonly buffers.input
  have outputRange := callerRange_capacity_local invariant.good current.good
    rfl sizes readonly buffers.output.range
  have nextBuffers : DispatchBuffers
      (Space.put h dest (output.set! j saved[sourceOff]))
      r slow bs :=
    ⟨inputRange,
      ⟨outputRange, buffers.output.nonnull,
        buffers.output.count, buffers.output.produced⟩,
      buffers.separate, executed.2.source⟩
  have outsideByte : ∀ k,
      k < j ∨ j + 1 ≤ k →
        (output.set! j saved[sourceOff])[k]? = output[k]? := by
    intro k outside
    have different : j ≠ k := by omega
    simp [Array.set!, different]
  have outsideRange : ∀ k,
      k < oo ∨ oo + slow.left.toNat ≤ k →
        (output.set! j saved[sourceOff])[k]? = output[k]? := by
    intro k outside
    apply outsideByte
    omega
  exact ⟨executed.1, executed.2, current, nextBuffers,
    sizes, byte_view_get_put outputGet outputWrite _, outsideByte,
    output_view_buffer_frame outputPtr outputGet outputWrite
      updatedSize outsideRange⟩

#print axioms FastInputPacket.copy1_local_state
end Zlib.Inflate.Local
