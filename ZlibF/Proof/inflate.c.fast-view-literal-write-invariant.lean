import ZlibF.Proof.«inflate.c.fast-view-dolen-base-leaf-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- One translated literal store and output-pointer increment preserve
the default state and caller buffers, including disjoint slices of one
byte allocation. -/
theorem FastInputPacket.literal_write_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (inside : oo ≤ j ∧ j < oo + slow.left.toNat)
    (value : UInt8) :
    let updated := output.set! j value
    let after := Space.put h dest updated
    let result : Zlib.Inffast.L :=
      { l with out := .ref dest (j + 1) }
    C.run (do
      store8 l.out value
      let out ← l.out.add 1
      pure { l with out }) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      DefaultStateJ after r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      Space.get after dest = some updated ∧
      Space.ro after dest = false ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  let updated := output.set! j value
  let after := Space.put h dest updated
  let result : Zlib.Inffast.L :=
    { l with out := .ref dest (j + 1) }
  have stored := packet.store8_output buffers.separate left
    outputPtr outputGet outputWrite outputSize inside value
  have storeRun : C.run (store8 l.out value) h =
      .ok ((), after) := by
    rw [outPtr]
    exact stored.1
  have storedPacket : FastInputPacket after slow bs l :=
    stored.2
  have updatedGet : Space.get after dest = some updated :=
    byte_view_get_put outputGet outputWrite updated
  have updatedWrite : Space.ro after dest = false := by
    rw [byte_view_ro_write]
    exact outputWrite
  have updatedSize : updated.size = output.size := by
    simp only [updated, Array.size_set!]
  have addRun : C.run (Ptr.add l.out 1) after =
      .ok (.ref dest (j + 1), after) := by
    rw [outPtr]
    have jLess : j < output.size := by omega
    have jBound : j + 1 ≤ updated.size := by
      rw [updatedSize]
      exact Nat.succ_le_of_lt jLess
    exact Ptr.add_nat_ok updatedGet jBound
  have privateWindow := callerRange_private_window
    invariant.good buffers.output.range outputPtr
  have nextState : DefaultStateJ after r zs z s :=
    invariant.byte_view_put outputGet outputWrite
      privateWindow _ updatedSize
  have sizes : ByteViewSizes h after :=
    byte_view_sizes_put outputGet outputWrite _ updatedSize
  have readonly : ∀ ref : BRef, Space.ro after ref =
      Space.ro h ref := by
    intro ref
    exact byte_view_ro_write h dest updated ref
  have inputRange := callerRange_capacity invariant.good
    nextState.good rfl sizes readonly buffers.input
  have outputRange := callerRange_capacity invariant.good
    nextState.good rfl sizes readonly buffers.output.range
  have nextBuffers : DispatchBuffers after r slow bs :=
    ⟨inputRange,
      ⟨outputRange, buffers.output.nonnull,
        buffers.output.count, buffers.output.produced⟩,
      buffers.separate, storedPacket.source⟩
  have nextPacket : FastInputPacket after slow bs result :=
    ⟨storedPacket.source, storedPacket.cursor,
      storedPacket.hold, storedPacket.bits⟩
  have outside : ∀ k,
      k < oo ∨ oo + slow.left.toNat ≤ k →
      updated[k]? = output[k]? := by
    intro k exterior
    have different : j ≠ k := by omega
    simp [updated, Array.set!, different]
  have frame : BufferFrame h after (fun _ => False)
      [⟨slow.put, slow.left.toNat⟩] :=
    output_view_buffer_frame outputPtr outputGet outputWrite
      updatedSize outside
  have run : C.run (do
      store8 l.out value
      let out ← l.out.add 1
      pure { l with out }) h = .ok (result, after) := by
    change (do
      store8 l.out value
      let out ← l.out.add 1
      pure { l with out }) h = .ok (result, after)
    change (store8 l.out value) h = .ok ((), after) at storeRun
    change (Ptr.add l.out 1) after =
      .ok (.ref dest (j + 1), after) at addRun
    rw [bind_ok storeRun]
    rw [bind_ok addRun]
    rfl
  exact ⟨run, nextPacket, nextState, nextBuffers, sizes,
    updatedGet, updatedWrite, frame⟩

end Zlib.Inflate.Proofs
