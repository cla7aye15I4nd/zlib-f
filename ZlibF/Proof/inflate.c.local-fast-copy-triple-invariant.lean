import ZlibF.Proof.«inflate.c.local-fast-state»
import ZlibF.Proof.«inflate.c.local-fast-copy-invariant»
import ZlibF.Proof.«inflate.c.fast-view-invariant»
import ZlibF.Proof.«inffast.c.frame»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Three actual fast copy stores preserve the default decoder relation
when their source and destination are different byte objects. This includes
the case where caller input occupies a disjoint slice of the output object. -/
theorem FastInputPacket.copy3_distinct_local_state
    {cutoff : Nat}
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    {source dest : BRef} (different : source ≠ dest)
    {saved output : Array UInt8} {sourceOff oo j : Nat}
    (fromPtr : l.from_ = .ref source sourceOff)
    (sourceGet : Space.get h source = some saved)
    (sourceRoom : sourceOff + 3 ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + 3 ≤ oo + slow.left.toNat) :
    let updated := Zlib.Inffast.Proofs.blitN saved 3 sourceOff j output
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.body3 l) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      LocalStateJ after cutoff r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      after = Space.put h dest updated ∧
      Space.get after dest = some updated ∧
      result.out = .ref dest (j + 3) ∧
      result.len = l.len - 3 ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  let a1 := output.set! j saved[sourceOff]
  let h1 := Space.put h dest a1
  let l1 : Zlib.Inffast.L := { l with
    from_ := .ref source (sourceOff + 1),
    out := .ref dest (j + 1) }
  obtain ⟨run1, packet1, invariant1, buffers1, _, output1,
      _, _⟩ :=
    Zlib.Inflate.Local.FastInputPacket.copy1_local_state packet invariant buffers left fromPtr
      sourceGet (by omega) outPtr outputPtr outputGet
      outputWrite outputSize
      (by omega : oo ≤ j ∧ j < oo + slow.left.toNat)
  change C.run (Zlib.Inffast.copy1 l) h = .ok (l1, h1) at run1
  have source1 : Space.get h1 source = some saved := by
    change Space.get (Space.put h dest a1) source = some saved
    rw [byte_view_get_put_ne h different]
    exact sourceGet
  have write1 : Space.ro h1 dest = false := by
    change Space.ro (Space.put h dest a1) dest = false
    rw [byte_view_ro_write]
    exact outputWrite
  let a2 := a1.set! (j + 1) saved[sourceOff + 1]
  let h2 := Space.put h1 dest a2
  let l2 : Zlib.Inffast.L := { l1 with
    from_ := .ref source (sourceOff + 2),
    out := .ref dest (j + 2) }
  obtain ⟨run2, packet2, invariant2, buffers2, _, output2,
      _, _⟩ :=
    Zlib.Inflate.Local.FastInputPacket.copy1_local_state packet1 invariant1 buffers1 left
      (by rfl) source1 (by omega)
      (by rfl) outputPtr output1 write1
      (by simpa [a1] using outputSize)
      (by omega : oo ≤ j + 1 ∧ j + 1 < oo + slow.left.toNat)
  change C.run (Zlib.Inffast.copy1 l1) h1 = .ok (l2, h2) at run2
  have source2 : Space.get h2 source = some saved := by
    change Space.get (Space.put h1 dest a2) source = some saved
    rw [byte_view_get_put_ne h1 different]
    exact source1
  have write2 : Space.ro h2 dest = false := by
    change Space.ro (Space.put h1 dest a2) dest = false
    rw [byte_view_ro_write]
    exact write1
  let a3 := a2.set! (j + 2) saved[sourceOff + 2]
  let h3 := Space.put h2 dest a3
  let l3 : Zlib.Inffast.L := { l2 with
    from_ := .ref source (sourceOff + 3),
    out := .ref dest (j + 3) }
  obtain ⟨run3, packet3, invariant3, buffers3, _, output3,
      _, _⟩ :=
    Zlib.Inflate.Local.FastInputPacket.copy1_local_state packet2 invariant2 buffers2 left
      (by rfl) source2 (by omega)
      (by rfl) outputPtr output2 write2
      (by simpa [a2, a1] using outputSize)
      (by omega : oo ≤ j + 2 ∧ j + 2 < oo + slow.left.toNat)
  change C.run (Zlib.Inffast.copy1 l2) h2 = .ok (l3, h3) at run3
  let result : Zlib.Inffast.L := { l3 with len := l.len - 3 }
  have bodyRun : C.run (Zlib.Inffast.Proofs.body3 l) h =
      .ok (result, h3) := by
    change Zlib.Inffast.Proofs.body3 l h = _
    change Zlib.Inffast.copy1 l h = .ok (l1, h1) at run1
    change Zlib.Inffast.copy1 l1 h1 = .ok (l2, h2) at run2
    change Zlib.Inffast.copy1 l2 h2 = .ok (l3, h3) at run3
    unfold Zlib.Inffast.Proofs.body3
    simp only [bind_app, run1, run2, run3, pure_app]
    rfl
  have resultPacket : FastInputPacket h3 slow bs result :=
    ⟨packet3.source, packet3.cursor, packet3.hold, packet3.bits⟩
  have exactView := packet.copy3_distinct_view buffers.separate
    left different fromPtr sourceGet sourceRoom outPtr
    outputPtr outputGet outputWrite outputSize outputRoom
  obtain ⟨viewResult, viewHeap, viewRun, _, _, _, _,
    viewOutput, _, _, _⟩ := exactView
  have sameRun : viewResult = result ∧ viewHeap = h3 := by
    rw [bodyRun] at viewRun
    cases viewRun
    exact ⟨rfl, rfl⟩
  rcases sameRun with ⟨_, heapEq⟩
  subst viewHeap
  have bytesEq : a3 =
      Zlib.Inffast.Proofs.blitN saved 3 sourceOff j output :=
    Option.some.inj (output3.symm.trans viewOutput)
  have heapEq : h3 = Space.put h dest a3 := by
    change Space.put (Space.put (Space.put h dest a1) dest a2)
      dest a3 = Space.put h dest a3
    rw [byte_view_put_put outputGet outputWrite a1 a2]
    rw [byte_view_put_put outputGet outputWrite a2 a3]
  have frameOutside : ∀ k,
      k < oo ∨ oo + slow.left.toNat ≤ k →
        (Zlib.Inffast.Proofs.blitN saved 3 sourceOff j output)[k]? =
          output[k]? := by
    intro k outside
    exact Zlib.Inffast.Proofs.blitN_frame saved 3 sourceOff j output k
      (by omega)
  have frame : BufferFrame h h3 (fun _ => False)
      [⟨slow.put, slow.left.toNat⟩] := by
    rw [heapEq, bytesEq]
    exact output_view_buffer_frame outputPtr outputGet outputWrite
      (Zlib.Inffast.Proofs.blitN_size _ _ _ _ _) frameOutside
  have sizes : ByteViewSizes h h3 := by
    rw [heapEq, bytesEq]
    exact byte_view_sizes_put outputGet outputWrite _
      (Zlib.Inffast.Proofs.blitN_size _ _ _ _ _)
  refine ⟨result, h3, bodyRun, resultPacket, invariant3,
    buffers3, sizes, ?_, ?_, ?_, ?_, frame⟩
  · rw [heapEq, bytesEq]
  · have exactOutput : Space.get h3 dest = some a3 := by
      simpa [h3, h2, h1, a3, a2, a1,
        show sourceOff + 1 + 1 = sourceOff + 2 by omega]
        using output3
    rw [bytesEq] at exactOutput
    exact exactOutput
  · rfl
  · rfl

/-- The same three actual stores preserve the default relation for an
overlapping back-reference in the output byte object. Each later source
read uses the array produced by the preceding store. -/
theorem FastInputPacket.copy3_same_local_state
    {cutoff : Nat}
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    {dest : BRef} {output : Array UInt8} {sourceOff oo j : Nat}
    (fromPtr : l.from_ = .ref dest sourceOff)
    (sourceRoom : sourceOff + 3 ≤ output.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + 3 ≤ oo + slow.left.toNat) :
    let updated := Zlib.Inffast.Proofs.cpyN 3 sourceOff j output
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.body3 l) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      LocalStateJ after cutoff r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      after = Space.put h dest updated ∧
      Space.get after dest = some updated ∧
      result.out = .ref dest (j + 3) ∧
      result.len = l.len - 3 ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  let a1 := output.set! j output[sourceOff]
  let h1 := Space.put h dest a1
  let l1 : Zlib.Inffast.L := { l with
    from_ := .ref dest (sourceOff + 1),
    out := .ref dest (j + 1) }
  obtain ⟨run1, packet1, invariant1, buffers1, _, output1,
      _, _⟩ :=
    Zlib.Inflate.Local.FastInputPacket.copy1_local_state packet invariant buffers left fromPtr
      outputGet (by omega) outPtr outputPtr outputGet
      outputWrite outputSize
      (by omega : oo ≤ j ∧ j < oo + slow.left.toNat)
  change C.run (Zlib.Inffast.copy1 l) h = .ok (l1, h1) at run1
  have write1 : Space.ro h1 dest = false := by
    change Space.ro (Space.put h dest a1) dest = false
    rw [byte_view_ro_write]
    exact outputWrite
  have sourceFit1 : sourceOff + 1 < a1.size := by
    simpa [a1] using
      (show sourceOff + 1 < output.size by omega)
  let a2 := a1.set! (j + 1) (a1[sourceOff + 1]'sourceFit1)
  let h2 := Space.put h1 dest a2
  let l2 : Zlib.Inffast.L := { l1 with
    from_ := .ref dest (sourceOff + 2),
    out := .ref dest (j + 2) }
  obtain ⟨run2, packet2, invariant2, buffers2, _, output2,
      _, _⟩ :=
    Zlib.Inflate.Local.FastInputPacket.copy1_local_state packet1 invariant1 buffers1 left
      (by rfl) output1 (by simpa [a1] using
        (show sourceOff + 1 < output.size by omega))
      (by rfl) outputPtr output1 write1
      (by simpa [a1] using outputSize)
      (by omega : oo ≤ j + 1 ∧ j + 1 < oo + slow.left.toNat)
  change C.run (Zlib.Inffast.copy1 l1) h1 = .ok (l2, h2) at run2
  have write2 : Space.ro h2 dest = false := by
    change Space.ro (Space.put h1 dest a2) dest = false
    rw [byte_view_ro_write]
    exact write1
  have sourceFit2 : sourceOff + 2 < a2.size := by
    simpa [a2, a1] using
      (show sourceOff + 2 < output.size by omega)
  let a3 := a2.set! (j + 2) (a2[sourceOff + 2]'sourceFit2)
  let h3 := Space.put h2 dest a3
  let l3 : Zlib.Inffast.L := { l2 with
    from_ := .ref dest (sourceOff + 3),
    out := .ref dest (j + 3) }
  obtain ⟨run3, packet3, invariant3, buffers3, _, output3,
      _, _⟩ :=
    Zlib.Inflate.Local.FastInputPacket.copy1_local_state packet2 invariant2 buffers2 left
      (by rfl) output2 (by simpa [a2, a1] using
        (show sourceOff + 2 < output.size by omega))
      (by rfl) outputPtr output2 write2
      (by simpa [a2, a1] using outputSize)
      (by omega : oo ≤ j + 2 ∧ j + 2 < oo + slow.left.toNat)
  change C.run (Zlib.Inffast.copy1 l2) h2 = .ok (l3, h3) at run3
  let result : Zlib.Inffast.L := { l3 with len := l.len - 3 }
  have bodyRun : C.run (Zlib.Inffast.Proofs.body3 l) h =
      .ok (result, h3) := by
    change Zlib.Inffast.Proofs.body3 l h = _
    change Zlib.Inffast.copy1 l h = .ok (l1, h1) at run1
    change Zlib.Inffast.copy1 l1 h1 = .ok (l2, h2) at run2
    change Zlib.Inffast.copy1 l2 h2 = .ok (l3, h3) at run3
    unfold Zlib.Inffast.Proofs.body3
    simp only [bind_app, run1, run2, run3, pure_app]
    rfl
  have resultPacket : FastInputPacket h3 slow bs result :=
    ⟨packet3.source, packet3.cursor, packet3.hold, packet3.bits⟩
  have exactView := packet.copy3_same_view buffers.separate
    left fromPtr sourceRoom outPtr outputPtr outputGet
    outputWrite outputSize outputRoom
  obtain ⟨viewResult, viewHeap, viewRun, _, _, _, _,
    viewOutput, _, _, _⟩ := exactView
  have sameRun : viewResult = result ∧ viewHeap = h3 := by
    rw [bodyRun] at viewRun
    cases viewRun
    exact ⟨rfl, rfl⟩
  rcases sameRun with ⟨_, heapEq⟩
  subst viewHeap
  have bytesEq : a3 =
      Zlib.Inffast.Proofs.cpyN 3 sourceOff j output :=
    Option.some.inj (output3.symm.trans viewOutput)
  have heapEq : h3 = Space.put h dest a3 := by
    change Space.put (Space.put (Space.put h dest a1) dest a2)
      dest a3 = Space.put h dest a3
    rw [byte_view_put_put outputGet outputWrite a1 a2]
    rw [byte_view_put_put outputGet outputWrite a2 a3]
  have frameOutside : ∀ k,
      k < oo ∨ oo + slow.left.toNat ≤ k →
        (Zlib.Inffast.Proofs.cpyN 3 sourceOff j output)[k]? =
          output[k]? := by
    intro k outside
    exact Zlib.Inffast.Proofs.cpyN_frame 3 sourceOff j output k
      (by omega)
  have frame : BufferFrame h h3 (fun _ => False)
      [⟨slow.put, slow.left.toNat⟩] := by
    rw [heapEq, bytesEq]
    exact output_view_buffer_frame outputPtr outputGet outputWrite
      (Zlib.Inffast.Proofs.cpyN_size _ _ _ _) frameOutside
  have sizes : ByteViewSizes h h3 := by
    rw [heapEq, bytesEq]
    exact byte_view_sizes_put outputGet outputWrite _
      (Zlib.Inffast.Proofs.cpyN_size _ _ _ _)
  refine ⟨result, h3, bodyRun, resultPacket, invariant3,
    buffers3, sizes, ?_, ?_, ?_, ?_, frame⟩
  · rw [heapEq, bytesEq]
  · have exactOutput : Space.get h3 dest = some a3 := by
      simpa [h3, h2, h1, a3, a2, a1,
        show sourceOff + 1 + 1 = sourceOff + 2 by omega]
        using output3
    rw [bytesEq] at exactOutput
    exact exactOutput
  · rfl
  · rfl

/-- The translated three-byte match body preserves the default state and
caller frame for either distinct or overlapping source storage. -/
theorem FastInputPacket.copy3_local_state
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
    (sourceRoom : sourceOff + 3 ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + 3 ≤ oo + slow.left.toNat) :
    let updated := if source = dest then
      Zlib.Inffast.Proofs.cpyN 3 sourceOff j output
      else Zlib.Inffast.Proofs.blitN saved 3 sourceOff j output
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.body3 l) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      LocalStateJ after cutoff r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      after = Space.put h dest updated ∧
      Space.get after dest = some updated ∧
      result.out = .ref dest (j + 3) ∧
      result.len = l.len - 3 ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  by_cases same : source = dest
  · subst source
    have arrays : saved = output :=
      Option.some.inj (sourceGet.symm.trans outputGet)
    subst saved
    simpa using Zlib.Inflate.Local.FastInputPacket.copy3_same_local_state packet invariant
      buffers left fromPtr sourceRoom outPtr outputPtr outputGet
      outputWrite outputSize outputRoom
  · simpa [same] using Zlib.Inflate.Local.FastInputPacket.copy3_distinct_local_state packet
      invariant buffers left same fromPtr sourceGet sourceRoom
      outPtr outputPtr outputGet outputWrite outputSize outputRoom

#print axioms FastInputPacket.copy3_distinct_local_state
#print axioms FastInputPacket.copy3_same_local_state
#print axioms FastInputPacket.copy3_local_state
end Zlib.Inflate.Local
