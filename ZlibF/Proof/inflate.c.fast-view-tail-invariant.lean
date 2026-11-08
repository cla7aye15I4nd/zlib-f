import ZlibF.Proof.«inflate.c.fast-view-do-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated zero-, one- and two-byte direct match suffix retains
the default reachable-state relation and caller buffer packet. -/
theorem FastInputPacket.tailIf_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {remaining : Nat}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    (count : l.len.toNat = remaining)
    (small : remaining < 3)
    {source dest : BRef} {saved output : Array UInt8}
    {sourceOff oo j : Nat}
    (fromPtr : l.from_ = .ref source sourceOff)
    (sourceGet : Space.get h source = some saved)
    (sourceRoom : sourceOff + remaining ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + remaining ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.tailIf l) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      DefaultStateJ after r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      result = { l with
        from_ := .ref source (sourceOff + remaining),
        out := .ref dest (j + remaining) } ∧
      Space.get after dest = some
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN remaining sourceOff j output
        else
          Zlib.Inffast.Proofs.blitN saved remaining sourceOff j output) ∧
      Space.ro after dest = false ∧
      after = Space.put h dest
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN remaining sourceOff j output
        else
          Zlib.Inffast.Proofs.blitN saved remaining sourceOff j output) ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  let finalArray := if source = dest then
    Zlib.Inffast.Proofs.cpyN remaining sourceOff j output
    else Zlib.Inffast.Proofs.blitN saved remaining sourceOff j output
  have finalSize : finalArray.size = output.size := by
    by_cases same : source = dest
    · simp [finalArray, same, Zlib.Inffast.Proofs.cpyN_size]
    · simp [finalArray, same, Zlib.Inffast.Proofs.blitN_size]
  have finalOutside : ∀ k,
      k < oo ∨ oo + slow.left.toNat ≤ k →
        finalArray[k]? = output[k]? := by
    intro k outside
    have copyOutside : k < j ∨ j + remaining ≤ k := by omega
    by_cases same : source = dest
    · simpa [finalArray, same] using
        Zlib.Inffast.Proofs.cpyN_frame remaining sourceOff j
          output k copyOutside
    · simpa [finalArray, same] using
        Zlib.Inffast.Proofs.blitN_frame saved remaining sourceOff
          j output k copyOutside
  have frameOfHeap {after : Heap}
      (heapEq : after = Space.put h dest finalArray) :
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
    rw [heapEq]
    exact output_view_buffer_frame outputPtr outputGet outputWrite
      finalSize finalOutside
  obtain ⟨viewResult, viewAfter, viewRun, _, _, _,
      viewOutput, viewWrite, viewEq⟩ :=
    packet.tailIf_view buffers.separate left count small
      fromPtr sourceGet sourceRoom outPtr outputPtr outputGet
      outputWrite outputSize outputRoom
  have cases : remaining = 0 ∨ remaining = 1 ∨ remaining = 2 := by
    omega
  rcases cases with zero | one | two
  · rw [zero] at count sourceRoom outputRoom viewEq viewOutput ⊢
    have lenZero : l.len = 0 :=
      UInt32.toNat_inj.mp (by simpa using count)
    have stateRun : C.run (Zlib.Inffast.Proofs.tailIf l) h =
        .ok (l, h) := by
      simp [Zlib.Inffast.Proofs.tailIf, lenZero, C.run]
    rw [stateRun] at viewRun
    cases viewRun
    have heapEq : h = Space.put h dest finalArray := by
      have arrayEq : finalArray = output := by
        simp [finalArray, zero, Zlib.Inffast.Proofs.cpyN,
          Zlib.Inffast.Proofs.blitN]
      rw [arrayEq]
      exact (byte_view_put_self outputGet outputWrite).symm
    exact ⟨l, h, stateRun, packet, invariant, buffers,
      ByteViewSizes.refl h, viewEq, viewOutput, viewWrite,
      by simpa [finalArray, zero] using heapEq,
      frameOfHeap heapEq⟩
  · rw [one] at count sourceRoom outputRoom viewEq viewOutput ⊢
    have lenOne : l.len = 1 :=
      UInt32.toNat_inj.mp (by simpa using count)
    let updated := output.set! j saved[sourceOff]
    let after := Space.put h dest updated
    let next : Zlib.Inffast.L := { l with
      from_ := .ref source (sourceOff + 1),
      out := .ref dest (j + 1) }
    obtain ⟨copyRun, nextPacket, nextInvariant,
        nextBuffers, sizes, outputAfter, _, _⟩ :=
      packet.copy1_default_state invariant buffers left
        fromPtr sourceGet (by omega) outPtr outputPtr outputGet
        outputWrite outputSize
        (by omega : oo ≤ j ∧ j < oo + slow.left.toNat)
    change C.run (Zlib.Inffast.copy1 l) h =
      .ok (next, after) at copyRun
    have stateRun : C.run (Zlib.Inffast.Proofs.tailIf l) h =
        .ok (next, after) := by
      change Zlib.Inffast.Proofs.tailIf l h = .ok (next, after)
      unfold Zlib.Inffast.Proofs.tailIf
      change Zlib.Inffast.copy1 l h = .ok (next, after) at copyRun
      simp [lenOne, bind_app, copyRun, next]
    have sameRun : viewResult = next ∧ viewAfter = after := by
      exact Prod.mk.inj (Except.ok.inj
        (viewRun.symm.trans stateRun))
    rw [sameRun.1] at viewEq
    rw [sameRun.2] at viewOutput viewWrite
    have arrayEq : updated =
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN 1 sourceOff j output
        else
          Zlib.Inffast.Proofs.blitN saved 1 sourceOff j output) :=
      Option.some.inj (outputAfter.symm.trans viewOutput)
    have heapEq : after = Space.put h dest
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN 1 sourceOff j output
        else
          Zlib.Inffast.Proofs.blitN saved 1 sourceOff j output) := by
      change Space.put h dest updated = _
      rw [arrayEq]
    have frame : BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] :=
      frameOfHeap (by simpa [finalArray, one] using heapEq)
    exact ⟨next, after, stateRun, nextPacket, nextInvariant,
      nextBuffers, sizes, viewEq, viewOutput, viewWrite,
      heapEq, frame⟩
  · rw [two] at count sourceRoom outputRoom viewEq viewOutput ⊢
    have lenTwo : l.len = 2 :=
      UInt32.toNat_inj.mp (by simpa using count)
    let a1 := output.set! j saved[sourceOff]
    let h1 := Space.put h dest a1
    let l1 : Zlib.Inffast.L := { l with
      from_ := .ref source (sourceOff + 1),
      out := .ref dest (j + 1) }
    obtain ⟨run1, packet1, invariant1, buffers1,
        sizes1, output1, _, _⟩ :=
      packet.copy1_default_state invariant buffers left
        fromPtr sourceGet (by omega) outPtr outputPtr outputGet
        outputWrite outputSize
        (by omega : oo ≤ j ∧ j < oo + slow.left.toNat)
    change C.run (Zlib.Inffast.copy1 l) h =
      .ok (l1, h1) at run1
    have source1 : Space.get h1 source = some
        (if source = dest then a1 else saved) := by
      by_cases same : source = dest
      · subst source
        simpa [h1, a1] using output1
      · simpa [same, h1] using
          (show Space.get (Space.put h dest a1) source =
            some saved by
              rw [byte_view_get_put_ne h same]
              exact sourceGet)
    have writable1 : Space.ro h1 dest = false := by
      change Space.ro (Space.put h dest a1) dest = false
      rw [byte_view_ro_write]
      exact outputWrite
    have sourceRoom1 : sourceOff + 1 <
        (if source = dest then a1 else saved).size := by
      by_cases same : source = dest
      · subst source
        have arrays : saved = output :=
          Option.some.inj (sourceGet.symm.trans outputGet)
        have a1Size : a1.size = output.size := by simp [a1]
        simpa only [ite_true, a1Size] using
          (show sourceOff + 1 < output.size by
            rw [arrays] at sourceRoom
            omega)
      · simp [same]
        omega
    let a2 := a1.set! (j + 1)
      (if source = dest then a1 else saved)[sourceOff + 1]
    let h2 := Space.put h1 dest a2
    let l2 : Zlib.Inffast.L := { l1 with
      from_ := .ref source (sourceOff + 2),
      out := .ref dest (j + 2) }
    obtain ⟨run2, packet2, invariant2, buffers2,
        sizes2, output2, _, _⟩ :=
      packet1.copy1_default_state invariant1 buffers1 left
        (by rfl) source1 sourceRoom1 (by rfl)
        outputPtr output1 writable1
        (by simpa [a1] using outputSize)
        (by omega : oo ≤ j + 1 ∧
          j + 1 < oo + slow.left.toNat)
    change C.run (Zlib.Inffast.copy1 l1) h1 =
      .ok (l2, h2) at run2
    have stateRun : C.run (Zlib.Inffast.Proofs.tailIf l) h =
        .ok (l2, h2) := by
      change Zlib.Inffast.Proofs.tailIf l h = .ok (l2, h2)
      change Zlib.Inffast.copy1 l h = .ok (l1, h1) at run1
      change Zlib.Inffast.copy1 l1 h1 = .ok (l2, h2) at run2
      unfold Zlib.Inffast.Proofs.tailIf
      have starts : (l.len != 0) = true := by simp [lenTwo]
      simp only [starts, ite_true, bind_app]
      rw [run1]
      have another : (l1.len > 1) = true := by
        simp [l1, lenTwo]
      simp only [another, ite_true, bind_app]
      rw [run2]
      rfl
    have sameRun : viewResult = l2 ∧ viewAfter = h2 := by
      exact Prod.mk.inj (Except.ok.inj
        (viewRun.symm.trans stateRun))
    rw [sameRun.1] at viewEq
    rw [sameRun.2] at viewOutput viewWrite
    have arrayEq : a2 =
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN 2 sourceOff j output
        else
          Zlib.Inffast.Proofs.blitN saved 2 sourceOff j output) :=
      Option.some.inj (output2.symm.trans viewOutput)
    have heapEq : h2 = Space.put h dest
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN 2 sourceOff j output
        else
          Zlib.Inffast.Proofs.blitN saved 2 sourceOff j output) := by
      change Space.put (Space.put h dest a1) dest a2 =
        _
      rw [byte_view_put_put outputGet outputWrite a1 a2]
      rw [arrayEq]
    have frame : BufferFrame h h2 (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] :=
      frameOfHeap (by simpa [finalArray, two] using heapEq)
    exact ⟨l2, h2, stateRun, packet2, invariant2,
      buffers2, sizes1.trans sizes2, viewEq, viewOutput,
      viewWrite, heapEq, frame⟩

/-- The complete translated direct-output match suffix retains the default
state and caller buffers through the mandatory repetition and short tail. -/
theorem FastInputPacket.tailD_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {n : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (count : l.len.toNat = n)
    (atLeastThree : 3 ≤ n)
    (left : slow.left ≠ 0)
    {source dest : BRef} {saved output : Array UInt8}
    {sourceOff oo j : Nat}
    (fromPtr : l.from_ = .ref source sourceOff)
    (sourceGet : Space.get h source = some saved)
    (sourceRoom : sourceOff + n ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + n ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.tailD l) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      DefaultStateJ after r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      result = { l with
        from_ := .ref source (sourceOff + n),
        out := .ref dest (j + n),
        len := UInt32.ofNat (n % 3) } ∧
      Space.get after dest = some
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN n sourceOff j output
        else
          Zlib.Inffast.Proofs.blitN saved n sourceOff j output) ∧
      Space.ro after dest = false ∧
      after = Space.put h dest
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN n sourceOff j output
        else
          Zlib.Inffast.Proofs.blitN saved n sourceOff j output) ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  let q := n / 3 - 1
  let rem := n % 3
  have small : rem < 3 := by dsimp [rem]; omega
  have split : n = 3 * (q + 1) + rem := by
    dsimp [q, rem]
    omega
  obtain ⟨loop, middle, doRun, loopPacket, loopInvariant,
      loopBuffers, loopSizes, loopEq, loopOutput,
      loopWritable, loopHeap, _⟩ :=
    packet.do3_default_state invariant buffers left
      (q := q) (rem := rem) small
      (by omega : l.len.toNat = 3 * (q + 1) + rem)
      fromPtr sourceGet (by omega) outPtr outputPtr outputGet
      outputWrite outputSize (by omega)
  let mid := if source = dest then
    Zlib.Inffast.Proofs.cpyN (3 * (q + 1)) sourceOff j output
    else Zlib.Inffast.Proofs.blitN saved (3 * (q + 1)) sourceOff j output
  let srcMid := if source = dest then mid else saved
  have midSize : mid.size = output.size := by
    by_cases same : source = dest
    · simp [mid, same, Zlib.Inffast.Proofs.cpyN_size]
    · simp [mid, same, Zlib.Inffast.Proofs.blitN_size]
  have sourceMid : Space.get middle source = some srcMid := by
    rw [loopHeap]
    by_cases same : source = dest
    · subst source
      simpa [srcMid, mid] using
        (byte_view_get_put outputGet outputWrite mid)
    · simp only [srcMid, same, ite_false]
      rw [byte_view_get_put_ne h same]
      exact sourceGet
  have srcRoom : sourceOff + 3 * (q + 1) + rem ≤ srcMid.size := by
    by_cases same : source = dest
    · subst source
      have arrays : saved = output :=
        Option.some.inj (sourceGet.symm.trans outputGet)
      simp only [srcMid, mid, if_pos rfl,
        Zlib.Inffast.Proofs.cpyN_size]
      rw [arrays] at sourceRoom
      omega
    · simp only [srcMid, same, ite_false]
      omega
  have tailCount : loop.len.toNat = rem := by
    rw [loopEq]
    simp
    omega
  obtain ⟨result, after, tailRun, resultPacket,
      resultInvariant, resultBuffers, tailSizes, _, _,
      resultWritable, tailHeap, _⟩ :=
    loopPacket.tailIf_default_state loopInvariant loopBuffers
      left tailCount small
      (by simp [loopEq]) sourceMid srcRoom
      (by simp [loopEq]) outputPtr loopOutput loopWritable
      (by rw [midSize]; exact outputSize)
      (by omega : oo ≤ j + 3 * (q + 1) ∧
        j + 3 * (q + 1) + rem ≤ oo + slow.left.toNat)
  have stateRun : C.run (Zlib.Inffast.Proofs.tailD l) h =
      .ok (result, after) := by
    change Zlib.Inffast.Proofs.tailD l h = .ok (result, after)
    unfold Zlib.Inffast.Proofs.tailD
    rw [bind_app]
    change cdoWhile Zlib.Inffast.Proofs.body3
      Zlib.Inffast.Proofs.cond3 l h = .ok (loop, middle) at doRun
    rw [doRun]
    exact tailRun
  obtain ⟨viewResult, viewAfter, viewRun, _, viewEq,
      viewOutput, viewWrite⟩ :=
    packet.tailD_view count atLeastThree buffers.separate left
      fromPtr sourceGet sourceRoom outPtr outputPtr outputGet
      outputWrite outputSize outputRoom
  have sameRun : viewResult = result ∧ viewAfter = after :=
    Prod.mk.inj (Except.ok.inj (viewRun.symm.trans stateRun))
  rw [sameRun.1] at viewEq
  rw [sameRun.2] at viewOutput viewWrite
  let tailArray := if source = dest then
    Zlib.Inffast.Proofs.cpyN rem
      (sourceOff + 3 * (q + 1)) (j + 3 * (q + 1)) mid
    else Zlib.Inffast.Proofs.blitN srcMid rem
      (sourceOff + 3 * (q + 1)) (j + 3 * (q + 1)) mid
  have tailHeapEq : after = Space.put middle dest tailArray :=
    tailHeap
  have heapBase : after = Space.put h dest tailArray := by
    rw [tailHeapEq, loopHeap]
    exact byte_view_put_put outputGet outputWrite mid tailArray
  have tailArrayGet : Space.get after dest = some tailArray := by
    rw [heapBase]
    exact byte_view_get_put outputGet outputWrite tailArray
  have arrayEq : tailArray =
      (if source = dest then
        Zlib.Inffast.Proofs.cpyN n sourceOff j output
      else
        Zlib.Inffast.Proofs.blitN saved n sourceOff j output) :=
    Option.some.inj (tailArrayGet.symm.trans viewOutput)
  have finalHeap : after = Space.put h dest
      (if source = dest then
        Zlib.Inffast.Proofs.cpyN n sourceOff j output
      else
        Zlib.Inffast.Proofs.blitN saved n sourceOff j output) := by
    rw [heapBase, arrayEq]
  have finalSize :
      (if source = dest then
        Zlib.Inffast.Proofs.cpyN n sourceOff j output
      else
        Zlib.Inffast.Proofs.blitN saved n sourceOff j output).size =
        output.size := by
    by_cases same : source = dest
    · simp [same, Zlib.Inffast.Proofs.cpyN_size]
    · simp [same, Zlib.Inffast.Proofs.blitN_size]
  have finalOutside : ∀ k,
      k < oo ∨ oo + slow.left.toNat ≤ k →
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN n sourceOff j output
        else
          Zlib.Inffast.Proofs.blitN saved n sourceOff j output)[k]? =
          output[k]? := by
    intro k outside
    have copyOutside : k < j ∨ j + n ≤ k := by omega
    by_cases same : source = dest
    · simpa [same] using
        Zlib.Inffast.Proofs.cpyN_frame n sourceOff j output k
          copyOutside
    · simpa [same] using
        Zlib.Inffast.Proofs.blitN_frame saved n sourceOff j output
          k copyOutside
  have frame : BufferFrame h after (fun _ => False)
      [⟨slow.put, slow.left.toNat⟩] := by
    rw [finalHeap]
    exact output_view_buffer_frame outputPtr outputGet outputWrite
      finalSize finalOutside
  exact ⟨result, after, stateRun, resultPacket,
    resultInvariant, resultBuffers, loopSizes.trans tailSizes,
    viewEq, viewOutput, viewWrite, finalHeap, frame⟩

end Zlib.Inflate.Proofs
