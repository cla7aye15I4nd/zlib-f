import ZlibF.Proof.«inflate.c.local-fast-state»
import ZlibF.Proof.«inflate.c.local-fast-copy-tail-invariant»
import ZlibF.Proof.«inflate.c.fast-view-tail-invariant»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The window/output `while (len > 2)` suffix retains the default state,
exact copied bytes and the caller output frame through its short tail. -/
theorem FastInputPacket.tailW_local_state
    {cutoff : Nat}
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {n : Nat} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (count : l.len.toNat = n)
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
      C.run (Zlib.Inffast.Proofs.tailW l) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      LocalStateJ after cutoff r zs z s ∧
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
  let q := n / 3
  let rem := n % 3
  have small : rem < 3 := by dsimp [rem]; omega
  have split : n = 3 * q + rem := by dsimp [q, rem]; omega
  obtain ⟨loop, middle, whileRun, loopPacket,
      loopInvariant, loopBuffers, loopSizes, loopEq,
      loopOutput, loopWritable, loopHeap, _⟩ :=
    Zlib.Inflate.Local.FastInputPacket.while3_local_state packet invariant buffers left
      (q := q) (rem := rem) small
      (by omega : l.len.toNat = 3 * q + rem)
      fromPtr sourceGet (by omega) outPtr outputPtr outputGet
      outputWrite outputSize (by omega)
  let mid := if source = dest then
    Zlib.Inffast.Proofs.cpyN (3 * q) sourceOff j output
    else Zlib.Inffast.Proofs.blitN saved (3 * q) sourceOff j output
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
  have srcRoom : sourceOff + 3 * q + rem ≤ srcMid.size := by
    by_cases same : source = dest
    · subst source
      have arrays : saved = output :=
        Option.some.inj (sourceGet.symm.trans outputGet)
      simp [srcMid, mid, Zlib.Inffast.Proofs.cpyN_size]
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
    Zlib.Inflate.Local.FastInputPacket.tailIf_local_state loopPacket loopInvariant loopBuffers
      left tailCount small
      (by simp [loopEq]) sourceMid srcRoom
      (by simp [loopEq]) outputPtr loopOutput loopWritable
      (by rw [midSize]; exact outputSize)
      (by omega : oo ≤ j + 3 * q ∧
        j + 3 * q + rem ≤ oo + slow.left.toNat)
  have stateRun : C.run (Zlib.Inffast.Proofs.tailW l) h =
      .ok (result, after) := by
    change Zlib.Inffast.Proofs.tailW l h = .ok (result, after)
    unfold Zlib.Inffast.Proofs.tailW
    rw [bind_app]
    change cwhile Zlib.Inffast.Proofs.cond3
      Zlib.Inffast.Proofs.body3 l h = .ok (loop, middle) at whileRun
    rw [whileRun]
    exact tailRun
  obtain ⟨viewResult, viewAfter, viewRun, _, viewEq,
      viewOutput, viewWrite⟩ :=
    packet.tailW_view count buffers.separate left
      fromPtr sourceGet sourceRoom outPtr outputPtr outputGet
      outputWrite outputSize outputRoom
  have sameRun : viewResult = result ∧ viewAfter = after :=
    Prod.mk.inj (Except.ok.inj (viewRun.symm.trans stateRun))
  rw [sameRun.1] at viewEq
  rw [sameRun.2] at viewOutput viewWrite
  let tailArray := if source = dest then
    Zlib.Inffast.Proofs.cpyN rem
      (sourceOff + 3 * q) (j + 3 * q) mid
    else Zlib.Inffast.Proofs.blitN srcMid rem
      (sourceOff + 3 * q) (j + 3 * q) mid
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

#print axioms FastInputPacket.tailW_local_state
end Zlib.Inflate.Local
