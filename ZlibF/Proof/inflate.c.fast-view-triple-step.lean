import ZlibF.Proof.«inflate.c.fast-view-triple-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The invariant-preserving three-byte step also retains the exact source
cursor and next readable source view needed by the repetition loop. -/
theorem FastInputPacket.copy3_default_loop_step
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
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
      DefaultStateJ after r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      after = Space.put h dest updated ∧
      Space.get after dest = some updated ∧
      Space.ro after dest = false ∧
      Space.get after source = some
        (if source = dest then updated else saved) ∧
      result = { l with
        from_ := .ref source (sourceOff + 3),
        out := .ref dest (j + 3),
        len := l.len - 3 } ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  obtain ⟨result, after, run, packetAfter, invariantAfter,
      buffersAfter, sizes, heapEq, outputAfter, _, _, frame⟩ :=
    packet.copy3_default_state invariant buffers left fromPtr
      sourceGet sourceRoom outPtr outputPtr outputGet outputWrite
      outputSize outputRoom
  obtain ⟨viewResult, viewAfter, viewRun, _, _, _, _, _,
      writable, sourceAfter, resultEq⟩ :=
    packet.copy3_view buffers.separate left fromPtr sourceGet
      sourceRoom outPtr outputPtr outputGet outputWrite
      outputSize outputRoom
  have sameResult : viewResult = result ∧ viewAfter = after := by
    rw [run] at viewRun
    cases viewRun
    exact ⟨rfl, rfl⟩
  rcases sameResult with ⟨resultSame, afterSame⟩
  rw [resultSame] at resultEq
  rw [afterSame] at writable sourceAfter
  have sourceView : Space.get after source =
      some (if source = dest then
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN 3 sourceOff j output
        else Zlib.Inffast.Proofs.blitN saved 3 sourceOff j output)
        else saved) := by
    by_cases same : source = dest
    · simpa only [if_pos same] using sourceAfter
    · simpa only [if_neg same] using sourceAfter
  exact ⟨result, after, run, packetAfter, invariantAfter,
    buffersAfter, sizes, heapEq, outputAfter, writable,
    sourceView, resultEq, frame⟩

end Zlib.Inflate.Proofs
