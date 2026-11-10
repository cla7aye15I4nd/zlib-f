import ZlibF.Proof.«inflate.c.fast-view-copy»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated three-copy body reads and writes general byte views when
the source and destination are different objects. The caller input can still
be a disjoint interval of the destination object. -/
theorem FastInputPacket.copy3_distinct_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs fastLocal)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    {source dest : BRef} (different : source ≠ dest)
    {saved array : Array UInt8} {sourceOff oo j : Nat}
    (fromPtr : fastLocal.from_ = .ref source sourceOff)
    (sourceGet : Space.get h source = some saved)
    (sourceRoom : sourceOff + 3 ≤ saved.size)
    (outPtr : fastLocal.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (outputRoom : oo ≤ j ∧ j + 3 ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.body3 fastLocal) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.from_ = .ref source (sourceOff + 3) ∧
      result.out = .ref dest (j + 3) ∧
      result.len = fastLocal.len - 3 ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.blitN saved 3 sourceOff j array) ∧
      Space.ro after dest = false ∧
      Space.get after source = some saved ∧
      result = { fastLocal with
        from_ := .ref source (sourceOff + 3),
        out := .ref dest (j + 3),
        len := fastLocal.len - 3 } := by
  let a1 := array.set! j saved[sourceOff]
  let h1 := Space.put h dest a1
  let l1 : Zlib.Inffast.L := { fastLocal with
    from_ := .ref source (sourceOff + 1), out := .ref dest (j + 1) }
  have ⟨run1, packet1⟩ := packet.copy1_view separate left
    fromPtr sourceGet (by omega) outPtr outputPtr outputGet
    outputWrite outputSize (by omega : oo ≤ j ∧ j < oo + slow.left.toNat)
  change Zlib.Inffast.copy1 fastLocal h = .ok (l1, h1) at run1
  have source1 : Space.get h1 source = some saved := by
    change Space.get (Space.put h dest a1) source = some saved
    rw [byte_view_get_put_ne h different]
    exact sourceGet
  have output1 : Space.get h1 dest = some a1 :=
    byte_view_get_put outputGet outputWrite _
  have writable1 : Space.ro h1 dest = false := by
    change Space.ro (Space.put h dest a1) dest = false
    rw [byte_view_ro_write]
    exact outputWrite
  let a2 := a1.set! (j + 1) saved[sourceOff + 1]
  let h2 := Space.put h1 dest a2
  let l2 : Zlib.Inffast.L := { l1 with
    from_ := .ref source (sourceOff + 2), out := .ref dest (j + 2) }
  have ⟨run2, packet2⟩ := packet1.copy1_view separate left
    (by rfl) source1 (by simpa only [Array.size] using
      (show sourceOff + 1 < saved.size by omega))
    (by rfl) outputPtr output1 writable1
    (by simpa [a1] using outputSize)
    (by omega : oo ≤ j + 1 ∧ j + 1 < oo + slow.left.toNat)
  change Zlib.Inffast.copy1 l1 h1 = .ok (l2, h2) at run2
  have source2 : Space.get h2 source = some saved := by
    change Space.get (Space.put h1 dest a2) source = some saved
    rw [byte_view_get_put_ne h1 different]
    exact source1
  have output2 : Space.get h2 dest = some a2 :=
    byte_view_get_put output1 writable1 _
  have writable2 : Space.ro h2 dest = false := by
    change Space.ro (Space.put h1 dest a2) dest = false
    rw [byte_view_ro_write]
    exact writable1
  let a3 := a2.set! (j + 2) saved[sourceOff + 2]
  let h3 := Space.put h2 dest a3
  let l3 : Zlib.Inffast.L := { l2 with
    from_ := .ref source (sourceOff + 3), out := .ref dest (j + 3) }
  have ⟨run3, packet3⟩ :=
    packet2.copy1_view (sourceOff := sourceOff + 2) separate left
    (by rfl) source2 (by omega)
    (by rfl) outputPtr output2 writable2
    (by simpa [a2, a1] using outputSize)
    (by omega : oo ≤ j + 2 ∧ j + 2 < oo + slow.left.toNat)
  change Zlib.Inffast.copy1 l2 h2 = .ok (l3, h3) at run3
  let result : Zlib.Inffast.L := { l3 with len := fastLocal.len - 3 }
  have runBody : Zlib.Inffast.Proofs.body3 fastLocal h =
      .ok (result, h3) := by
    unfold Zlib.Inffast.Proofs.body3
    simp only [bind_app, run1, run2, run3, pure_app]
    simp [result, l3, l2, l1]
  have resultPacket : FastInputPacket h3 slow bs result :=
    ⟨packet3.source, packet3.cursor, packet3.hold, packet3.bits⟩
  have output3 : Space.get h3 dest = some a3 :=
    byte_view_get_put output2 writable2 _
  have writable3 : Space.ro h3 dest = false := by
    change Space.ro (Space.put h2 dest a3) dest = false
    rw [byte_view_ro_write]
    exact writable2
  have source3 : Space.get h3 source = some saved := by
    change Space.get (Space.put h2 dest a3) source = some saved
    rw [byte_view_get_put_ne h2 different]
    exact source2
  have bytes3 : a3 =
      Zlib.Inffast.Proofs.blitN saved 3 sourceOff j array := by
    rw [← copyOtherBytes_eq_blitN]
    simp only [copyOtherBytes, a1, a2, a3,
      getElem!_pos saved sourceOff (by omega),
      getElem!_pos saved (sourceOff + 1) (by omega),
      getElem!_pos saved (sourceOff + 2) (by omega)]
  exact ⟨result, h3, runBody, resultPacket,
    by simp [result, l3],
    by simp [result, l3],
    by simp [result],
    by simpa only [bytes3] using output3, writable3, source3,
    by simp [result, l3, l2, l1]⟩

/-- The three-copy body also preserves the C order when the source lies in
the destination object. Later reads can see bytes written by earlier copies. -/
theorem FastInputPacket.copy3_same_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs fastLocal)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    {dest : BRef} {array : Array UInt8} {sourceOff oo j : Nat}
    (fromPtr : fastLocal.from_ = .ref dest sourceOff)
    (sourceRoom : sourceOff + 3 ≤ array.size)
    (outPtr : fastLocal.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (outputRoom : oo ≤ j ∧ j + 3 ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.body3 fastLocal) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.from_ = .ref dest (sourceOff + 3) ∧
      result.out = .ref dest (j + 3) ∧
      result.len = fastLocal.len - 3 ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.cpyN 3 sourceOff j array) ∧
      Space.ro after dest = false ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.cpyN 3 sourceOff j array) ∧
      result = { fastLocal with
        from_ := .ref dest (sourceOff + 3),
        out := .ref dest (j + 3),
        len := fastLocal.len - 3 } := by
  let a1 := array.set! j array[sourceOff]
  let h1 := Space.put h dest a1
  let l1 : Zlib.Inffast.L := { fastLocal with
    from_ := .ref dest (sourceOff + 1), out := .ref dest (j + 1) }
  have ⟨run1, packet1⟩ := packet.copy1_view separate left
    fromPtr outputGet (by omega) outPtr outputPtr outputGet
    outputWrite outputSize (by omega : oo ≤ j ∧ j < oo + slow.left.toNat)
  change Zlib.Inffast.copy1 fastLocal h = .ok (l1, h1) at run1
  have output1 : Space.get h1 dest = some a1 :=
    byte_view_get_put outputGet outputWrite _
  have writable1 : Space.ro h1 dest = false := by
    change Space.ro (Space.put h dest a1) dest = false
    rw [byte_view_ro_write]
    exact outputWrite
  have sourceFit1 : sourceOff + 1 < a1.size := by
    simpa [a1] using (show sourceOff + 1 < array.size by omega)
  let a2 := a1.set! (j + 1) (a1[sourceOff + 1]'sourceFit1)
  let h2 := Space.put h1 dest a2
  let l2 : Zlib.Inffast.L := { l1 with
    from_ := .ref dest (sourceOff + 2), out := .ref dest (j + 2) }
  have ⟨run2, packet2⟩ := packet1.copy1_view separate left
    (by rfl) output1 (by simpa [a1] using
      (show sourceOff + 1 < array.size by omega))
    (by rfl) outputPtr output1 writable1
    (by simpa [a1] using outputSize)
    (by omega : oo ≤ j + 1 ∧ j + 1 < oo + slow.left.toNat)
  change Zlib.Inffast.copy1 l1 h1 = .ok (l2, h2) at run2
  have output2 : Space.get h2 dest = some a2 :=
    byte_view_get_put output1 writable1 _
  have writable2 : Space.ro h2 dest = false := by
    change Space.ro (Space.put h1 dest a2) dest = false
    rw [byte_view_ro_write]
    exact writable1
  have sourceFit2 : sourceOff + 2 < a2.size := by
    simpa [a2, a1] using (show sourceOff + 2 < array.size by omega)
  let a3 := a2.set! (j + 2) (a2[sourceOff + 2]'sourceFit2)
  let h3 := Space.put h2 dest a3
  let l3 : Zlib.Inffast.L := { l2 with
    from_ := .ref dest (sourceOff + 3), out := .ref dest (j + 3) }
  have ⟨run3, packet3⟩ :=
    packet2.copy1_view (sourceOff := sourceOff + 2) separate left
    (by rfl) output2 (by simpa [a2, a1] using
      (show sourceOff + 2 < array.size by omega))
    (by rfl) outputPtr output2 writable2
    (by simpa [a2, a1] using outputSize)
    (by omega : oo ≤ j + 2 ∧ j + 2 < oo + slow.left.toNat)
  change Zlib.Inffast.copy1 l2 h2 = .ok (l3, h3) at run3
  let result : Zlib.Inffast.L := { l3 with len := fastLocal.len - 3 }
  have runBody : Zlib.Inffast.Proofs.body3 fastLocal h =
      .ok (result, h3) := by
    unfold Zlib.Inffast.Proofs.body3
    simp only [bind_app, run1, run2, run3, pure_app]
    simp [result, l3, l2, l1]
  have resultPacket : FastInputPacket h3 slow bs result :=
    ⟨packet3.source, packet3.cursor, packet3.hold, packet3.bits⟩
  have output3 : Space.get h3 dest = some a3 :=
    byte_view_get_put output2 writable2 _
  have writable3 : Space.ro h3 dest = false := by
    change Space.ro (Space.put h2 dest a3) dest = false
    rw [byte_view_ro_write]
    exact writable2
  have bytes3 : a3 =
      Zlib.Inffast.Proofs.cpyN 3 sourceOff j array := by
    rw [← copySameBytes_eq_cpyN]
    simp only [copySameBytes, a1, a2, a3,
      getElem!_pos array sourceOff (by omega),
      getElem!_pos a1 (sourceOff + 1) (by simpa [a1] using
        (show sourceOff + 1 < array.size by omega)),
      getElem!_pos a2 (sourceOff + 2) (by simpa [a2, a1] using
        (show sourceOff + 2 < array.size by omega))]
  exact ⟨result, h3, runBody, resultPacket,
    by simp [result, l3],
    by simp [result, l3],
    by simp [result],
    by simpa only [bytes3] using output3, writable3,
    by simpa only [bytes3] using output3,
    by simp [result, l3, l2, l1]⟩

/-- The actual three-copy body on general byte views. This is the source
fragment used by both match-copy loops in translated `inflate_fast`. -/
theorem FastInputPacket.copy3_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs fastLocal)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    {source dest : BRef} {saved array : Array UInt8}
    {sourceOff oo j : Nat}
    (fromPtr : fastLocal.from_ = .ref source sourceOff)
    (sourceGet : Space.get h source = some saved)
    (sourceRoom : sourceOff + 3 ≤ saved.size)
    (outPtr : fastLocal.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (outputRoom : oo ≤ j ∧ j + 3 ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.body3 fastLocal) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.from_ = .ref source (sourceOff + 3) ∧
      result.out = .ref dest (j + 3) ∧
      result.len = fastLocal.len - 3 ∧
      Space.get after dest = some
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN 3 sourceOff j array
        else
          Zlib.Inffast.Proofs.blitN saved 3 sourceOff j array) ∧
      Space.ro after dest = false ∧
      Space.get after source = some
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN 3 sourceOff j array
        else saved) ∧
      result = { fastLocal with
        from_ := .ref source (sourceOff + 3),
        out := .ref dest (j + 3),
        len := fastLocal.len - 3 } := by
  by_cases same : source = dest
  · subst source
    have arrays : saved = array :=
      Option.some.inj (sourceGet.symm.trans outputGet)
    subst saved
    simpa using packet.copy3_same_view separate left fromPtr
      sourceRoom outPtr outputPtr outputGet outputWrite
      outputSize outputRoom
  · simpa [same] using packet.copy3_distinct_view separate left same
      fromPtr sourceGet sourceRoom outPtr outputPtr outputGet
      outputWrite outputSize outputRoom

end Zlib.Inflate.Proofs
