import ZlibF.Proof.«inflate.c.fast-view-triple»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Two consecutive translated copy steps from a separate source object. -/
theorem FastInputPacket.copy2_distinct_view
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
    (sourceRoom : sourceOff + 2 ≤ saved.size)
    (outPtr : fastLocal.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (outputRoom : oo ≤ j ∧ j + 2 ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (do
        let one ← Zlib.Inffast.copy1 fastLocal
        Zlib.Inffast.copy1 one) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.from_ = .ref source (sourceOff + 2) ∧
      result.out = .ref dest (j + 2) ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.blitN saved 2 sourceOff j array) ∧
      Space.ro after dest = false ∧
      result = { fastLocal with
        from_ := .ref source (sourceOff + 2),
        out := .ref dest (j + 2) } := by
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
  have ⟨run2, packet2⟩ :=
    packet1.copy1_view (sourceOff := sourceOff + 1) separate left
    (by rfl) source1 (by omega) (by rfl) outputPtr output1
    writable1 (by simpa [a1] using outputSize)
    (by omega : oo ≤ j + 1 ∧ j + 1 < oo + slow.left.toNat)
  change Zlib.Inffast.copy1 l1 h1 = .ok (l2, h2) at run2
  have runBoth : C.run (do
      let one ← Zlib.Inffast.copy1 fastLocal
      Zlib.Inffast.copy1 one) h = .ok (l2, h2) := by
    change (Zlib.Inffast.copy1 fastLocal >>= Zlib.Inffast.copy1) h = _
    rw [bind_app, run1]
    exact run2
  have output2 : Space.get h2 dest = some a2 :=
    byte_view_get_put output1 writable1 _
  have writable2 : Space.ro h2 dest = false := by
    change Space.ro (Space.put h1 dest a2) dest = false
    rw [byte_view_ro_write]
    exact writable1
  have bytes2 : a2 =
      Zlib.Inffast.Proofs.blitN saved 2 sourceOff j array := by
    rw [← copyOtherBytes_eq_blitN]
    simp only [copyOtherBytes, a1, a2,
      getElem!_pos saved sourceOff (by omega),
      getElem!_pos saved (sourceOff + 1) (by omega)]
  exact ⟨l2, h2, runBoth, packet2,
    by simp [l2], by simp [l2],
    by simpa only [bytes2] using output2, writable2,
    by simp [l2, l1]⟩

/-- Two consecutive translated copy steps with sequential self-reference. -/
theorem FastInputPacket.copy2_same_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs fastLocal)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    {dest : BRef} {array : Array UInt8} {sourceOff oo j : Nat}
    (fromPtr : fastLocal.from_ = .ref dest sourceOff)
    (sourceRoom : sourceOff + 2 ≤ array.size)
    (outPtr : fastLocal.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (outputRoom : oo ≤ j ∧ j + 2 ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (do
        let one ← Zlib.Inffast.copy1 fastLocal
        Zlib.Inffast.copy1 one) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.from_ = .ref dest (sourceOff + 2) ∧
      result.out = .ref dest (j + 2) ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.cpyN 2 sourceOff j array) ∧
      Space.ro after dest = false ∧
      result = { fastLocal with
        from_ := .ref dest (sourceOff + 2),
        out := .ref dest (j + 2) } := by
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
  have ⟨run2, packet2⟩ :=
    packet1.copy1_view (sourceOff := sourceOff + 1) separate left
    (by rfl) output1 sourceFit1 (by rfl) outputPtr output1
    writable1 (by simpa [a1] using outputSize)
    (by omega : oo ≤ j + 1 ∧ j + 1 < oo + slow.left.toNat)
  change Zlib.Inffast.copy1 l1 h1 = .ok (l2, h2) at run2
  have runBoth : C.run (do
      let one ← Zlib.Inffast.copy1 fastLocal
      Zlib.Inffast.copy1 one) h = .ok (l2, h2) := by
    change (Zlib.Inffast.copy1 fastLocal >>= Zlib.Inffast.copy1) h = _
    rw [bind_app, run1]
    exact run2
  have output2 : Space.get h2 dest = some a2 :=
    byte_view_get_put output1 writable1 _
  have writable2 : Space.ro h2 dest = false := by
    change Space.ro (Space.put h1 dest a2) dest = false
    rw [byte_view_ro_write]
    exact writable1
  have bytes2 : a2 =
      Zlib.Inffast.Proofs.cpyN 2 sourceOff j array := by
    rw [← copySameBytes_eq_cpyN]
    simp only [copySameBytes, a1, a2,
      getElem!_pos array sourceOff (by omega),
      getElem!_pos a1 (sourceOff + 1) sourceFit1]
  exact ⟨l2, h2, runBoth, packet2,
    by simp [l2], by simp [l2],
    by simpa only [bytes2] using output2, writable2,
    by simp [l2, l1]⟩

/-- The two-byte tail copy on either public byte-view arrangement. -/
theorem FastInputPacket.copy2_view
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
    (sourceRoom : sourceOff + 2 ≤ saved.size)
    (outPtr : fastLocal.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (outputRoom : oo ≤ j ∧ j + 2 ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (do
        let one ← Zlib.Inffast.copy1 fastLocal
        Zlib.Inffast.copy1 one) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.from_ = .ref source (sourceOff + 2) ∧
      result.out = .ref dest (j + 2) ∧
      Space.get after dest = some
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN 2 sourceOff j array
        else
          Zlib.Inffast.Proofs.blitN saved 2 sourceOff j array) ∧
      Space.ro after dest = false ∧
      result = { fastLocal with
        from_ := .ref source (sourceOff + 2),
        out := .ref dest (j + 2) } := by
  by_cases same : source = dest
  · subst source
    have arrays : saved = array :=
      Option.some.inj (sourceGet.symm.trans outputGet)
    subst saved
    simpa using packet.copy2_same_view separate left fromPtr
      sourceRoom outPtr outputPtr outputGet outputWrite
      outputSize outputRoom
  · simpa [same] using packet.copy2_distinct_view separate left same
      fromPtr sourceGet sourceRoom outPtr outputPtr outputGet
      outputWrite outputSize outputRoom

/-- The actual short match suffix for zero, one or two remaining bytes. -/
theorem FastInputPacket.tailIf_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {fastLocal : Zlib.Inffast.L} {remaining : Nat}
    (packet : FastInputPacket h slow bs fastLocal)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (count : fastLocal.len.toNat = remaining)
    (small : remaining < 3)
    {source dest : BRef} {saved array : Array UInt8}
    {sourceOff oo j : Nat}
    (fromPtr : fastLocal.from_ = .ref source sourceOff)
    (sourceGet : Space.get h source = some saved)
    (sourceRoom : sourceOff + remaining ≤ saved.size)
    (outPtr : fastLocal.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (outputRoom : oo ≤ j ∧
      j + remaining ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.Proofs.tailIf fastLocal) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.from_ = .ref source (sourceOff + remaining) ∧
      result.out = .ref dest (j + remaining) ∧
      Space.get after dest = some
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN remaining sourceOff j array
        else
          Zlib.Inffast.Proofs.blitN saved remaining sourceOff j array) ∧
      Space.ro after dest = false ∧
      result = { fastLocal with
        from_ := .ref source (sourceOff + remaining),
        out := .ref dest (j + remaining) } := by
  have cases : remaining = 0 ∨ remaining = 1 ∨ remaining = 2 := by
    omega
  rcases cases with zero | one | two
  · rw [zero] at count sourceRoom outputRoom ⊢
    have lenZero : fastLocal.len = 0 :=
      UInt32.toNat_inj.mp (by simpa using count)
    refine ⟨fastLocal, h, ?_, packet, ?_, ?_, ?_, outputWrite, ?_⟩
    · simp [Zlib.Inffast.Proofs.tailIf, lenZero, C.run]
    · simpa only [Nat.add_zero] using fromPtr
    · simpa only [Nat.add_zero] using outPtr
    · simpa only [Zlib.Inffast.Proofs.cpyN,
        Zlib.Inffast.Proofs.blitN, ite_self] using outputGet
    · simpa only [Nat.add_zero, ← fromPtr, ← outPtr]
  · rw [one] at count sourceRoom outputRoom ⊢
    have lenOne : fastLocal.len = 1 :=
      UInt32.toNat_inj.mp (by simpa using count)
    let after := Space.put h dest (array.set! j saved[sourceOff])
    let next : Zlib.Inffast.L := { fastLocal with
      from_ := .ref source (sourceOff + 1),
      out := .ref dest (j + 1) }
    have ⟨copied, nextPacket⟩ := packet.copy1_view separate left
      fromPtr sourceGet (by omega) outPtr outputPtr outputGet
      outputWrite outputSize (by omega : oo ≤ j ∧
        j < oo + slow.left.toNat)
    change Zlib.Inffast.copy1 fastLocal h = .ok (next, after) at copied
    have run : Zlib.Inffast.Proofs.tailIf fastLocal h =
        .ok (next, after) := by
      unfold Zlib.Inffast.Proofs.tailIf
      simp [lenOne, bind_app, copied, next]
    have outputAfter : Space.get after dest =
        some (array.set! j saved[sourceOff]) :=
      byte_view_get_put outputGet outputWrite _
    have writableAfter : Space.ro after dest = false := by
      change Space.ro (Space.put h dest
        (array.set! j saved[sourceOff])) dest = false
      rw [byte_view_ro_write]
      exact outputWrite
    have sourceBound : sourceOff < saved.size := by omega
    have bytes : array.set! j saved[sourceOff] =
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN 1 sourceOff j array
        else
          Zlib.Inffast.Proofs.blitN saved 1 sourceOff j array) := by
      by_cases same : source = dest
      · subst source
        have arrays : saved = array :=
          Option.some.inj (sourceGet.symm.trans outputGet)
        subst saved
        simp [Zlib.Inffast.Proofs.cpyN,
          Array.getD_eq_getD_getElem?, sourceBound]
      · simp [same, Zlib.Inffast.Proofs.blitN,
          Array.getD_eq_getD_getElem?, sourceBound]
    exact ⟨next, after, run, nextPacket, by rfl, by rfl,
      by simpa only [bytes] using outputAfter, writableAfter,
      by rfl⟩
  · rw [two] at count sourceRoom outputRoom ⊢
    have lenTwo : fastLocal.len = 2 :=
      UInt32.toNat_inj.mp (by simpa using count)
    obtain ⟨result, after, both, nextPacket, fromFinal,
        outFinal, bytes, writable, resultEq⟩ := packet.copy2_view
      separate left fromPtr sourceGet sourceRoom outPtr outputPtr
      outputGet outputWrite outputSize outputRoom
    let firstHeap := Space.put h dest (array.set! j saved[sourceOff])
    let firstLocal : Zlib.Inffast.L := { fastLocal with
      from_ := .ref source (sourceOff + 1),
      out := .ref dest (j + 1) }
    have ⟨first, _⟩ := packet.copy1_view separate left
      fromPtr sourceGet (by omega) outPtr outputPtr outputGet
      outputWrite outputSize (by omega : oo ≤ j ∧
        j < oo + slow.left.toNat)
    change Zlib.Inffast.copy1 fastLocal h =
      .ok (firstLocal, firstHeap) at first
    have second : Zlib.Inffast.copy1 firstLocal firstHeap =
        .ok (result, after) := by
      change (Zlib.Inffast.copy1 fastLocal >>= Zlib.Inffast.copy1) h =
        .ok (result, after) at both
      rw [bind_app, first] at both
      exact both
    have run : Zlib.Inffast.Proofs.tailIf fastLocal h =
        .ok (result, after) := by
      unfold Zlib.Inffast.Proofs.tailIf
      have starts : (fastLocal.len != 0) = true := by simp [lenTwo]
      simp only [starts, ite_true, bind_app]
      rw [first]
      have another : (firstLocal.len > 1) = true := by
        simp [firstLocal, lenTwo]
      simp only [another, ite_true, bind_app]
      rw [second]
      rfl
    exact ⟨result, after, run, nextPacket, fromFinal,
      outFinal, bytes, writable, resultEq⟩

end Zlib.Inflate.Proofs
