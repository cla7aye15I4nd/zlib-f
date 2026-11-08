import ZlibF.Proof.«inflate.c.fast-view-tail»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated `while (len > 2)` loop on general byte views, when its
source is a separate byte object. The output may still share an object with
the caller's unread input in a disjoint interval. -/
theorem FastInputPacket.while3_distinct_go
    {slow : IL} {bs : List UInt8}
    {source dest : BRef} {saved : Array UInt8} {oo : Nat}
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (different : source ≠ dest)
    (outputPtr : slow.put = .ref dest oo) :
    ∀ q (h : Heap) (l : Zlib.Inffast.L)
      (output : Array UInt8) (fo j fu r : Nat),
      FastInputPacket h slow bs l →
      r < 3 → l.len.toNat = 3 * q + r → q ≤ fu →
      l.from_ = .ref source fo →
      Space.get h source = some saved →
      fo + 3 * q ≤ saved.size →
      l.out = .ref dest j →
      Space.get h dest = some output →
      Space.ro h dest = false →
      oo + slow.left.toNat ≤ output.size →
      oo ≤ j ∧ j + 3 * q ≤ oo + slow.left.toNat →
      ∃ result after,
        cwhile.go Zlib.Inffast.Proofs.cond3
          Zlib.Inffast.Proofs.body3 (fu + 1) l h =
            .ok (result, after) ∧
        FastInputPacket after slow bs result ∧
        result = { l with
          from_ := .ref source (fo + 3 * q),
          out := .ref dest (j + 3 * q),
          len := UInt32.ofNat r } ∧
        Space.get after dest = some
          (Zlib.Inffast.Proofs.blitN saved (3 * q) fo j output) ∧
        Space.ro after dest = false ∧
        Space.get after source = some saved := by
  intro q
  induction q with
  | zero =>
    intro h l output fo j fu r packet small count _ fromPtr
      sourceGet _ outPtr outputGet outputWrite _ _
    have condition := Zlib.Inffast.Proofs.cond3_false
      (l := l) (by omega : l.len.toNat ≤ 2) h
    have run : cwhile.go Zlib.Inffast.Proofs.cond3
        Zlib.Inffast.Proofs.body3 (fu + 1) l h = .ok (l, h) := by
      unfold cwhile.go
      rw [bind_app, condition]
      rfl
    have lenEq : l.len = UInt32.ofNat r := by
      apply UInt32.toNat_inj.mp
      rw [count]
      simp [UInt32.toNat_ofNat]
      omega
    have exactResult : l = { l with
        from_ := .ref source (fo + 3 * 0),
        out := .ref dest (j + 3 * 0),
        len := UInt32.ofNat r } := by
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [← fromPtr, ← outPtr, ← lenEq]
    exact ⟨l, h, run, packet, exactResult,
      by simpa only [Nat.mul_zero, Zlib.Inffast.Proofs.blitN] using outputGet,
      outputWrite, sourceGet⟩
  | succ q ih =>
    intro h l output fo j fu r packet small count fuelBound fromPtr
      sourceGet sourceRoom outPtr outputGet outputWrite outputSize
      outputRoom
    obtain ⟨fu, rfl⟩ : ∃ nextFuel, fu = nextFuel + 1 :=
      ⟨fu - 1, by omega⟩
    have condition := Zlib.Inffast.Proofs.cond3_true
      (l := l) (by omega : 3 ≤ l.len.toNat) h
    obtain ⟨next, heap1, copied, packet1, nextFrom, nextOut,
        nextLen, nextOutput, nextWrite, nextSource, nextEq⟩ :=
      packet.copy3_distinct_view separate left different
        fromPtr sourceGet (by omega) outPtr outputPtr
        outputGet outputWrite outputSize
        (by omega : oo ≤ j ∧ j + 3 ≤ oo + slow.left.toNat)
    change Zlib.Inffast.Proofs.body3 l h =
      .ok (next, heap1) at copied
    have nextCount : next.len.toNat = 3 * q + r := by
      rw [nextLen, Zlib.Inffast.Proofs.len_sub3 (by omega)]
      omega
    obtain ⟨result, after, rest, resultPacket, resultEq,
        resultOutput, resultWrite, resultSource⟩ :=
      ih heap1 next
        (Zlib.Inffast.Proofs.blitN saved 3 fo j output)
        (fo + 3) (j + 3) fu r packet1 small nextCount
        (by omega) nextFrom nextSource (by omega)
        nextOut nextOutput nextWrite
        (by simpa only [Zlib.Inffast.Proofs.blitN_size]
          using outputSize)
        (by omega)
    have run : cwhile.go Zlib.Inffast.Proofs.cond3
        Zlib.Inffast.Proofs.body3 (fu + 1 + 1) l h =
          .ok (result, after) := by
      unfold cwhile.go
      rw [bind_app, condition]
      simp only [ite_true, bind_app]
      rw [copied]
      exact rest
    have finalEq : result = { l with
        from_ := .ref source (fo + 3 * (q + 1)),
        out := .ref dest (j + 3 * (q + 1)),
        len := UInt32.ofNat r } := by
      rw [resultEq, nextEq]
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
    have finalOutput : Space.get after dest = some
        (Zlib.Inffast.Proofs.blitN saved (3 * (q + 1))
          fo j output) := by
      simpa only [show 3 * (q + 1) = 3 + 3 * q by omega,
        Zlib.Inffast.Proofs.blitN_add] using resultOutput
    exact ⟨result, after, run, resultPacket, finalEq,
      finalOutput, resultWrite, resultSource⟩

/-- The same translated loop for sequential self-reference in the output
byte object, including overlapping back-references. -/
theorem FastInputPacket.while3_same_go
    {slow : IL} {bs : List UInt8}
    {dest : BRef} {oo : Nat}
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (outputPtr : slow.put = .ref dest oo) :
    ∀ q (h : Heap) (l : Zlib.Inffast.L)
      (output : Array UInt8) (fo j fu r : Nat),
      FastInputPacket h slow bs l →
      r < 3 → l.len.toNat = 3 * q + r → q ≤ fu →
      l.from_ = .ref dest fo →
      fo + 3 * q ≤ output.size →
      l.out = .ref dest j →
      Space.get h dest = some output →
      Space.ro h dest = false →
      oo + slow.left.toNat ≤ output.size →
      oo ≤ j ∧ j + 3 * q ≤ oo + slow.left.toNat →
      ∃ result after,
        cwhile.go Zlib.Inffast.Proofs.cond3
          Zlib.Inffast.Proofs.body3 (fu + 1) l h =
            .ok (result, after) ∧
        FastInputPacket after slow bs result ∧
        result = { l with
          from_ := .ref dest (fo + 3 * q),
          out := .ref dest (j + 3 * q),
          len := UInt32.ofNat r } ∧
        Space.get after dest = some
          (Zlib.Inffast.Proofs.cpyN (3 * q) fo j output) ∧
        Space.ro after dest = false := by
  intro q
  induction q with
  | zero =>
    intro h l output fo j fu r packet small count _ fromPtr
      _ outPtr outputGet outputWrite _ _
    have condition := Zlib.Inffast.Proofs.cond3_false
      (l := l) (by omega : l.len.toNat ≤ 2) h
    have run : cwhile.go Zlib.Inffast.Proofs.cond3
        Zlib.Inffast.Proofs.body3 (fu + 1) l h = .ok (l, h) := by
      unfold cwhile.go
      rw [bind_app, condition]
      rfl
    have lenEq : l.len = UInt32.ofNat r := by
      apply UInt32.toNat_inj.mp
      rw [count]
      simp [UInt32.toNat_ofNat]
      omega
    have exactResult : l = { l with
        from_ := .ref dest (fo + 3 * 0),
        out := .ref dest (j + 3 * 0),
        len := UInt32.ofNat r } := by
      simp only [Nat.mul_zero, Nat.add_zero]
      rw [← fromPtr, ← outPtr, ← lenEq]
    exact ⟨l, h, run, packet, exactResult,
      by simpa only [Nat.mul_zero, Zlib.Inffast.Proofs.cpyN] using outputGet,
      outputWrite⟩
  | succ q ih =>
    intro h l output fo j fu r packet small count fuelBound fromPtr
      sourceRoom outPtr outputGet outputWrite outputSize outputRoom
    obtain ⟨fu, rfl⟩ : ∃ nextFuel, fu = nextFuel + 1 :=
      ⟨fu - 1, by omega⟩
    have condition := Zlib.Inffast.Proofs.cond3_true
      (l := l) (by omega : 3 ≤ l.len.toNat) h
    obtain ⟨next, heap1, copied, packet1, nextFrom, nextOut,
        nextLen, nextOutput, nextWrite, _, nextEq⟩ :=
      packet.copy3_same_view separate left fromPtr
        (by omega) outPtr outputPtr outputGet outputWrite
        outputSize
        (by omega : oo ≤ j ∧ j + 3 ≤ oo + slow.left.toNat)
    change Zlib.Inffast.Proofs.body3 l h =
      .ok (next, heap1) at copied
    have nextCount : next.len.toNat = 3 * q + r := by
      rw [nextLen, Zlib.Inffast.Proofs.len_sub3 (by omega)]
      omega
    obtain ⟨result, after, rest, resultPacket, resultEq,
        resultOutput, resultWrite⟩ :=
      ih heap1 next
        (Zlib.Inffast.Proofs.cpyN 3 fo j output)
        (fo + 3) (j + 3) fu r packet1 small nextCount
        (by omega) nextFrom
        (by simpa only [Zlib.Inffast.Proofs.cpyN_size]
          using (show fo + 3 + 3 * q ≤ output.size by omega))
        nextOut nextOutput nextWrite
        (by simpa only [Zlib.Inffast.Proofs.cpyN_size]
          using outputSize)
        (by omega)
    have run : cwhile.go Zlib.Inffast.Proofs.cond3
        Zlib.Inffast.Proofs.body3 (fu + 1 + 1) l h =
          .ok (result, after) := by
      unfold cwhile.go
      rw [bind_app, condition]
      simp only [ite_true, bind_app]
      rw [copied]
      exact rest
    have finalEq : result = { l with
        from_ := .ref dest (fo + 3 * (q + 1)),
        out := .ref dest (j + 3 * (q + 1)),
        len := UInt32.ofNat r } := by
      rw [resultEq, nextEq]
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
    have finalOutput : Space.get after dest = some
        (Zlib.Inffast.Proofs.cpyN (3 * (q + 1))
          fo j output) := by
      simpa only [show 3 * (q + 1) = 3 + 3 * q by omega,
        Zlib.Inffast.Proofs.cpyN_add] using resultOutput
    exact ⟨result, after, run, resultPacket, finalEq,
      finalOutput, resultWrite⟩

/-- The actual three-byte repetition loop on either general byte-view
arrangement. Its source object remains readable after each iteration. -/
theorem FastInputPacket.while3_view_go
    {slow : IL} {bs : List UInt8}
    {source dest : BRef} {saved : Array UInt8} {oo : Nat}
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (outputPtr : slow.put = .ref dest oo)
    {q : Nat} {h : Heap} {l : Zlib.Inffast.L}
    {output : Array UInt8} {fo j fu r : Nat}
    (packet : FastInputPacket h slow bs l)
    (small : r < 3) (count : l.len.toNat = 3 * q + r)
    (fuelBound : q ≤ fu)
    (fromPtr : l.from_ = .ref source fo)
    (sourceGet : Space.get h source = some saved)
    (sourceRoom : fo + 3 * q ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + 3 * q ≤ oo + slow.left.toNat) :
    ∃ result after,
      cwhile.go Zlib.Inffast.Proofs.cond3
        Zlib.Inffast.Proofs.body3 (fu + 1) l h =
          .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result = { l with
        from_ := .ref source (fo + 3 * q),
        out := .ref dest (j + 3 * q),
        len := UInt32.ofNat r } ∧
      Space.get after dest = some
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN (3 * q) fo j output
        else
          Zlib.Inffast.Proofs.blitN saved (3 * q) fo j output) ∧
      Space.ro after dest = false ∧
      Space.get after source = some
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN (3 * q) fo j output
        else saved) := by
  by_cases same : source = dest
  · subst source
    have arrays : saved = output :=
      Option.some.inj (sourceGet.symm.trans outputGet)
    subst saved
    obtain ⟨result, after, run, packet1, resultEq,
        bytes, writable⟩ :=
      FastInputPacket.while3_same_go separate left outputPtr
        q h l output fo j fu r packet small count fuelBound
        fromPtr sourceRoom outPtr outputGet outputWrite outputSize
        outputRoom
    refine ⟨result, after, run, packet1, resultEq,
      ?_, writable, ?_⟩
    · simpa using bytes
    · simpa using bytes
  · obtain ⟨result, after, run, packet1, resultEq,
        bytes, writable, sourceFinal⟩ :=
      FastInputPacket.while3_distinct_go separate left same outputPtr
        q h l output fo j fu r packet small count fuelBound
        fromPtr sourceGet sourceRoom outPtr outputGet outputWrite
        outputSize outputRoom
    refine ⟨result, after, run, packet1, resultEq,
      ?_, writable, ?_⟩
    · simpa [same] using bytes
    · simpa [same] using sourceFinal

/-- The complete translated window-source copy suffix on general byte views:
the three-byte loop followed by its zero-, one- or two-byte tail. -/
theorem FastInputPacket.tailW_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {n : Nat}
    (packet : FastInputPacket h slow bs l)
    (count : l.len.toNat = n)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    {source dest : BRef} {saved output : Array UInt8}
    {fo oo j : Nat}
    (fromPtr : l.from_ = .ref source fo)
    (sourceGet : Space.get h source = some saved)
    (sourceRoom : fo + n ≤ saved.size)
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
      result = { l with
        from_ := .ref source (fo + n),
        out := .ref dest (j + n),
        len := UInt32.ofNat (n % 3) } ∧
      Space.get after dest = some
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN n fo j output
        else
          Zlib.Inffast.Proofs.blitN saved n fo j output) ∧
      Space.ro after dest = false := by
  let q := n / 3
  let r := n % 3
  have small : r < 3 := by dsimp [r]; omega
  have split : n = 3 * q + r := by dsimp [q, r]; omega
  have fuelBound : q ≤ fuel - 1 := by
    have limit := UInt32.toNat_lt l.len
    unfold q fuel
    omega
  obtain ⟨loop, heap1, loopRun, packet1, loopEq,
      loopOutput, loopWritable, loopSource⟩ :=
    packet.while3_view_go separate left outputPtr
      (q := q) (fu := fuel - 1) (r := r) small
      (by omega : l.len.toNat = 3 * q + r) fuelBound
      fromPtr sourceGet (by omega) outPtr outputGet outputWrite
      outputSize (by omega)
  have whileRun : cwhile Zlib.Inffast.Proofs.cond3
      Zlib.Inffast.Proofs.body3 l h = .ok (loop, heap1) := by
    unfold cwhile
    simpa only [Zlib.Inffast.Proofs.fuel_pred] using loopRun
  let mid := if source = dest then
    Zlib.Inffast.Proofs.cpyN (3 * q) fo j output
    else Zlib.Inffast.Proofs.blitN saved (3 * q) fo j output
  let srcMid := if source = dest then
    Zlib.Inffast.Proofs.cpyN (3 * q) fo j output else saved
  have midSize : mid.size = output.size := by
    by_cases same : source = dest
    · simp [mid, same, Zlib.Inffast.Proofs.cpyN_size]
    · simp [mid, same, Zlib.Inffast.Proofs.blitN_size]
  have srcRoom : fo + 3 * q + r ≤ srcMid.size := by
    by_cases same : source = dest
    · rw [same] at sourceGet
      have arrays : saved = output :=
        Option.some.inj (sourceGet.symm.trans outputGet)
      subst saved
      simp only [srcMid, same, ite_true,
        Zlib.Inffast.Proofs.cpyN_size]
      omega
    · simp only [srcMid, same, ite_false]
      rw [split] at sourceRoom
      simpa only [Nat.add_assoc] using sourceRoom
  have tailCount : loop.len.toNat = r := by
    rw [loopEq]
    simp [UInt32.toNat_ofNat]
    omega
  obtain ⟨result, after, tailRun, resultPacket, fromFinal,
      outFinal, tailOutput, resultWritable, tailEq⟩ :=
    packet1.tailIf_view separate left tailCount small
      (by simp [loopEq])
      loopSource srcRoom
      (by simp [loopEq]) outputPtr loopOutput loopWritable
      (by rw [midSize]; exact outputSize)
      (by omega : oo ≤ j + 3 * q ∧
        j + 3 * q + r ≤ oo + slow.left.toNat)
  have run : Zlib.Inffast.Proofs.tailW l h =
      .ok (result, after) := by
    unfold Zlib.Inffast.Proofs.tailW
    rw [bind_app, whileRun]
    exact tailRun
  have resultEq : result = { l with
      from_ := .ref source (fo + n),
      out := .ref dest (j + n),
      len := UInt32.ofNat (n % 3) } := by
    have sourceOffEq : fo + 3 * q + r = fo + n := by omega
    have outputOffEq : j + 3 * q + r = j + n := by omega
    rw [tailEq, loopEq]
    simp [sourceOffEq, outputOffEq, r]
  have bytes : Space.get after dest = some
      (if source = dest then
        Zlib.Inffast.Proofs.cpyN n fo j output
      else
        Zlib.Inffast.Proofs.blitN saved n fo j output) := by
    by_cases same : source = dest
    · simpa [mid, srcMid, same, split,
        Zlib.Inffast.Proofs.cpyN_add] using tailOutput
    · simpa [mid, srcMid, same, split,
        Zlib.Inffast.Proofs.blitN_add] using tailOutput
  exact ⟨result, after, run, resultPacket, resultEq,
    bytes, resultWritable⟩

end Zlib.Inflate.Proofs
