import ZlibF.Proof.«inflate.c.fast-view-repeat-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The direct-output match repetition executes its mandatory first
three-byte copy and retains the default state through every later copy. -/
theorem FastInputPacket.do3_default_state_go
    {slow : IL} {bs : List UInt8} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (left : slow.left ≠ 0) :
    ∀ q (h : Heap) (l : Zlib.Inffast.L)
      (source dest : BRef) (saved output : Array UInt8)
      (sourceOff oo j fu rem : Nat),
      FastInputPacket h slow bs l →
      DefaultStateJ h r zs z s →
      DispatchBuffers h r slow bs →
      rem < 3 → l.len.toNat = 3 * (q + 1) + rem → q ≤ fu →
      l.from_ = .ref source sourceOff →
      Space.get h source = some saved →
      sourceOff + 3 * (q + 1) ≤ saved.size →
      l.out = .ref dest j →
      slow.put = .ref dest oo →
      Space.get h dest = some output →
      Space.ro h dest = false →
      oo + slow.left.toNat ≤ output.size →
      oo ≤ j ∧ j + 3 * (q + 1) ≤ oo + slow.left.toNat →
      ∃ result after array,
        cdoWhile.go Zlib.Inffast.Proofs.body3
          Zlib.Inffast.Proofs.cond3 (fu + 1) l h =
            .ok (result, after) ∧
        FastInputPacket after slow bs result ∧
        DefaultStateJ after r zs z s ∧
        DispatchBuffers after r slow bs ∧
        ByteViewSizes h after ∧
        after = Space.put h dest array ∧
        array.size = output.size ∧
        (∀ k, k < oo ∨ oo + slow.left.toNat ≤ k →
          array[k]? = output[k]?) := by
  intro q
  induction q with
  | zero =>
    intro h l source dest saved output sourceOff oo j fu rem
      packet invariant buffers small count _ fromPtr
      sourceGet sourceRoom outPtr outputPtr outputGet outputWrite
      outputSize outputRoom
    let updated := if source = dest then
      Zlib.Inffast.Proofs.cpyN 3 sourceOff j output
      else Zlib.Inffast.Proofs.blitN saved 3 sourceOff j output
    obtain ⟨next, middle, firstRun, nextPacket,
      nextInvariant, nextBuffers, firstSizes, middleEq, _, _, _,
      nextEq, _⟩ :=
      packet.copy3_default_loop_step invariant buffers left
        fromPtr sourceGet (by omega) outPtr outputPtr outputGet
        outputWrite outputSize
        (by omega : oo ≤ j ∧ j + 3 ≤ oo + slow.left.toNat)
    have nextSmall : next.len.toNat ≤ 2 := by
      rw [nextEq]
      simp only
      rw [Zlib.Inffast.Proofs.len_sub3 (by omega)]
      omega
    have condition := Zlib.Inffast.Proofs.cond3_false
      (l := next) nextSmall middle
    have run : cdoWhile.go Zlib.Inffast.Proofs.body3
        Zlib.Inffast.Proofs.cond3 (fu + 1) l h =
          .ok (next, middle) := by
      change Zlib.Inffast.Proofs.body3 l h =
        .ok (next, middle) at firstRun
      unfold cdoWhile.go
      simp only [bind_app, firstRun, condition]
      rfl
    have updatedSize : updated.size = output.size := by
      by_cases same : source = dest
      · simp [updated, same, Zlib.Inffast.Proofs.cpyN_size]
      · simp [updated, same, Zlib.Inffast.Proofs.blitN_size]
    have updatedFrame : ∀ k,
        k < oo ∨ oo + slow.left.toNat ≤ k →
          updated[k]? = output[k]? := by
      intro k outside
      have copyOutside : k < j ∨ j + 3 ≤ k := by omega
      by_cases same : source = dest
      · simpa [updated, same] using
          Zlib.Inffast.Proofs.cpyN_frame 3 sourceOff j output k
            copyOutside
      · simpa [updated, same] using
          Zlib.Inffast.Proofs.blitN_frame saved 3 sourceOff j
            output k copyOutside
    exact ⟨next, middle, updated, run, nextPacket,
      nextInvariant, nextBuffers, firstSizes, middleEq,
      updatedSize, updatedFrame⟩
  | succ q ih =>
    intro h l source dest saved output sourceOff oo j fu rem
      packet invariant buffers small count fuelBound fromPtr
      sourceGet sourceRoom outPtr outputPtr outputGet outputWrite
      outputSize outputRoom
    obtain ⟨nextFuel, rfl⟩ : ∃ n, fu = n + 1 :=
      ⟨fu - 1, by omega⟩
    let updated := if source = dest then
      Zlib.Inffast.Proofs.cpyN 3 sourceOff j output
      else Zlib.Inffast.Proofs.blitN saved 3 sourceOff j output
    obtain ⟨next, middle, firstRun, nextPacket,
      nextInvariant, nextBuffers, firstSizes, middleEq, updatedGet,
      updatedWrite, sourceNext, nextEq, _⟩ :=
      packet.copy3_default_loop_step invariant buffers left
        fromPtr sourceGet (by omega) outPtr outputPtr outputGet
        outputWrite outputSize
        (by omega : oo ≤ j ∧ j + 3 ≤ oo + slow.left.toNat)
    have updatedSize : updated.size = output.size := by
      by_cases same : source = dest
      · simp [updated, same, Zlib.Inffast.Proofs.cpyN_size]
      · simp [updated, same, Zlib.Inffast.Proofs.blitN_size]
    have updatedFrame : ∀ k,
        k < oo ∨ oo + slow.left.toNat ≤ k →
          updated[k]? = output[k]? := by
      intro k outside
      have copyOutside : k < j ∨ j + 3 ≤ k := by omega
      by_cases same : source = dest
      · simpa [updated, same] using
          Zlib.Inffast.Proofs.cpyN_frame 3 sourceOff j output k
            copyOutside
      · simpa [updated, same] using
          Zlib.Inffast.Proofs.blitN_frame saved 3 sourceOff j
            output k copyOutside
    have sourceSize : (if source = dest then updated else saved).size =
        saved.size := by
      by_cases same : source = dest
      · subst source
        have arrays : saved = output :=
          Option.some.inj (sourceGet.symm.trans outputGet)
        simp [updated, arrays, Zlib.Inffast.Proofs.cpyN_size]
      · simp [same]
    have nextCount : next.len.toNat = 3 * (q + 1) + rem := by
      rw [nextEq]
      simp only
      rw [Zlib.Inffast.Proofs.len_sub3 (by omega)]
      omega
    have condition := Zlib.Inffast.Proofs.cond3_true
      (l := next) (by omega : 3 ≤ next.len.toNat) middle
    obtain ⟨result, after, finalArray, restRun,
      resultPacket, finalInvariant, finalBuffers, restSizes,
      restHeap, restSize, restFrame⟩ :=
      ih middle next source dest
        (if source = dest then updated else saved) updated
        (sourceOff + 3) oo (j + 3) nextFuel rem
        nextPacket nextInvariant nextBuffers small nextCount
        (by omega) (by rw [nextEq]) sourceNext
        (by rw [sourceSize]; omega)
        (by rw [nextEq]) outputPtr updatedGet updatedWrite
        (by rw [updatedSize]; exact outputSize)
        (by omega)
    have run : cdoWhile.go Zlib.Inffast.Proofs.body3
        Zlib.Inffast.Proofs.cond3 (nextFuel + 1 + 1) l h =
          .ok (result, after) := by
      change Zlib.Inffast.Proofs.body3 l h =
        .ok (next, middle) at firstRun
      unfold cdoWhile.go
      simp only [bind_app, firstRun, condition, ite_true]
      exact restRun
    have finalHeap : after = Space.put h dest finalArray := by
      rw [restHeap, middleEq]
      exact byte_view_put_put outputGet outputWrite updated
        finalArray
    have finalSize : finalArray.size = output.size :=
      restSize.trans updatedSize
    have finalFrame : ∀ k,
        k < oo ∨ oo + slow.left.toNat ≤ k →
          finalArray[k]? = output[k]? := by
      intro k outside
      exact (restFrame k outside).trans (updatedFrame k outside)
    exact ⟨result, after, finalArray, run, resultPacket,
      finalInvariant, finalBuffers, firstSizes.trans restSizes,
      finalHeap, finalSize, finalFrame⟩

/-- The actual direct-output three-byte repetition preserves the default
state and caller buffers, and produces the exact sequential bytes. -/
theorem FastInputPacket.do3_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    {source dest : BRef} {saved output : Array UInt8}
    {sourceOff oo j q rem : Nat}
    (small : rem < 3)
    (count : l.len.toNat = 3 * (q + 1) + rem)
    (fromPtr : l.from_ = .ref source sourceOff)
    (sourceGet : Space.get h source = some saved)
    (sourceRoom : sourceOff + 3 * (q + 1) ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + 3 * (q + 1) ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (cdoWhile Zlib.Inffast.Proofs.body3
        Zlib.Inffast.Proofs.cond3 l) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      DefaultStateJ after r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      result = { l with
        from_ := .ref source (sourceOff + 3 * (q + 1)),
        out := .ref dest (j + 3 * (q + 1)),
        len := UInt32.ofNat rem } ∧
      Space.get after dest = some
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN (3 * (q + 1)) sourceOff j output
        else
          Zlib.Inffast.Proofs.blitN saved (3 * (q + 1)) sourceOff j output) ∧
      Space.ro after dest = false ∧
      after = Space.put h dest
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN (3 * (q + 1)) sourceOff j output
        else
          Zlib.Inffast.Proofs.blitN saved (3 * (q + 1)) sourceOff j output) ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  have fuelBound : q ≤ fuel - 1 := by
    have width := UInt32.toNat_lt l.len
    unfold fuel
    omega
  obtain ⟨result, after, finalArray, stateGo, resultPacket,
      finalInvariant, finalBuffers, sizes, heapEq,
      arraySize, arrayFrame⟩ :=
    FastInputPacket.do3_default_state_go
      (r := r) (zs := zs) (z := z) (s := s) left
      q h l source dest saved output sourceOff oo j
      (fuel - 1) rem packet invariant buffers small count
      fuelBound fromPtr sourceGet sourceRoom outPtr outputPtr
      outputGet outputWrite outputSize outputRoom
  have stateRun : C.run (cdoWhile Zlib.Inffast.Proofs.body3
      Zlib.Inffast.Proofs.cond3 l) h = .ok (result, after) := by
    change cdoWhile.go Zlib.Inffast.Proofs.body3
      Zlib.Inffast.Proofs.cond3 fuel l h = .ok (result, after)
    rw [← Zlib.Inffast.Proofs.fuel_pred]
    exact stateGo
  obtain ⟨viewResult, viewAfter, viewGo, _, viewEq,
      viewOutput, viewWrite, _⟩ :=
    packet.do3_view_go buffers.separate left outputPtr
      (q := q) (fu := fuel - 1) (r := rem) small count
      fuelBound fromPtr sourceGet sourceRoom outPtr outputGet
      outputWrite outputSize outputRoom
  have viewRun : C.run (cdoWhile Zlib.Inffast.Proofs.body3
      Zlib.Inffast.Proofs.cond3 l) h =
        .ok (viewResult, viewAfter) := by
    change cdoWhile.go Zlib.Inffast.Proofs.body3
      Zlib.Inffast.Proofs.cond3 fuel l h =
        .ok (viewResult, viewAfter)
    rw [← Zlib.Inffast.Proofs.fuel_pred]
    exact viewGo
  have sameRun : viewResult = result ∧ viewAfter = after := by
    rw [stateRun] at viewRun
    cases viewRun
    exact ⟨rfl, rfl⟩
  rcases sameRun with ⟨resultSame, afterSame⟩
  rw [resultSame] at viewEq
  rw [afterSame] at viewOutput viewWrite
  have arrayGet : Space.get after dest = some finalArray := by
    rw [heapEq]
    exact byte_view_get_put outputGet outputWrite _
  have arrayEq : finalArray =
      (if source = dest then
        Zlib.Inffast.Proofs.cpyN (3 * (q + 1)) sourceOff j output
      else
        Zlib.Inffast.Proofs.blitN saved (3 * (q + 1)) sourceOff j output) :=
    Option.some.inj (arrayGet.symm.trans viewOutput)
  have finalHeap : after = Space.put h dest
      (if source = dest then
        Zlib.Inffast.Proofs.cpyN (3 * (q + 1)) sourceOff j output
      else
        Zlib.Inffast.Proofs.blitN saved (3 * (q + 1)) sourceOff j output) := by
    rw [heapEq, arrayEq]
  have frame : BufferFrame h after (fun _ => False)
      [⟨slow.put, slow.left.toNat⟩] := by
    rw [heapEq]
    exact output_view_buffer_frame outputPtr outputGet outputWrite
      arraySize arrayFrame
  exact ⟨result, after, stateRun, resultPacket,
    finalInvariant, finalBuffers, sizes, viewEq,
    viewOutput, viewWrite, finalHeap, frame⟩

end Zlib.Inflate.Proofs
