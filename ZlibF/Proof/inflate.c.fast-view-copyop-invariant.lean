import ZlibF.Proof.«inflate.c.fast-view-window-short-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Each repeated window-source `copyOp` byte retains the default decoder
state, caller buffers, and all bytes outside the output interval. -/
theorem FastInputPacket.copyOp_distinct_default_state_go
    {slow : IL} {bs : List UInt8} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    {source dest : BRef} {oo : Nat}
    (left : slow.left ≠ 0)
    (different : source ≠ dest)
    (outputPtr : slow.put = .ref dest oo) :
    ∀ k (h : Heap) (l : Zlib.Inffast.L)
      (saved output : Array UInt8) (sourceOff j fu : Nat),
      FastInputPacket h slow bs l →
      DefaultStateJ h r zs z s →
      DispatchBuffers h r slow bs →
      l.op.toNat = k + 1 → k ≤ fu →
      l.from_ = .ref source sourceOff →
      Space.get h source = some saved →
      sourceOff + k + 1 ≤ saved.size →
      l.out = .ref dest j →
      Space.get h dest = some output →
      Space.ro h dest = false →
      oo + slow.left.toNat ≤ output.size →
      oo ≤ j ∧ j + k + 1 ≤ oo + slow.left.toNat →
      ∃ result after array,
        cdoWhile.go Zlib.Inffast.copy1
          (fun current => let op := current.op - 1;
            pure (op != 0, { current with op }))
          (fu + 1) l h = .ok (result, after) ∧
        FastInputPacket after slow bs result ∧
        DefaultStateJ after r zs z s ∧
        DispatchBuffers after r slow bs ∧
        ByteViewSizes h after ∧
        after = Space.put h dest array ∧
        array.size = output.size ∧
        (∀ index, index < oo ∨ oo + slow.left.toNat ≤ index →
          array[index]? = output[index]?) := by
  intro k
  induction k with
  | zero =>
    intro h l saved output sourceOff j fu packet invariant buffers
      count _ fromPtr sourceGet sourceRoom outPtr outputGet
      outputWrite outputSize outputRoom
    let updated := output.set! j saved[sourceOff]
    let middle := Space.put h dest updated
    let first : Zlib.Inffast.L := { l with
      from_ := .ref source (sourceOff + 1),
      out := .ref dest (j + 1) }
    obtain ⟨firstRun, firstPacket, firstInvariant,
      firstBuffers, firstSizes, _, outsideByte, _⟩ :=
      packet.copy1_default_state invariant buffers left
        fromPtr sourceGet (by omega) outPtr outputPtr outputGet
        outputWrite outputSize
        (by omega : oo ≤ j ∧ j < oo + slow.left.toNat)
    change Zlib.Inffast.copy1 l h = .ok (first, middle)
      at firstRun
    have zeroOp : l.op - 1 = 0 := by
      apply UInt32.toNat_inj.mp
      rw [Zlib.Inffast.Proofs.u32_sub_one_toNat (by omega)]
      simp [count]
    let result : Zlib.Inffast.L := { first with op := 0 }
    have run : cdoWhile.go Zlib.Inffast.copy1
        (fun current => let op := current.op - 1;
          pure (op != 0, { current with op }))
        (fu + 1) l h = .ok (result, middle) := by
      unfold cdoWhile.go
      simp only [bind_app, firstRun]
      simp [first, result, zeroOp]
    have updatedSize : updated.size = output.size := by
      simp [updated]
    have updatedOutside : ∀ index,
        index < oo ∨ oo + slow.left.toNat ≤ index →
          updated[index]? = output[index]? := by
      intro index outside
      exact outsideByte index (by omega)
    exact ⟨result, middle, updated, run,
      firstPacket.with_op 0, firstInvariant, firstBuffers,
      firstSizes, rfl, updatedSize, updatedOutside⟩
  | succ k ih =>
    intro h l saved output sourceOff j fu packet invariant buffers
      count fuelBound fromPtr sourceGet sourceRoom outPtr outputGet
      outputWrite outputSize outputRoom
    obtain ⟨nextFuel, rfl⟩ : ∃ n, fu = n + 1 :=
      ⟨fu - 1, by omega⟩
    let updated := output.set! j saved[sourceOff]
    let middle := Space.put h dest updated
    let first : Zlib.Inffast.L := { l with
      from_ := .ref source (sourceOff + 1),
      out := .ref dest (j + 1) }
    obtain ⟨firstRun, firstPacket, firstInvariant,
      firstBuffers, firstSizes, updatedGet, outsideByte, _⟩ :=
      packet.copy1_default_state invariant buffers left
        fromPtr sourceGet (by omega) outPtr outputPtr outputGet
        outputWrite outputSize
        (by omega : oo ≤ j ∧ j < oo + slow.left.toNat)
    change Zlib.Inffast.copy1 l h = .ok (first, middle)
      at firstRun
    let next : Zlib.Inffast.L := { first with op := l.op - 1 }
    have sourceNext : Space.get middle source = some saved := by
      change Space.get (Space.put h dest updated) source = _
      rw [byte_view_get_put_ne h different]
      exact sourceGet
    have writeNext : Space.ro middle dest = false := by
      change Space.ro (Space.put h dest updated) dest = false
      rw [byte_view_ro_write]
      exact outputWrite
    have nextCount : next.op.toNat = k + 1 := by
      change (l.op - 1).toNat = k + 1
      rw [Zlib.Inffast.Proofs.u32_sub_one_toNat (by omega)]
      omega
    have nextPacket : FastInputPacket middle slow bs next :=
      firstPacket.with_op (l.op - 1)
    obtain ⟨result, after, finalArray, restRun,
      resultPacket, finalInvariant, finalBuffers, restSizes,
      restHeap, restSize, restOutside⟩ :=
      ih middle next saved updated (sourceOff + 1) (j + 1)
        nextFuel nextPacket firstInvariant firstBuffers nextCount
        (by omega) (by rfl) sourceNext (by omega)
        (by rfl) updatedGet writeNext
        (by simpa [updated] using outputSize) (by omega)
    have continues : (l.op - 1 != 0) = true :=
      Zlib.Inffast.Proofs.u32_sub_one_ne (by omega)
    have run : cdoWhile.go Zlib.Inffast.copy1
        (fun current => let op := current.op - 1;
          pure (op != 0, { current with op }))
        (nextFuel + 1 + 1) l h = .ok (result, after) := by
      unfold cdoWhile.go
      simp only [bind_app, firstRun]
      simp [first, next, continues, restRun]
    have finalHeap : after = Space.put h dest finalArray := by
      rw [restHeap]
      change Space.put (Space.put h dest updated) dest finalArray =
        Space.put h dest finalArray
      exact byte_view_put_put outputGet outputWrite updated finalArray
    have finalSize : finalArray.size = output.size := by
      rw [restSize]
      simp [updated]
    have finalOutside : ∀ index,
        index < oo ∨ oo + slow.left.toNat ≤ index →
          finalArray[index]? = output[index]? := by
      intro index outside
      exact (restOutside index outside).trans
        (outsideByte index (by omega))
    exact ⟨result, after, finalArray, run, resultPacket,
      finalInvariant, finalBuffers, firstSizes.trans restSizes,
      finalHeap, finalSize, finalOutside⟩

/-- The complete translated window-source `copyOp` repetition is safe on
the default state, and writes exactly its stated output bytes. -/
theorem FastInputPacket.copyOp_distinct_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
    (left : slow.left ≠ 0)
    {source dest : BRef} (different : source ≠ dest)
    {saved output : Array UInt8} {sourceOff oo j : Nat}
    (fromPtr : l.from_ = .ref source sourceOff)
    (sourceGet : Space.get h source = some saved)
    (sourceRoom : sourceOff + l.op.toNat ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.op.toNat ≤ oo + slow.left.toNat)
    (positive : 1 ≤ l.op.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.copyOp l) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      DefaultStateJ after r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      result = { l with
        from_ := .ref source (sourceOff + l.op.toNat),
        out := .ref dest (j + l.op.toNat), op := 0 } ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.blitN saved l.op.toNat
          sourceOff j output) ∧
      Space.ro after dest = false ∧
      after = Space.put h dest
        (Zlib.Inffast.Proofs.blitN saved l.op.toNat
          sourceOff j output) ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  obtain ⟨k, count⟩ : ∃ k, l.op.toNat = k + 1 :=
    ⟨l.op.toNat - 1, by omega⟩
  have fuelBound : k ≤ fuel - 1 := by
    have width := UInt32.toNat_lt l.op
    unfold fuel
    omega
  obtain ⟨result, after, finalArray, stateGo,
      resultPacket, finalInvariant, finalBuffers, sizes,
      heapEq, arraySize, arrayOutside⟩ :=
    FastInputPacket.copyOp_distinct_default_state_go
      (r := r) (zs := zs) (z := z) (s := s)
      left different outputPtr k h l saved output sourceOff j
      (fuel - 1) packet invariant buffers count fuelBound
      fromPtr sourceGet (by omega) outPtr outputGet outputWrite
      outputSize (by omega)
  have stateRun : C.run (Zlib.Inffast.copyOp l) h =
      .ok (result, after) := by
    change Zlib.Inffast.copyOp l h = .ok (result, after)
    unfold Zlib.Inffast.copyOp cdoWhile
    simpa only [Zlib.Inffast.Proofs.fuel_pred] using stateGo
  obtain ⟨viewResult, viewAfter, viewRun, _, _, _, _,
      viewOutput, viewWrite, _, viewEq⟩ :=
    packet.copyOp_distinct_view buffers.separate left different
      fromPtr sourceGet sourceRoom outPtr outputPtr outputGet
      outputWrite outputSize outputRoom positive
  have sameRun : viewResult = result ∧ viewAfter = after :=
    Prod.mk.inj (Except.ok.inj (viewRun.symm.trans stateRun))
  rw [sameRun.1] at viewEq
  rw [sameRun.2] at viewOutput viewWrite
  have arrayGet : Space.get after dest = some finalArray := by
    rw [heapEq]
    exact byte_view_get_put outputGet outputWrite finalArray
  have arrayEq : finalArray =
      Zlib.Inffast.Proofs.blitN saved l.op.toNat sourceOff j output := by
    apply Option.some.inj
    rw [copyOtherBytes_eq_blitN] at viewOutput
    exact arrayGet.symm.trans viewOutput
  have finalHeap : after = Space.put h dest
      (Zlib.Inffast.Proofs.blitN saved l.op.toNat
        sourceOff j output) := by
    rw [heapEq, arrayEq]
  have frame : BufferFrame h after (fun _ => False)
      [⟨slow.put, slow.left.toNat⟩] := by
    rw [heapEq]
    exact output_view_buffer_frame outputPtr outputGet outputWrite
      arraySize arrayOutside
  exact ⟨result, after, stateRun, resultPacket,
    finalInvariant, finalBuffers, sizes, viewEq,
    by simpa [copyOtherBytes_eq_blitN] using viewOutput,
    viewWrite, finalHeap, frame⟩

end Zlib.Inflate.Proofs
