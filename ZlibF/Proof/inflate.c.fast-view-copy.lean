import ZlibF.Proof.«inflate.c.fast-entry»
import ZlibF.Proof.«inffast.c.copy»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The exact forward copy when the source is a separate byte object. -/
def copyOtherBytes (saved : Array UInt8) (sourceOff : Nat)
    (output : Array UInt8) (j : Nat) : Nat → Array UInt8
  | 0 => output
  | n + 1 => copyOtherBytes saved (sourceOff + 1)
      (output.set! j saved[sourceOff]!) (j + 1) n

/-- The exact sequential copy when source and output share a byte object. -/
def copySameBytes (output : Array UInt8) (sourceOff j : Nat) :
    Nat → Array UInt8
  | 0 => output
  | n + 1 => copySameBytes (output.set! j output[sourceOff]!)
      (sourceOff + 1) (j + 1) n

/-- The general-view proof uses the same pure copying function as the
previous raw-buffer fast decoder proof. -/
theorem copyOtherBytes_eq_blitN :
    ∀ n saved sourceOff output j,
      copyOtherBytes saved sourceOff output j n =
        Zlib.Inffast.Proofs.blitN saved n sourceOff j output
  | 0, _, _, _, _ => rfl
  | n + 1, saved, sourceOff, output, j => by
      simp only [copyOtherBytes, Zlib.Inffast.Proofs.blitN,
        Array.getElem!_eq_getD]
      exact copyOtherBytes_eq_blitN n saved (sourceOff + 1)
        (output.set! j (saved.getD sourceOff 0)) (j + 1)

/-- Sequential overlapping copies use the old decoder's `cpyN` model. -/
theorem copySameBytes_eq_cpyN :
    ∀ n output sourceOff j,
      copySameBytes output sourceOff j n =
        Zlib.Inffast.Proofs.cpyN n sourceOff j output
  | 0, _, _, _ => rfl
  | n + 1, output, sourceOff, j => by
      simp only [copySameBytes, Zlib.Inffast.Proofs.cpyN,
        Array.getElem!_eq_getD]
      exact copySameBytes_eq_cpyN n
        (output.set! j (output.getD sourceOff 0))
        (sourceOff + 1) (j + 1)

/-- The translated `copyOp` loop terminates on a general writable output
view when its readable source is a different byte object. The public input
may still share the output object in a disjoint interval. Every actual copy
step retains the synchronized unread-input packet. -/
theorem FastInputPacket.copyOp_distinct_view
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
    (sourceRoom : sourceOff + fastLocal.op.toNat ≤ saved.size)
    (outPtr : fastLocal.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (outputRoom : oo ≤ j ∧
      j + fastLocal.op.toNat ≤ oo + slow.left.toNat)
    (positive : 1 ≤ fastLocal.op.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.copyOp fastLocal) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧ result.op = 0 ∧
      result.from_ = .ref source
        (sourceOff + fastLocal.op.toNat) ∧
      result.out = .ref dest (j + fastLocal.op.toNat) ∧
      Space.get after dest = some
        (copyOtherBytes saved sourceOff array j fastLocal.op.toNat) ∧
      Space.ro after dest = false ∧
      Space.get after source = some saved ∧
      result = { fastLocal with
        from_ := .ref source (sourceOff + fastLocal.op.toNat),
        out := .ref dest (j + fastLocal.op.toNat),
        op := 0 } := by
  let body := Zlib.Inffast.copy1
  let cond : Zlib.Inffast.L → M (Bool × Zlib.Inffast.L) :=
    fun l => let op := l.op - 1; pure (op != 0, { l with op })
  have go : ∀ k fu (heap : Heap) (current : Zlib.Inffast.L)
      (output : Array UInt8) (fo oj : Nat),
      current.op.toNat = k + 1 → k ≤ fu →
      FastInputPacket heap slow bs current →
      current.from_ = .ref source fo →
      Space.get heap source = some saved →
      fo + k + 1 ≤ saved.size →
      current.out = .ref dest oj →
      Space.get heap dest = some output →
      Space.ro heap dest = false →
      output.size = array.size →
      oo ≤ oj → oj + k + 1 ≤ oo + slow.left.toNat →
      ∃ final heapFinal,
        cdoWhile.go body cond (fu + 1) current heap =
          .ok (final, heapFinal) ∧
        FastInputPacket heapFinal slow bs final ∧ final.op = 0 ∧
        final.from_ = .ref source (fo + k + 1) ∧
        final.out = .ref dest (oj + k + 1) ∧
        Space.get heapFinal dest = some
          (copyOtherBytes saved fo output oj (k + 1)) ∧
        Space.ro heapFinal dest = false ∧
        Space.get heapFinal source = some saved ∧
        final = { current with
          from_ := .ref source (fo + k + 1),
          out := .ref dest (oj + k + 1), op := 0 } := by
    intro k
    induction k with
    | zero =>
      intro fu heap current output fo oj count _ currentPacket
        sourcePtr currentSource sourceFit currentOut currentOutput
        currentWrite currentSize lower upper
      have inside : oo ≤ oj ∧ oj < oo + slow.left.toNat :=
        ⟨lower, by omega⟩
      have fullSize : oo + slow.left.toNat ≤ output.size := by
        rw [currentSize]
        exact outputSize
      have ⟨copyRun, copied⟩ := currentPacket.copy1_view
        separate left sourcePtr currentSource (by omega)
        currentOut outputPtr currentOutput currentWrite fullSize
        inside
      let heap1 := Space.put heap dest (output.set! oj saved[fo])
      let first : Zlib.Inffast.L := { current with
        from_ := .ref source (fo + 1), out := .ref dest (oj + 1) }
      change Zlib.Inffast.copy1 current heap = .ok (first, heap1) at copyRun
      have zeroOp : current.op - 1 = 0 := by
        apply UInt32.toNat_inj.mp
        rw [Zlib.Inffast.Proofs.u32_sub_one_toNat (by omega)]
        simp [count]
      let final : Zlib.Inffast.L := { first with op := 0 }
      have run : cdoWhile.go body cond (fu + 1) current heap =
          .ok (final, heap1) := by
        unfold cdoWhile.go
        simp only [bind_app]
        dsimp only [body]
        rw [copyRun]
        simp [cond, first, final, zeroOp]
      have finalBytes : Space.get heap1 dest = some
          (copyOtherBytes saved fo output oj 1) := by
        have nextGet : Space.get heap1 dest =
            some (output.set! oj saved[fo]) :=
          byte_view_get_put currentOutput currentWrite _
        rw [nextGet]
        simp only [copyOtherBytes, getElem!_pos saved fo (by omega)]
      have finalWritable : Space.ro heap1 dest = false := by
        change Space.ro (Space.put heap dest (output.set! oj saved[fo])) dest = false
        rw [byte_view_ro_write]
        exact currentWrite
      have finalSource : Space.get heap1 source = some saved := by
        change Space.get (Space.put heap dest (output.set! oj saved[fo])) source = _
        rw [byte_view_get_put_ne heap different]
        exact currentSource
      exact ⟨final, heap1, run, copied.with_op 0, rfl,
        by simp [final, first], by simp [final, first],
        finalBytes, finalWritable, finalSource,
        by simp [final, first]⟩
    | succ k ih =>
      intro fu heap current output fo oj count fuelBound currentPacket
        sourcePtr currentSource sourceFit currentOut currentOutput
        currentWrite currentSize lower upper
      obtain ⟨fu, rfl⟩ : ∃ nextFuel, fu = nextFuel + 1 :=
        ⟨fu - 1, by omega⟩
      have inside : oo ≤ oj ∧ oj < oo + slow.left.toNat :=
        ⟨lower, by omega⟩
      have fullSize : oo + slow.left.toNat ≤ output.size := by
        rw [currentSize]
        exact outputSize
      have ⟨copyRun, copied⟩ := currentPacket.copy1_view
        separate left sourcePtr currentSource (by omega)
        currentOut outputPtr currentOutput currentWrite fullSize
        inside
      let heap1 := Space.put heap dest (output.set! oj saved[fo])
      let first : Zlib.Inffast.L := { current with
        from_ := .ref source (fo + 1), out := .ref dest (oj + 1) }
      change Zlib.Inffast.copy1 current heap = .ok (first, heap1) at copyRun
      let next : Zlib.Inffast.L := { first with op := current.op - 1 }
      have sourceNext : Space.get heap1 source = some saved := by
        change Space.get (Space.put heap dest (output.set! oj saved[fo])) source = _
        rw [byte_view_get_put_ne heap different]
        exact currentSource
      have outputNext : Space.get heap1 dest =
          some (output.set! oj saved[fo]) :=
        byte_view_get_put currentOutput currentWrite _
      have writeNext : Space.ro heap1 dest = false := by
        change Space.ro (Space.put heap dest (output.set! oj saved[fo])) dest = false
        rw [byte_view_ro_write]
        exact currentWrite
      have nextCount : next.op.toNat = k + 1 := by
        change (current.op - 1).toNat = k + 1
        rw [Zlib.Inffast.Proofs.u32_sub_one_toNat (by omega)]
        omega
      have nextPacket : FastInputPacket heap1 slow bs next :=
        copied.with_op (current.op - 1)
      obtain ⟨final, heapFinal, nextRun, finalPacket, finalOp,
          finalFrom, finalOut, finalBytes, finalWritable,
          finalSource, finalEq⟩ :=
        ih fu heap1 next (output.set! oj saved[fo]) (fo + 1)
          (oj + 1) nextCount (by omega) nextPacket rfl
          sourceNext (by omega) rfl outputNext writeNext
          (by simpa using currentSize) (by omega) (by omega)
      have continues : (current.op - 1 != 0) = true :=
        Zlib.Inffast.Proofs.u32_sub_one_ne (by omega)
      have run : cdoWhile.go body cond (fu + 1 + 1) current heap =
          .ok (final, heapFinal) := by
        unfold cdoWhile.go
        simp only [bind_app]
        dsimp only [body]
        rw [copyRun]
        simp [body, cond, first, next, continues, nextRun]
      have exactBytes : Space.get heapFinal dest = some
          (copyOtherBytes saved fo output oj (k + 1 + 1)) := by
        simpa only [copyOtherBytes,
          getElem!_pos saved fo (by omega)] using finalBytes
      exact ⟨final, heapFinal, run, finalPacket, finalOp,
        by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using finalFrom,
        by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using finalOut, exactBytes, finalWritable, finalSource,
        by rw [finalEq]; simp [next, first, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]⟩
  obtain ⟨n, count⟩ : ∃ n, fastLocal.op.toNat = n + 1 :=
    ⟨fastLocal.op.toNat - 1, by omega⟩
  have fuelBound : n < fuel := by
    have machine := UInt32.toNat_lt fastLocal.op
    unfold fuel
    omega
  obtain ⟨result, after, run, finalPacket, finalOp,
      finalFrom, finalOut, finalBytes, finalWritable,
      finalSource, finalEq⟩ :=
    go n (fuel - 1) h fastLocal array sourceOff j count
      (by have bound := fuelBound; unfold fuel at bound ⊢; omega)
      packet fromPtr sourceGet
      (by rw [count] at sourceRoom; exact sourceRoom)
      outPtr outputGet outputWrite rfl outputRoom.1
      (by rw [count] at outputRoom; exact outputRoom.2)
  refine ⟨result, after, ?_, finalPacket, finalOp, ?_, ?_, ?_,
    finalWritable, finalSource, ?_⟩
  · change Zlib.Inffast.copyOp fastLocal h = _
    unfold Zlib.Inffast.copyOp cdoWhile
    simpa only [Zlib.Inffast.Proofs.fuel_pred] using run
  · simpa only [count, Nat.add_assoc] using finalFrom
  · simpa only [count, Nat.add_assoc] using finalOut
  · simpa only [count] using finalBytes
  · simpa only [count, Nat.add_assoc] using finalEq

/-- The translated `copyOp` loop also terminates when the back-reference
source is the current output object. Each iteration reads the updated array,
so overlapping LZ77 copies retain their sequential C meaning. The separate
public input packet remains valid throughout. -/
theorem FastInputPacket.copyOp_same_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {fastLocal : Zlib.Inffast.L}
    (packet : FastInputPacket h slow bs fastLocal)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    {dest : BRef} {array : Array UInt8} {sourceOff oo j : Nat}
    (fromPtr : fastLocal.from_ = .ref dest sourceOff)
    (outPtr : fastLocal.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (sourceRoom : sourceOff + fastLocal.op.toNat ≤ array.size)
    (outputRoom : oo ≤ j ∧
      j + fastLocal.op.toNat ≤ oo + slow.left.toNat)
    (positive : 1 ≤ fastLocal.op.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.copyOp fastLocal) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧ result.op = 0 ∧
      result.from_ = .ref dest
        (sourceOff + fastLocal.op.toNat) ∧
      result.out = .ref dest (j + fastLocal.op.toNat) ∧
      Space.get after dest = some
        (copySameBytes array sourceOff j fastLocal.op.toNat) ∧
      Space.ro after dest = false := by
  let body := Zlib.Inffast.copy1
  let cond : Zlib.Inffast.L → M (Bool × Zlib.Inffast.L) :=
    fun l => let op := l.op - 1; pure (op != 0, { l with op })
  have go : ∀ k fu (heap : Heap) (current : Zlib.Inffast.L)
      (output : Array UInt8) (fo oj : Nat),
      current.op.toNat = k + 1 → k ≤ fu →
      FastInputPacket heap slow bs current →
      current.from_ = .ref dest fo →
      current.out = .ref dest oj →
      Space.get heap dest = some output →
      Space.ro heap dest = false →
      output.size = array.size →
      fo + k + 1 ≤ output.size →
      oo ≤ oj → oj + k + 1 ≤ oo + slow.left.toNat →
      ∃ final heapFinal,
        cdoWhile.go body cond (fu + 1) current heap =
          .ok (final, heapFinal) ∧
        FastInputPacket heapFinal slow bs final ∧ final.op = 0 ∧
        final.from_ = .ref dest (fo + k + 1) ∧
        final.out = .ref dest (oj + k + 1) ∧
        Space.get heapFinal dest = some
          (copySameBytes output fo oj (k + 1)) ∧
        Space.ro heapFinal dest = false := by
    intro k
    induction k with
    | zero =>
      intro fu heap current output fo oj count _ currentPacket
        sourcePtr currentOut currentOutput currentWrite currentSize
        sourceFit lower upper
      have inside : oo ≤ oj ∧ oj < oo + slow.left.toNat :=
        ⟨lower, by omega⟩
      have fullSize : oo + slow.left.toNat ≤ output.size := by
        rw [currentSize]
        exact outputSize
      have ⟨copyRun, copied⟩ := currentPacket.copy1_view
        separate left sourcePtr currentOutput (by omega)
        currentOut outputPtr currentOutput currentWrite fullSize
        inside
      let heap1 := Space.put heap dest (output.set! oj output[fo])
      let first : Zlib.Inffast.L := { current with
        from_ := .ref dest (fo + 1), out := .ref dest (oj + 1) }
      change Zlib.Inffast.copy1 current heap = .ok (first, heap1) at copyRun
      have zeroOp : current.op - 1 = 0 := by
        apply UInt32.toNat_inj.mp
        rw [Zlib.Inffast.Proofs.u32_sub_one_toNat (by omega)]
        simp [count]
      let final : Zlib.Inffast.L := { first with op := 0 }
      have run : cdoWhile.go body cond (fu + 1) current heap =
          .ok (final, heap1) := by
        unfold cdoWhile.go
        simp only [bind_app]
        dsimp only [body]
        rw [copyRun]
        simp [cond, first, final, zeroOp]
      have finalBytes : Space.get heap1 dest = some
          (copySameBytes output fo oj 1) := by
        have nextGet : Space.get heap1 dest =
            some (output.set! oj output[fo]) :=
          byte_view_get_put currentOutput currentWrite _
        rw [nextGet]
        simp only [copySameBytes, getElem!_pos output fo (by omega)]
      have finalWritable : Space.ro heap1 dest = false := by
        change Space.ro (Space.put heap dest (output.set! oj output[fo])) dest = false
        rw [byte_view_ro_write]
        exact currentWrite
      exact ⟨final, heap1, run, copied.with_op 0, rfl,
        by simp [final, first], by simp [final, first],
        finalBytes, finalWritable⟩
    | succ k ih =>
      intro fu heap current output fo oj count fuelBound currentPacket
        sourcePtr currentOut currentOutput currentWrite currentSize
        sourceFit lower upper
      obtain ⟨fu, rfl⟩ : ∃ nextFuel, fu = nextFuel + 1 :=
        ⟨fu - 1, by omega⟩
      have inside : oo ≤ oj ∧ oj < oo + slow.left.toNat :=
        ⟨lower, by omega⟩
      have fullSize : oo + slow.left.toNat ≤ output.size := by
        rw [currentSize]
        exact outputSize
      have ⟨copyRun, copied⟩ := currentPacket.copy1_view
        separate left sourcePtr currentOutput (by omega)
        currentOut outputPtr currentOutput currentWrite fullSize
        inside
      let heap1 := Space.put heap dest (output.set! oj output[fo])
      let first : Zlib.Inffast.L := { current with
        from_ := .ref dest (fo + 1), out := .ref dest (oj + 1) }
      change Zlib.Inffast.copy1 current heap = .ok (first, heap1) at copyRun
      let next : Zlib.Inffast.L := { first with op := current.op - 1 }
      have outputNext : Space.get heap1 dest =
          some (output.set! oj output[fo]) :=
        byte_view_get_put currentOutput currentWrite _
      have writeNext : Space.ro heap1 dest = false := by
        change Space.ro (Space.put heap dest (output.set! oj output[fo])) dest = false
        rw [byte_view_ro_write]
        exact currentWrite
      have nextCount : next.op.toNat = k + 1 := by
        change (current.op - 1).toNat = k + 1
        rw [Zlib.Inffast.Proofs.u32_sub_one_toNat (by omega)]
        omega
      have nextPacket : FastInputPacket heap1 slow bs next :=
        copied.with_op (current.op - 1)
      obtain ⟨final, heapFinal, nextRun, finalPacket, finalOp,
          finalFrom, finalOut, finalBytes, finalWritable⟩ :=
        ih fu heap1 next (output.set! oj output[fo]) (fo + 1)
          (oj + 1) nextCount (by omega) nextPacket rfl rfl
          outputNext writeNext (by simpa using currentSize)
          (by simpa only [Array.size_set!] using
            (show fo + 1 + k + 1 ≤ output.size by omega))
          (by omega) (by omega)
      have continues : (current.op - 1 != 0) = true :=
        Zlib.Inffast.Proofs.u32_sub_one_ne (by omega)
      have run : cdoWhile.go body cond (fu + 1 + 1) current heap =
          .ok (final, heapFinal) := by
        unfold cdoWhile.go
        simp only [bind_app]
        dsimp only [body]
        rw [copyRun]
        simp [body, cond, first, next, continues, nextRun]
      have exactBytes : Space.get heapFinal dest = some
          (copySameBytes output fo oj (k + 1 + 1)) := by
        simpa only [copySameBytes,
          getElem!_pos output fo (by omega)] using finalBytes
      exact ⟨final, heapFinal, run, finalPacket, finalOp,
        by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using finalFrom,
        by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using finalOut, exactBytes, finalWritable⟩
  obtain ⟨n, count⟩ : ∃ n, fastLocal.op.toNat = n + 1 :=
    ⟨fastLocal.op.toNat - 1, by omega⟩
  have fuelBound : n < fuel := by
    have machine := UInt32.toNat_lt fastLocal.op
    unfold fuel
    omega
  obtain ⟨result, after, run, finalPacket, finalOp,
      finalFrom, finalOut, finalBytes, finalWritable⟩ :=
    go n (fuel - 1) h fastLocal array sourceOff j count
      (by have bound := fuelBound; unfold fuel at bound ⊢; omega)
      packet fromPtr outPtr outputGet outputWrite rfl
      (by rw [count] at sourceRoom; exact sourceRoom)
      outputRoom.1
      (by rw [count] at outputRoom; exact outputRoom.2)
  refine ⟨result, after, ?_, finalPacket, finalOp, ?_, ?_, ?_,
    finalWritable⟩
  · change Zlib.Inffast.copyOp fastLocal h = _
    unfold Zlib.Inffast.copyOp cdoWhile
    simpa only [Zlib.Inffast.Proofs.fuel_pred] using run
  · simpa only [count, Nat.add_assoc] using finalFrom
  · simpa only [count, Nat.add_assoc] using finalOut
  · simpa only [count] using finalBytes

/-- The complete translated `copyOp` loop on general byte views. The source
may be the output itself, another object, or an object containing the
caller's input, provided its stated readable range is live. -/
theorem FastInputPacket.copyOp_view
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
    (sourceRoom : sourceOff + fastLocal.op.toNat ≤ saved.size)
    (outPtr : fastLocal.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some array)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ array.size)
    (outputRoom : oo ≤ j ∧
      j + fastLocal.op.toNat ≤ oo + slow.left.toNat)
    (positive : 1 ≤ fastLocal.op.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.copyOp fastLocal) h = .ok (result, after) ∧
      FastInputPacket after slow bs result ∧ result.op = 0 ∧
      result.from_ = .ref source
        (sourceOff + fastLocal.op.toNat) ∧
      result.out = .ref dest (j + fastLocal.op.toNat) ∧
      Space.get after dest = some
        (if source = dest then
          Zlib.Inffast.Proofs.cpyN fastLocal.op.toNat
            sourceOff j array
        else
          Zlib.Inffast.Proofs.blitN saved fastLocal.op.toNat
            sourceOff j array) ∧
      Space.ro after dest = false := by
  by_cases same : source = dest
  · subst source
    have arrays : saved = array :=
      Option.some.inj (sourceGet.symm.trans outputGet)
    subst saved
    simpa [copySameBytes_eq_cpyN] using
      packet.copyOp_same_view separate left fromPtr outPtr
      outputPtr outputGet outputWrite outputSize sourceRoom
      outputRoom positive
  · obtain ⟨result, after, run, nextPacket, zeroOp, nextFrom,
        nextOut, bytes, writable, _, _⟩ :=
      packet.copyOp_distinct_view separate left same fromPtr
        sourceGet sourceRoom outPtr outputPtr outputGet outputWrite
        outputSize outputRoom positive
    exact ⟨result, after, run, nextPacket, zeroOp, nextFrom,
      nextOut, by simpa [same, copyOtherBytes_eq_blitN]
        using bytes, writable⟩

end Zlib.Inflate.Proofs
