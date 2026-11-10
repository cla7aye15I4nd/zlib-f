import ZlibF.Proof.«inflate.c.output-credit-append»
import ZlibF.Proof.«inflate.c.output-invariant»
namespace Zlib.Inflate.Proofs.FunctionalTrailer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- Extract a fresh output slice from the actual returned byte object.
The old physical prefix is preserved by the produced output frame. -/
theorem OutputCredit.observe_segment
    {h after : Heap} {r : ZStreamRef} {z stream : ZStream} {s state : InflateState}
    {l regs : IL} {prior old : List UInt8} {credited made : Nat} {changed : Nat → Prop}
    (ledger : OutputCredit h z s l prior old credited)
    (output : OutputCursorInvariant h r l)
    (frame : BufferFrame h after changed [⟨l.put, made⟩])
    (put : regs.put = inputAdvance l.put made)
    (left : regs.left.toNat + made = l.left.toNat)
    (out : regs.out_ = l.out_)
    (credit : AdlerCredit stream state (prior ++ old.take credited)) :
    ∃ more, more.length = made ∧
      OutputCredit after stream state regs prior (old ++ more) credited ∧
      (∀ dest off array, regs.put = .ref dest off → Space.get after dest = some array →
        writtenBytes array off (old ++ more).length = old ++ more) ∧
      ∃ dest off array, l.put = .ref dest off ∧ regs.put = .ref dest (off + made) ∧
        Space.get after dest = some array ∧ off + made ≤ array.size ∧
        writtenBytes array (off + made) made = more := by
  obtain ⟨dest, off, oldArray, pointer, getOld, _start, _bound, _oldBytes⟩ := ledger.physical
  have range := output.range
  obtain null | ⟨_readable, writable, _owned⟩ := range
  · exact False.elim (output.nonnull null)
  have writable := writable rfl
  rcases writable with null | ⟨dest2, off2, outputArray, pointer2, get2, _write, capacity⟩
  · rw [pointer] at null
    cases null.1
  · have samePtr := pointer.symm.trans pointer2
    cases samePtr
    have sameArray : outputArray = oldArray := Option.some.inj (get2.symm.trans getOld)
    subst outputArray
    have bound : off + made ≤ oldArray.size := by omega
    obtain ⟨array, get, size, _outside⟩ := frame.2 ⟨l.put, made⟩ (by simp) dest off oldArray pointer getOld
    let more := writtenBytes array (off + made) made
    have length : more.length = made := by
      simp only [more, writtenBytes, List.length_take, List.length_drop, Array.length_toList]
      omega
    have cursor : regs.put = .ref dest (off + made) := by rw [put, pointer]; rfl
    have delta : (regs.out_ - regs.left).toNat = (l.out_ - l.left).toNat + more.length := by
      have beforeLe : l.left ≤ l.out_ := UInt32.le_iff_toNat_le.mpr output.count
      have afterLe : regs.left ≤ regs.out_ := UInt32.le_iff_toNat_le.mpr (by rw [out]; have := output.count; omega)
      rw [UInt32.toNat_sub_of_le _ _ afterLe, UInt32.toNat_sub_of_le _ _ beforeLe, out, length]
      have count := left
      have lower := output.count
      omega
    have final := ledger.append_observed (by rw [length]; exact frame) credit delta
      ⟨dest, off, array, pointer, by rw [length]; exact cursor, get, by omega, by rw [length]⟩
    refine ⟨more, length, final, ?_, dest, off, array, pointer, cursor, get, by omega, rfl⟩
    intro d i a ptr getA
    obtain ⟨d0, i0, a0, ptr0, get0, _start0, _bound0, bytes⟩ := final.physical
    have same := ptr.symm.trans ptr0
    cases same
    have arrayEq : a = a0 := Option.some.inj (getA.symm.trans get0)
    subst a
    exact bytes

#print axioms OutputCredit.observe_segment
end Zlib.Inflate.Proofs.FunctionalTrailer
