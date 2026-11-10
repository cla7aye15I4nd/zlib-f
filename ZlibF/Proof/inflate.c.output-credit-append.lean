import ZlibF.Proof.«inflate.c.functional-trailer»
import ZlibF.Proof.«inflate.c.caller-input-frame»

namespace Zlib.Inflate.Proofs.FunctionalTrailer
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false

theorem writtenBytes_append {array : Array UInt8} {off old made : Nat}
    (start : old ≤ off) :
    ZlibF.Math.LZ77Copy.writtenBytes array (off + made) (old + made) =
      ZlibF.Math.LZ77Copy.writtenBytes array off old ++
        ZlibF.Math.LZ77Copy.writtenBytes array (off + made) made := by
  unfold ZlibF.Math.LZ77Copy.writtenBytes
  rw [show off + made - (old + made) = off - old by omega,
    show off + made - made = off by omega, List.take_add]
  rw [List.drop_drop, show off - old + old = off by omega]

/-- An actual payload write outside the already-produced prefix retains
that prefix and appends precisely its independently observed new slice. -/
theorem physical_output_append {before after : Heap} {changed : Nat → Prop}
    {ref : BRef} {off : Nat} {oldArray array : Array UInt8} {old more : List UInt8}
    (frame : BufferFrame before after changed [⟨.ref ref off, more.length⟩])
    (getBefore : Space.get before ref = some oldArray)
    (getAfter : Space.get after ref = some array)
    (start : old.length ≤ off) (bound : off ≤ oldArray.size)
    (observed : ZlibF.Math.LZ77Copy.writtenBytes oldArray off old.length = old)
    (newBytes : ZlibF.Math.LZ77Copy.writtenBytes array (off + more.length) more.length = more) :
    ZlibF.Math.LZ77Copy.writtenBytes array (off + more.length) (old ++ more).length = old ++ more := by
  have separate : Separate (.ref ref (off - old.length)) old.length
      (.ref ref off) more.length := by
    apply Or.inr; apply Or.inr
    exact Or.inr (Or.inl (by omega))
  have preserved := BufferFrame.same_view_separate_read frame getBefore
    (show off - old.length + old.length ≤ oldArray.size by omega) separate
  rcases preserved with impossible | ⟨otherRef, base, current, pointer, get, size, values⟩
  · exact False.elim (by cases impossible.1)
  · cases pointer
    have same : current = array := Option.some.inj (get.symm.trans getAfter)
    subst current
    have prior : ZlibF.Math.LZ77Copy.writtenBytes array off old.length = old := by
      exact values.symm.trans observed
    rw [List.length_append, writtenBytes_append start, prior, newBytes]

/-- A source-proved payload segment extends the full-call physical output
while leaving CHECK's already-credited count unchanged. The same rule
handles literal, stored and match segments, including output in prior blocks. -/
theorem OutputCredit.append_observed
    {before after : Heap} {changed : Nat → Prop} {z stream : ZStream}
    {s state : InflateState} {l regs : IL} {prior old more : List UInt8} {credited : Nat}
    (ledger : OutputCredit before z s l prior old credited)
    (frame : BufferFrame before after changed [⟨l.put, more.length⟩])
    (credit : AdlerCredit stream state (prior ++ old.take credited))
    (count : (regs.out_ - regs.left).toNat = (l.out_ - l.left).toNat + more.length)
    (physical : ∃ ref off array,
      l.put = .ref ref off ∧ regs.put = .ref ref (off + more.length) ∧
      Space.get after ref = some array ∧ off + more.length ≤ array.size ∧
      ZlibF.Math.LZ77Copy.writtenBytes array (off + more.length) more.length = more) :
    OutputCredit after stream state regs prior (old ++ more) credited := by
  obtain ⟨ref, off, array, pointer, cursor, getAfter, bound, newBytes⟩ := physical
  obtain ⟨oldRef, oldOff, oldArray, oldPointer, getBefore, start, oldBound, oldBytes⟩ := ledger.physical
  have samePointer := oldPointer.symm.trans pointer
  cases samePointer
  have observed := physical_output_append (by simpa only [pointer] using frame)
    getBefore getAfter start oldBound oldBytes newBytes
  refine ⟨by have := ledger.count; simp only [List.length_append]; omega, ?_, ?_, ?_⟩
  · have take : (old ++ more).take credited = old.take credited := by
      rw [List.take_append, Nat.sub_eq_zero_of_le ledger.count]
      simp only [List.take_zero, List.append_nil]
    rw [take]
    exact credit
  · rw [count, ledger.pending, List.length_append]
    have := ledger.count
    omega
  · refine ⟨ref, off + more.length, array, cursor, getAfter, ?_, bound, observed⟩
    simp only [List.length_append]
    omega

end Zlib.Inflate.Proofs.FunctionalTrailer
