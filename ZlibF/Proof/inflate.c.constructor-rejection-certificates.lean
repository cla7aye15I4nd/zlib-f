import ZlibF.Proof.«inftrees.c»

namespace Zlib.Inftrees.Proofs.ConstructorRejects
open C Zlib.Inftrees Zlib.Inftrees.Spec ZlibF.Spec
set_option autoImplicit false

/-- A real constructor run returns -1 exactly when its independently
interpreted source alphabet is unacceptable. The execution and source
memory facts are observations; no callee contract is assumed. -/
theorem actual_return_rejects_iff
    {h after : Heap} {type : UInt32} {rl rw : WRef} {ol ow offset : Nat}
    {count bits : UInt32} {rc : CodeRef} {result : Int32 × CodePtr × UInt32}
    (pre : CallPre h type rl ol count rc offset bits rw ow)
    (actual : C.run (inflate_table type (.ref rl ol) count (.ref rc offset) bits (.ref rw ow)) h =
      .ok (result, after)) :
    result.1 = -1 ↔ ¬ Acceptable (kindOf type) (lensOf pre.f count.toNat) := by
  obtain ⟨other, otherHeap, source, rejects, _zero, _capacity⟩ :=
    inflate_table_correct_ret h type rl ol count rc offset bits rw ow pre.la pre.wa pre.ca
      pre.hty pre.hgl pre.hgw pre.hgc pre.hro pre.hne pre.hla pre.hwa pre.hca
      pre.hf15 pre.hcodes pre.hlens pre.hdists
  rw [actual] at source
  cases source
  exact rejects

/-- An independent observation of the source length array identifies the
same alphabet as the real constructor's CallPre. This form is convenient
for connecting an actual constructor refusal to decoded header fields. -/
theorem actual_source_return_rejects_iff
    {h after : Heap} {type : UInt32} {rl rw : WRef} {ol ow offset : Nat}
    {count bits : UInt32} {rc : CodeRef} {result : Int32 × CodePtr × UInt32}
    {lengths : Array UInt16}
    (pre : CallPre h type rl ol count rc offset bits rw ow)
    (get : Space.get h rl = some lengths)
    (actual : C.run (inflate_table type (.ref rl ol) count (.ref rc offset) bits (.ref rw ow)) h =
      .ok (result, after)) :
    result.1 = -1 ↔ ¬ Acceptable (kindOf type) (lensList lengths ol count.toNat) := by
  have arrays : pre.la = lengths := Option.some.inj (pre.hgl.symm.trans get)
  have alphabet : lensOf pre.f count.toNat = lensList lengths ol count.toNat := by
    change lensList pre.la ol count.toNat = _
    rw [arrays]
  rw [← alphabet]
  exact actual_return_rejects_iff pre actual

/-- The real default CODES call has nineteen lengths and requested root
seven. A refusal contradicts the acceptable code-length alphabet required
by an independent accepted dynamic header. This does not claim that an
arbitrary CodeLens derivation by itself requires Acceptable. -/
theorem codes_failure_not_acceptable
    {h after : Heap} {rl rw : WRef} {ol ow offset : Nat} {rc : CodeRef}
    {result : Int32 × CodePtr × UInt32} {lengths : Array UInt16}
    (pre : CallPre h CODES rl ol 19 rc offset 7 rw ow)
    (get : Space.get h rl = some lengths)
    (actual : C.run (inflate_table CODES (.ref rl ol) 19 (.ref rc offset) 7 (.ref rw ow)) h =
      .ok (result, after)) (failure : result.1 = -1) :
    ¬ Acceptable .codeLength (lensList lengths ol 19) := by
  have rejected := (actual_source_return_rejects_iff pre get actual).mp failure
  exact rejected

/-- The actual default LENS root is nine. The theorem retains the existing
CallPre domain (up to 288 symbols), which includes the source caller's
at-most-286 restriction without needing that extra bound here. -/
theorem lens_failure_not_acceptable
    {h after : Heap} {rl rw : WRef} {ol ow offset : Nat} {rc : CodeRef} {count : UInt32}
    {result : Int32 × CodePtr × UInt32} {lengths : Array UInt16}
    (pre : CallPre h LENS rl ol count rc offset 9 rw ow)
    (get : Space.get h rl = some lengths)
    (actual : C.run (inflate_table LENS (.ref rl ol) count (.ref rc offset) 9 (.ref rw ow)) h =
      .ok (result, after)) (failure : result.1 = -1) :
    ¬ Acceptable .litLen (lensList lengths ol count.toNat) := by
  have rejected := (actual_source_return_rejects_iff pre get actual).mp failure
  exact rejected

/-- The actual default DISTS root is six. The theorem retains the existing
CallPre domain (up to 32 symbols), which includes the source caller's
at-most-30 restriction without adding it as a new hypothesis. -/
theorem dists_failure_not_acceptable
    {h after : Heap} {rl rw : WRef} {ol ow offset : Nat} {rc : CodeRef} {count : UInt32}
    {result : Int32 × CodePtr × UInt32} {lengths : Array UInt16}
    (pre : CallPre h DISTS rl ol count rc offset 6 rw ow)
    (get : Space.get h rl = some lengths)
    (actual : C.run (inflate_table DISTS (.ref rl ol) count (.ref rc offset) 6 (.ref rw ow)) h =
      .ok (result, after)) (failure : result.1 = -1) :
    ¬ Acceptable .dist (lensList lengths ol count.toNat) := by
  have rejected := (actual_source_return_rejects_iff pre get actual).mp failure
  exact rejected

#print axioms actual_return_rejects_iff
#print axioms actual_source_return_rejects_iff
#print axioms codes_failure_not_acceptable
#print axioms lens_failure_not_acceptable
#print axioms dists_failure_not_acceptable
end Zlib.Inftrees.Proofs.ConstructorRejects
