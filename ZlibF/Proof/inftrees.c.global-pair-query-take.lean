import ZlibF.Proof.«inflate.c.global-pair-length-flags»
import ZlibF.Proof.«inftrees.c.query-take-source»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inftrees
open Zlib.Inflate.Proofs Zlib.Inftrees.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Proofs.QueryTakeSource
set_option autoImplicit false

/-- The consumed-prefix property belongs to the actual successful table
constructor, including its reserved and invalid cells. -/
theorem actual_constructor_query_take
    {h : Heap} {type : UInt32} {rl rw : WRef} {ol ow offset : Nat}
    {count bits : UInt32} {rc : CodeRef} {result : Int32 × CodePtr × UInt32}
    {codes : Array Code}
    (trace : PayloadStable.CallTrace h type rl ol count rc offset bits rw ow result codes)
    (kind : type = LENS ∨ type = DISTS) (success : result.1 = 0) :
    QueryTake type codes offset result.2.2.toNat := by
  obtain ⟨pre, after, actual, _frame, get⟩ := trace
  obtain ⟨other, otherHeap, source, meaning⟩ :=
    constructor_establishes_query_take _ _ _ _ _ _ _ _ _ _ pre kind
  rw [actual] at source
  cases source
  exact meaning success codes get

/-- The second constructor's actual pointwise frame retains the first
table's consumed-prefix property. The first returned pointer supplies the
extent boundary; no disjoint-table premise is imposed on public callers. -/
theorem pair_length_query_take
    {h : Heap} {zs offset : Nat} {before middle state : InflateState}
    (trace : PayloadStable.PairTrace h zs before middle state offset) :
    QueryTake LENS state.codes 0 state.lenbits.toNat := by
  obtain ⟨nextL, bitsL, workL, codesL, nextD, bitsD, workD, codesD,
    middleEq, stateEq, next, lengthCall, distanceCall⟩ := trace
  have takeQuery := actual_constructor_query_take lengthCall (Or.inl rfl) rfl
  obtain ⟨used, pointer, extent⟩ := actual_constructor_extent lengthCall rfl
  have size : used = offset := by
    have same := Ptr.ref.inj (pointer.symm.trans next)
    simpa only [Nat.zero_add] using same.2
  subst used
  obtain ⟨pre, after, _actual, frame, get⟩ := distanceCall
  have initialGet : Space.get (setI (setI h zs middle) zs (clDistPre middle))
      (CodeRef.istate_codes zs) = some codesL := by
    simpa only [middleEq, clDistPre, clLensResult] using
      (CodeRef.get_istate_codes (setI_istates_same (setI h zs middle) zs (clDistPre middle)))
  have old : pre.ca = codesL := Option.some.inj (pre.hgc.symm.trans initialGet)
  obtain ⟨_work, array, heap, _workSize, _codeSize, _workFrame, cells, _result⟩ := frame
  have actualGet : Space.get after (CodeRef.istate_codes zs) = some array := by
    rw [heap]
    apply Zlib.Inftrees.Proofs.cget_put_self (a0 := pre.ca)
    · rw [Zlib.Inftrees.Proofs.cget_put_word]
      exact pre.hgc
    · exact pre.hro
  have final : array = codesD := Option.some.inj (actualGet.symm.trans get)
  subst array
  have preserved : QueryTake LENS codesD 0 bitsL.toNat := by
    apply query_take_of_prefix LENS codesL codesD 0 bitsL.toNat offset
      (Or.inl rfl) extent takeQuery
    intro i _lower upper
    rw [old] at cells
    exact cells i (Or.inl (by omega))
  rw [stateEq, middleEq]
  exact preserved

theorem pair_distance_query_take
    {h : Heap} {zs offset : Nat} {before middle state : InflateState}
    (trace : PayloadStable.PairTrace h zs before middle state offset) :
    QueryTake DISTS state.codes offset state.distbits.toNat := by
  obtain ⟨nextL, bitsL, workL, codesL, nextD, bitsD, workD, codesD,
    middleEq, stateEq, _next, _lengthCall, distanceCall⟩ := trace
  have takeQuery := actual_constructor_query_take distanceCall (Or.inr rfl) rfl
  rw [stateEq, middleEq]
  exact takeQuery

/-- Both installed table pointers have source-proved consumed-prefix
queries. This is internal metadata, not a public caller precondition. -/
def InstalledQueryTake (h : Heap) (s : InflateState) : Prop :=
  (∃ ref offset codes, s.lencode = .ref ref offset ∧ Space.get h ref = some codes ∧
    QueryTake LENS codes offset s.lenbits.toNat) ∧
  (∃ ref offset codes, s.distcode = .ref ref offset ∧ Space.get h ref = some codes ∧
    QueryTake DISTS codes offset s.distbits.toNat)

theorem pair_installed_query_take
    {h : Heap} {zs offset : Nat} {before middle state : InflateState}
    (trace : PayloadStable.PairTrace h zs before middle state offset) :
    InstalledQueryTake (setI h zs state) state := by
  have length := pair_length_query_take trace
  have distance := pair_distance_query_take trace
  obtain ⟨nextL, bitsL, workL, codesL, nextD, bitsD, workD, codesD,
    middleEq, stateEq, next, _lengthCall, _distanceCall⟩ := trace
  have get : Space.get (setI h zs state) (CodeRef.istate_codes zs) = some state.codes :=
    CodeRef.get_istate_codes (setI_istates_same ..)
  refine ⟨⟨.istate_codes zs, 0, state.codes, ?_, get, length⟩,
    ⟨.istate_codes zs, offset, state.codes, ?_, get, distance⟩⟩
  · rw [stateEq, middleEq]; rfl
  · rw [stateEq, middleEq]
    exact next

theorem InstalledQueryTake.restore
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (meaning : InstalledQueryTake h s) (get : h.istates zs = some s) (l : IL) :
    InstalledQueryTake (setI (r.put h (leaveStream z l)) zs (leaveState s l)) (leaveState s l) := by
  have stored : (r.put h (leaveStream z l)).istates zs = some s := by simpa using get
  constructor
  · obtain ⟨ref, offset, codes, pointer, tableGet, takeQuery⟩ := meaning.1
    refine ⟨ref, offset, codes, pointer, ?_, takeQuery⟩
    unfold leaveState
    rw [code_views_set_bits stored, code_views_put_stream]
    exact tableGet
  · obtain ⟨ref, offset, codes, pointer, tableGet, takeQuery⟩ := meaning.2
    refine ⟨ref, offset, codes, pointer, ?_, takeQuery⟩
    unfold leaveState
    rw [code_views_set_bits stored, code_views_put_stream]
    exact tableGet

/-- The actual decoder's non-table writes retain the two established
properties through their proved code-view and pointer frames. -/
theorem InstalledQueryTake.of_views
    {h after : Heap} {s state : InflateState}
    (meaning : InstalledQueryTake h s)
    (views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (lengths : state.lencode = s.lencode) (distances : state.distcode = s.distcode)
    (lengthBits : state.lenbits = s.lenbits) (distanceBits : state.distbits = s.distbits) :
    InstalledQueryTake after state := by
  constructor
  · obtain ⟨ref, offset, codes, pointer, tableGet, takeQuery⟩ := meaning.1
    exact ⟨ref, offset, codes, lengths.trans pointer, by rw [views]; exact tableGet,
      by rw [lengthBits]; exact takeQuery⟩
  · obtain ⟨ref, offset, codes, pointer, tableGet, takeQuery⟩ := meaning.2
    exact ⟨ref, offset, codes, distances.trans pointer, by rw [views]; exact tableGet,
      by rw [distanceBits]; exact takeQuery⟩

#print axioms actual_constructor_query_take
#print axioms pair_length_query_take
#print axioms pair_distance_query_take
#print axioms pair_installed_query_take
#print axioms InstalledQueryTake.restore
#print axioms InstalledQueryTake.of_views
end Zlib.Inflate.Proofs.FunctionalEpoch
