import ZlibF.Proof.«inflate.c.global-dynamic-payload-composition»
import ZlibF.Proof.«inftrees.c.decode.frame»
import ZlibF.Proof.«inftrees.c.read-extent»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inftrees
open Zlib.Inflate.Proofs Zlib.Inftrees.Spec
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.FastTableFlags
set_option autoImplicit false

theorem actual_constructor_extent
    {h : Heap} {type : UInt32} {rl rw : WRef} {ol ow countOffset : Nat}
    {count bits : UInt32} {rc : CodeRef} {result : Int32 × CodePtr × UInt32} {codes : Array Code}
    (trace : PayloadStable.CallTrace h type rl ol count rc countOffset bits rw ow result codes)
    (success : result.1 = 0) :
    ∃ used, result.2.1 = .ref rc (countOffset + used) ∧
      TableReadExtent type codes countOffset result.2.2.toNat used := by
  obtain ⟨pre, after, actual, _frame, get⟩ := trace
  obtain ⟨other, otherHeap, source, _result, extent⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_read_extent _ _ _ _ _ _ _ _ _ _ pre
  rw [actual] at source
  cases source
  obtain ⟨array, used, sameGet, pointer, _capacity, meaning, _⟩ := extent success
  have same : array = codes := Option.some.inj (sameGet.symm.trans get)
  subst array
  exact ⟨used, pointer, meaning⟩

theorem query_flags_of_prefix
    {type : UInt32} {before after : Array Code} {offset root used : Nat}
    (kind : type = LENS ∨ type = DISTS)
    (extent : TableReadExtent type before offset root used)
    (flags : QueryCompatible type before offset root)
    (cells : ∀ i, offset ≤ i → i < offset + used → after[i]? = before[i]?) :
    QueryCompatible type after offset root := by
  intro input entry consumed enough query
  rw [Zlib.Inftrees.Proofs.decode_table_read_preserved _ _ _ _ _ _ kind extent cells] at query
  exact flags input entry consumed enough query

/-- Both actual constructor traces matter: DISTS preserves the first
LENS query extent through its real pointwise write frame. -/
theorem pair_length_fast_flags
    {h : Heap} {zs offset : Nat} {before middle state : InflateState}
    (trace : PayloadStable.PairTrace h zs before middle state offset) :
    QueryCompatible LENS state.codes 0 state.lenbits.toNat := by
  obtain ⟨nextL, bitsL, workL, codesL, nextD, bitsD, workD, codesD,
    middleEq, stateEq, next, lengthCall, distanceCall⟩ := trace
  have flags := actual_constructor_fast_flags lengthCall (Or.inl rfl) rfl
  obtain ⟨used, pointer, extent⟩ := actual_constructor_extent lengthCall rfl
  have size : used = offset := by
    have same := Ptr.ref.inj (pointer.symm.trans next)
    simpa only [Nat.zero_add] using same.2
  subst used
  obtain ⟨pre, after, actual, frame, get⟩ := distanceCall
  have initialGet : Space.get (setI (setI h zs middle) zs (clDistPre middle))
      (CodeRef.istate_codes zs) = some codesL := by
    simpa only [middleEq, clDistPre, clLensResult] using
      (CodeRef.get_istate_codes (setI_istates_same (setI h zs middle) zs (clDistPre middle)))
  have old : pre.ca = codesL := Option.some.inj (pre.hgc.symm.trans initialGet)
  obtain ⟨work, array, heap, _workSize, _codeSize, _workFrame, cells, _result⟩ := frame
  have actualGet : Space.get after (CodeRef.istate_codes zs) = some array := by
    rw [heap]
    apply Zlib.Inftrees.Proofs.cget_put_self (a0 := pre.ca)
    · rw [Zlib.Inftrees.Proofs.cget_put_word]
      exact pre.hgc
    · exact pre.hro
  have final : array = codesD := Option.some.inj (actualGet.symm.trans get)
  subst array
  have preserved : QueryCompatible LENS codesD 0 bitsL.toNat := by
    apply query_flags_of_prefix (Or.inl rfl) extent flags
    intro i _lower upper
    rw [old] at cells
    exact cells i (Or.inl (by omega))
  rw [stateEq, middleEq]
  exact preserved

/-- Fast branch compatibility of the actually installed pair, including
reserved leaves. This is separate from Inv and safe read bounds. -/
def InstalledQueryFlags (h : Heap) (s : InflateState) : Prop :=
  (∃ ref offset codes, s.lencode = .ref ref offset ∧ Space.get h ref = some codes ∧
    QueryCompatible LENS codes offset s.lenbits.toNat) ∧
  (∃ ref offset codes, s.distcode = .ref ref offset ∧ Space.get h ref = some codes ∧
    QueryCompatible DISTS codes offset s.distbits.toNat)

theorem pair_installed_query_flags
    {h : Heap} {zs offset : Nat} {before middle state : InflateState}
    (trace : PayloadStable.PairTrace h zs before middle state offset) :
    InstalledQueryFlags (setI h zs state) state := by
  have length := pair_length_fast_flags trace
  have distance := pair_distance_fast_flags trace
  obtain ⟨nextL, bitsL, workL, codesL, nextD, bitsD, workD, codesD,
    middleEq, stateEq, next, _lengthCall, _distanceCall⟩ := trace
  have get : Space.get (setI h zs state) (CodeRef.istate_codes zs) = some state.codes :=
    CodeRef.get_istate_codes (setI_istates_same ..)
  refine ⟨⟨.istate_codes zs, 0, state.codes, ?_, get, length⟩,
    ⟨.istate_codes zs, offset, state.codes, ?_, get, distance⟩⟩
  · rw [stateEq, middleEq]; rfl
  · rw [stateEq, middleEq]
    exact next

theorem InstalledQueryFlags.restore
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (flags : InstalledQueryFlags h s) (get : h.istates zs = some s) (l : IL) :
    InstalledQueryFlags (setI (r.put h (leaveStream z l)) zs (leaveState s l)) (leaveState s l) := by
  have stored : (r.put h (leaveStream z l)).istates zs = some s := by simpa using get
  constructor
  · obtain ⟨ref, offset, codes, pointer, tableGet, compatible⟩ := flags.1
    refine ⟨ref, offset, codes, pointer, ?_, compatible⟩
    unfold leaveState
    rw [code_views_set_bits stored, code_views_put_stream]
    exact tableGet
  · obtain ⟨ref, offset, codes, pointer, tableGet, compatible⟩ := flags.2
    refine ⟨ref, offset, codes, pointer, ?_, compatible⟩
    unfold leaveState
    rw [code_views_set_bits stored, code_views_put_stream]
    exact tableGet

end Zlib.Inflate.Proofs.FunctionalEpoch
