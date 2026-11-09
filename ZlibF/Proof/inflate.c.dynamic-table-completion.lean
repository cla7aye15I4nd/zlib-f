import ZlibF.Proof.«inflate.c.dynamic-semantics»
import ZlibF.Proof.«inflate.c.code-length-classified»
import ZlibF.Proof.«inftrees.c.default-budget»
import ZlibF.Proof.«inflate.c.code-length-completion»

namespace Zlib.Inflate.Proofs.PayloadTables
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inftrees
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The two real payload constructors consume consecutive slices of the
same actual length array. -/
theorem lensOf_append_split (f : Nat → Nat) (n m : Nat) :
    Zlib.Inftrees.Proofs.lensOf f (n + m) =
      Zlib.Inftrees.Proofs.lensOf f n ++ Zlib.Inftrees.Proofs.lensOf (fun k => f (n + k)) m := by
  unfold Zlib.Inftrees.Proofs.lensOf
  rw [List.range_add, List.map_append, List.map_map]
  rfl

theorem actualLengthPrefix_payload_slices (s : InflateState)
    (count : s.«have».toNat = s.nlen.toNat + s.ndist.toNat) :
    (actualLengthPrefix s).take s.nlen.toNat =
      Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat ∧
    (actualLengthPrefix s).drop s.nlen.toNat =
      Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat := by
  rw [actualLengthPrefix, count, lensOf_append_split]
  constructor
  · exact List.take_left' (by rw [Zlib.Inftrees.Proofs.lensOf_length])
  · exact List.drop_left' (by rw [Zlib.Inftrees.Proofs.lensOf_length])

#print axioms lensOf_append_split
#print axioms actualLengthPrefix_payload_slices

/-- `case CODELENS:`. The actual first table constructor establishes
canonical decoding meaning at its real continuation, on the same array
as the existing execution and safety result. All refusals remain included. -/
theorem clTables_lens_valid_semantics {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (count : s.nlen.toNat ≤ 286)
    (lengths : ∀ k, k < s.nlen.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (valid : Acceptable .litLen (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat)) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852) ∧ bits.toNat ≤ 15 ∧ (ret = 0 ∨ ret = 1) ∧
      runX (clTables c) l h = runX (clAfterLens c ret) { l with ret := ret }
        (setI h zs (clLensResult zs s next bits work codes)) ∧
      (ret = 0 → ∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852 ∧
        Zlib.Inffast.Spec.LenTableSafe codes 0 bits.toNat ∧
        Zlib.Inftrees.Spec.TableReadExtent LENS codes 0 bits.toNat used ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS codes 0 bits.toNat used
          (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat)) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h zs (clLensPre zs s)).istates zs = some (clLensPre zs s) := by simp
  have lens : Space.get (setI h zs (clLensPre zs s)) (WRef.istate_lens zs) = some s.lens := by
    simpa [clLensPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h zs (clLensPre zs s)) (WRef.istate_work zs) = some s.work := by
    simpa [clLensPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h zs (clLensPre zs s)) (CodeRef.istate_codes zs) = some s.codes := by
    simpa [clLensPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (clLensPre zs s)) LENS
      (.istate_lens zs) 0 s.nlen (.istate_codes zs) 0 9 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inr (Or.inl rfl), lens, work, codes, by simp, by simp,
      by omega, by omega, by simp [Zlib.Inftrees.Spec.capOf, LENS, CODES]; omega,
      by simpa using lengths, (by intro impossible; cases impossible),
      fun _ => by omega, (by intro impossible; cases impossible)⟩
  obtain ⟨result, after, run, frame, tables⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_read_extent _ _ _ _ _ _ _ _ _ _ pre
  obtain ⟨result0, after0, run0, rejected, _accepted, _space⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_correct_ret (setI h zs (clLensPre zs s)) LENS
      (.istate_lens zs) 0 s.nlen (.istate_codes zs) 0 9 (.istate_work zs) 0
      pre.la pre.wa pre.ca pre.hty pre.hgl pre.hgw pre.hgc pre.hro pre.hne
      pre.hla pre.hwa pre.hca pre.hf15 pre.hcodes pre.hlens pre.hdists
  rw [run] at run0
  cases run0
  obtain ⟨semanticResult, semanticAfter, semanticRun, _semanticFrame, meaning⟩ :=
    Zlib.Inftrees.Proofs.constructor_establishes_decode_table_invariant
      _ _ _ _ _ _ _ _ _ _ pre (Or.inl rfl)
  rw [run] at semanticRun
  cases semanticRun
  have bounds := Zlib.Inftrees.Proofs.result_pointer_width_bounds frame (by decide)
    (by
      intro success
      obtain ⟨_, _, _, _, _, extent, _⟩ := tables success
      exact extent.2.1)
  obtain ⟨ret, next, bits⟩ := result
  have pointerBounds : ∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852 := by
    obtain ⟨used, bound, pointer⟩ := bounds.1
    exact ⟨used, by simpa using pointer,
      by simpa [Zlib.Inftrees.Spec.capOf, LENS, CODES] using bound⟩
  obtain ⟨wa, ca, heap, waSize, caSize, _, _, retCases⟩ := frame
  have rejection : ret = -1 ↔ ¬ Acceptable .litLen
      (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat) := by
    simpa [Zlib.Inftrees.Spec.kindOf, Zlib.Inftrees.Spec.lensList,
      Zlib.Inftrees.Proofs.lensOf, pre, CODES, LENS] using rejected
  have kinds : ret = 0 ∨ ret = 1 := by
    rcases retCases with ⟨zero, _⟩ | ⟨one | bad, _⟩
    · exact Or.inl zero
    · exact Or.inr one
    · exact False.elim ((rejection.mp bad) valid)
  refine ⟨ret, next, bits, wa, ca, waSize.trans workSize, caSize.trans codeSize, pointerBounds, bounds.2, kinds, ?_, ?_⟩
  · unfold clTables clAfterLens
    rw [hc]
    have actual := run
    change inflate_table LENS _ _ _ _ _ _ = _ at actual
    simp only [clLensPre] at actual
    rw [heap, put_work_codes stored] at actual
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, clLensPre, lensP, workP, codesP,
      actual, runX_modify, setI_setI, clLensResult]
  · intro success
    obtain ⟨array, used, get, pointer, bound, extent, _, safe, _⟩ := tables success
    have actualGet : Space.get after (CodeRef.istate_codes zs) = some ca := by
      rw [heap, put_work_codes stored]
      simp [Space.get, setI, clLensPre]
    rw [actualGet] at get
    cases get
    obtain ⟨semanticArray, semanticUsed, semanticGet, semanticPointer, _semanticCapacity, invariant⟩ := meaning success
    rw [actualGet] at semanticGet
    cases semanticGet
    have usedEq : semanticUsed = used := by
      have equality := Ptr.ref.inj (semanticPointer.symm.trans pointer)
      omega
    subst semanticUsed
    have alphabet : pre.f = fun k => (s.lens.getD k 0).toNat := by
      funext k
      change (s.lens.getD (0 + k) 0).toNat = _
      rw [Nat.zero_add]
    rw [alphabet] at invariant
    exact ⟨used, by simpa using pointer, by simpa [Zlib.Inftrees.Spec.capOf, LENS, CODES] using bound,
      safe rfl, extent, invariant⟩


#print axioms clTables_lens_valid_semantics

/-- `case CODELENS:` after successful length-table construction.
The actual distance call starts at the previous returned end. It retains
that length alphabet's invariant even on refusal, and establishes the new
distance alphabet on success. The register stores and continuation are
those of the actual source. This is a local construction result. -/
theorem clAfterLens_distance_valid_semantics {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.ndist.toNat → (s.lens.getD (s.nlen.toNat + k) 0).toNat ≤ 15)
    (offset : Nat) (next : s.next = .ref (.istate_codes zs) offset) (room : offset ≤ 852)
    (lensAlphabet : List Nat)
    (lensInvariant : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS s.codes 0 s.lenbits.toNat offset lensAlphabet)
    (valid : Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592) ∧ bits.toNat ≤ 15 ∧ (ret = 0 ∨ ret = 1) ∧
      runX (clAfterLens c 0) l h = runX (clAfterDist c ret) { l with ret := ret }
        (setI h zs (clDistResult s next bits work codes)) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS codes 0 s.lenbits.toNat offset lensAlphabet ∧
      (ret = 0 → ∃ used,
        next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS codes offset bits.toNat used
          (Zlib.Inftrees.Proofs.lensOf
            (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h zs (clDistPre s)).istates zs = some (clDistPre s) := by simp
  have lens : Space.get (setI h zs (clDistPre s)) (WRef.istate_lens zs) = some s.lens := by
    simpa [clDistPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h zs (clDistPre s)) (WRef.istate_work zs) = some s.work := by
    simpa [clDistPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h zs (clDistPre s)) (CodeRef.istate_codes zs) = some s.codes := by
    simpa [clDistPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (clDistPre s)) DISTS
      (.istate_lens zs) s.nlen.toNat s.ndist (.istate_codes zs) offset 6 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inr (Or.inr rfl), lens, work, codes, by simp, by simp,
      by omega, by omega, by simp [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES]; omega,
      lengths, (by intro impossible; cases impossible),
      (by intro impossible; cases impossible), fun _ => by omega⟩
  obtain ⟨result, after, array, run, frame, getArray, sameLens, newMeaning⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_preserves_decode_invariant pre (Or.inr rfl)
      lensInvariant (by omega)
  obtain ⟨result0, after0, run0, rejected, _accepted, _space⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_correct_ret (setI h zs (clDistPre s)) DISTS
      (.istate_lens zs) s.nlen.toNat s.ndist (.istate_codes zs) offset 6 (.istate_work zs) 0
      pre.la pre.wa pre.ca pre.hty pre.hgl pre.hgw pre.hgc pre.hro pre.hne
      pre.hla pre.hwa pre.hca pre.hf15 pre.hcodes pre.hlens pre.hdists
  rw [run] at run0
  cases run0
  have bounds := Zlib.Inftrees.Proofs.result_pointer_width_bounds frame (by decide)
    (by
      intro success
      obtain ⟨_, _, _, invariant⟩ := newMeaning success
      exact invariant.rootTable.2.1)
  obtain ⟨ret, nextResult, bits⟩ := result
  have pointerBounds : ∃ used, nextResult = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 := by
    obtain ⟨used, bound, pointer⟩ := bounds.1
    exact ⟨used, pointer, by simpa [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES] using bound⟩
  obtain ⟨wa, ca, heap, waSize, caSize, _, _, retCases⟩ := frame
  have actualGet : Space.get after (CodeRef.istate_codes zs) = some ca := by
    rw [heap, put_work_codes stored]
    simp [Space.get, setI, clDistPre]
  rw [actualGet] at getArray
  have sameArray : ca = array := Option.some.inj getArray
  subst array
  change (ret = -1 ↔ ¬ Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) at rejected
  have kinds : ret = 0 ∨ ret = 1 := by
    rcases retCases with ⟨zero, _⟩ | ⟨one | bad, _⟩
    · exact Or.inl zero
    · exact Or.inr one
    · exact False.elim ((rejected.mp bad) valid)
  refine ⟨ret, nextResult, bits, wa, ca, waSize.trans workSize, caSize.trans codeSize, pointerBounds, bounds.2, kinds, ?_, sameLens, ?_⟩
  · unfold clAfterLens clAfterDist
    rw [hc]
    have actual := run
    change inflate_table DISTS _ _ _ _ _ _ = _ at actual
    rw [heap, put_work_codes stored] at actual
    have add := Ptr.add_nat_ok (off := 0) (n := s.nlen.toNat) lens (by omega : 0 + s.nlen.toNat ≤ s.lens.size)
    unfold OkOn at add
    simp only [Nat.zero_add, clDistPre, next, setI_setI] at add actual
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, clDistPre, lensP, workP, codesP,
      next, add, actual, runX_modify, setI_setI, clDistResult]
  · intro success
    obtain ⟨used, pointer, capacity, invariant⟩ := newMeaning success
    refine ⟨used, pointer, ?_, ?_⟩
    · simpa [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES] using capacity
    · have alphabet : pre.f = fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat := rfl
      rw [alphabet] at invariant
      exact invariant


#print axioms clAfterLens_distance_valid_semantics

/-- Independent valid payload alphabets exclude malformed-tree refusal
at both real constructors. Capacity refusal 1 remains visible until the
default-root table-budget proof excludes it; success is not a premise. -/
theorem clTables_valid_alphabets_boundary
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (validL : Acceptable .litLen (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat))
    (validD : Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) :
    ∃ (retL : Int32) (nextL : CodePtr) (bitsL : UInt32) (workL : Array UInt16) (codesL : Array Code),
      (retL = 0 ∨ retL = 1) ∧
      runX (clTables c) l h = runX (clAfterLens c retL) { l with ret := retL }
        (setI h zs (clLensResult zs s nextL bitsL workL codesL)) ∧
      (retL = 0 → ∃ (offset : Nat) (retD : Int32) (state : InflateState),
        (retD = 0 ∨ retD = 1) ∧ offset ≤ 852 ∧
        state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
        runX (clTables c) l h = runX (clAfterDist c retD) { l with ret := retD } (setI h zs state) ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset
          (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat) ∧
        (retD = 0 → ∃ used,
          state.next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 ∧
          Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat used
            (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat) ∧
          runX (clTables c) l h =
            if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), setI h zs { state with mode := LEN_ })
            else runX (inflate_LEN_ c) { l with ret := 0 } (setI h zs { state with mode := LEN_ }))) := by
  obtain ⟨retL, nextL, bitsL, workL, codesL, workSize, codeSize,
    _pointer, _width, kindsL, firstRun, firstMeaning⟩ :=
    clTables_lens_valid_semantics (l := l) hc hs wf nlen (fun k inside => lengths k (by omega)) validL
  refine ⟨retL, nextL, bitsL, workL, codesL, kindsL, firstRun, ?_⟩
  intro successL
  obtain ⟨offset, pointer, room, _safe, _extent, meaning⟩ := firstMeaning successL
  let middle := clLensResult zs s nextL bitsL workL codesL
  have stored : (setI h zs middle).istates zs = some middle := by simp
  have middleWf : middle.WellFormed := ⟨wf.1, workSize, codeSize⟩
  obtain ⟨retD, nextD, bitsD, workD, codesD, _workSizeD, _codeSizeD,
    _pointerD, _widthD, kindsD, secondRun, retained, distance⟩ :=
    clAfterLens_distance_valid_semantics (l := { l with ret := 0 }) hc stored middleWf
      nlen ndist (fun k inside => lengths (s.nlen.toNat + k) (by change k < s.ndist.toNat at inside; omega))
      offset pointer room _ meaning validD
  let state := clDistResult middle nextD bitsD workD codesD
  have source : runX (clTables c) l h = runX (clAfterDist c retD) { l with ret := retD } (setI h zs state) := by
    rw [successL] at firstRun
    simpa only [setI_setI] using firstRun.trans secondRun
  refine ⟨offset, retD, state, kindsD, room, rfl, pointer, source, retained, ?_⟩
  intro successD
  obtain ⟨used, next, capacity, invariant⟩ := distance successD
  refine ⟨used, next, capacity, invariant, ?_⟩
  rw [successD] at source
  have tail := clAfterDist_success (c := c) (l := { l with ret := 0 }) hc
    (show (setI h zs state).istates zs = some state by simp)
  simpa only [setI_setI] using source.trans tail

#print axioms clTables_valid_alphabets_boundary
/-- Independent EOB validity of the decoded literal slice is exactly the
nonzero actual array cell checked by clTail. -/
theorem actualLengthPrefix_payload_eob {s : InflateState} {decoded : List Nat}
    (count : s.«have».toNat = s.nlen.toNat + s.ndist.toNat)
    (matched : actualLengthPrefix s = decoded)
    (eob : HasEndOfBlock (decoded.take s.nlen.toNat)) : (s.lens.getD 256 0).toNat ≠ 0 := by
  have slices := actualLengthPrefix_payload_slices s count
  rw [← matched, slices.1] at eob
  unfold HasEndOfBlock at eob
  by_cases inside : 256 < s.nlen.toNat
  · rw [Zlib.Inftrees.Proofs.lensOf_getD _ inside] at eob
    exact eob
  · have zero : (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat).getD 256 0 = 0 := by
      simp [Zlib.Inftrees.Proofs.lensOf, List.getD_eq_getElem?_getD, inside]
    exact False.elim (eob zero)

/-- The actual EOB array check reaches the real table constructors without
any assumed callee return. -/
theorem clTail_eob_source_cut
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (nonzero : (s.lens.getD 256 0).toNat ≠ 0) :
    runX (clTail c) l h = runX (clTables c) l h := by
  have inside : 0 + 256 < s.lens.size := by omega
  have read := Ptr.index_ok (off := 0) (i := 256) (WRef.get_istate_lens hs) inside
  let value : UInt16 := s.lens[0 + 256]
  have actual : Ptr.index (lensP c.st) 256 h = .ok (value, h) := by rw [hc]; exact read
  have notZero : value ≠ 0 := by
    intro zero
    apply nonzero
    have cell : s.lens.getD 256 0 = value := by simp [Array.getD, inside, value]
    rw [cell, zero]
    rfl
  have modeRead : rdS c.st (·.mode) h = .ok (CODELENS, h) := by
    rw [hc, rdI_eq, hs]
    simp only [mode]
  have distinct : CODELENS ≠ BAD := by decide
  simp [clTail, runX_bind, runX_lift_ok modeRead, distinct, runX_lift_ok actual, notZero]

#print axioms actualLengthPrefix_payload_eob
#print axioms clTail_eob_source_cut
/-- Match the actual completed lens array to the independent decoded
list, derive both payload alphabets and the EOB test, then execute the
real clTail. Only unresolved capacity result 1 is retained as a branch. -/
theorem clTail_decoded_lengths_boundary
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState} {decoded : List Nat}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (wf : s.WellFormed)
    (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (count : s.«have».toNat = s.nlen.toNat + s.ndist.toNat)
    (matched : actualLengthPrefix s = decoded)
    (eob : HasEndOfBlock (decoded.take s.nlen.toNat))
    (validL : Acceptable .litLen (decoded.take s.nlen.toNat))
    (validD : Acceptable .dist (decoded.drop s.nlen.toNat)) :
    ∃ (retL : Int32) (nextL : CodePtr) (bitsL : UInt32) (workL : Array UInt16) (codesL : Array Code),
      (retL = 0 ∨ retL = 1) ∧
      runX (clTail c) l h = runX (clAfterLens c retL) { l with ret := retL }
        (setI h zs (clLensResult zs s nextL bitsL workL codesL)) ∧
      (retL = 0 → ∃ (offset : Nat) (retD : Int32) (state : InflateState),
        (retD = 0 ∨ retD = 1) ∧ offset ≤ 852 ∧
        state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
        runX (clTail c) l h = runX (clAfterDist c retD) { l with ret := retD } (setI h zs state) ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset
          (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat) ∧
        (retD = 0 → ∃ used,
          state.next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 ∧
          Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat used
            (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat) ∧
          runX (clTail c) l h =
            if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), setI h zs { state with mode := LEN_ })
            else runX (inflate_LEN_ c) { l with ret := 0 } (setI h zs { state with mode := LEN_ }))) := by
  have slices := actualLengthPrefix_payload_slices s count
  have nonzero := actualLengthPrefix_payload_eob count matched eob
  rw [← matched, slices.1] at validL
  rw [← matched, slices.2] at validD
  obtain ⟨_pointer, _safe, nlen, ndist, _have, initialized⟩ := stateInv mode
  have lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15 := by
    rw [← count]
    exact initialized
  have tailCut := clTail_eob_source_cut (l := l) hc hs wf.1 mode nonzero
  obtain ⟨retL, nextL, bitsL, workL, codesL, kindsL, firstRun, ready⟩ :=
    clTables_valid_alphabets_boundary (l := l) hc hs wf nlen ndist lengths validL validD
  refine ⟨retL, nextL, bitsL, workL, codesL, kindsL, tailCut.trans firstRun, ?_⟩
  intro successL
  obtain ⟨offset, retD, state, kindsD, room, lenPtr, distPtr, secondRun, lenMeaning, distance⟩ := ready successL
  refine ⟨offset, retD, state, kindsD, room, lenPtr, distPtr, tailCut.trans secondRun, lenMeaning, ?_⟩
  intro successD
  obtain ⟨used, next, capacity, distMeaning, finalRun⟩ := distance successD
  exact ⟨used, next, capacity, distMeaning, tailCut.trans finalRun⟩

#print axioms clTail_decoded_lengths_boundary
end Zlib.Inflate.Proofs.PayloadTables

namespace Zlib.Inflate.Proofs.PayloadTables
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inftrees
open Zlib.Inflate.Proofs
set_option autoImplicit false

theorem clTables_lens_success_semantics {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (count : s.nlen.toNat ≤ 286)
    (lengths : ∀ k, k < s.nlen.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (valid : Acceptable .litLen (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat)) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852) ∧ bits.toNat ≤ 15 ∧ ret = 0 ∧
      runX (clTables c) l h = runX (clAfterLens c ret) { l with ret := ret }
        (setI h zs (clLensResult zs s next bits work codes)) ∧
      (ret = 0 → ∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852 ∧
        Zlib.Inffast.Spec.LenTableSafe codes 0 bits.toNat ∧
        Zlib.Inftrees.Spec.TableReadExtent LENS codes 0 bits.toNat used ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS codes 0 bits.toNat used
          (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat)) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h zs (clLensPre zs s)).istates zs = some (clLensPre zs s) := by simp
  have lens : Space.get (setI h zs (clLensPre zs s)) (WRef.istate_lens zs) = some s.lens := by
    simpa [clLensPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h zs (clLensPre zs s)) (WRef.istate_work zs) = some s.work := by
    simpa [clLensPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h zs (clLensPre zs s)) (CodeRef.istate_codes zs) = some s.codes := by
    simpa [clLensPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (clLensPre zs s)) LENS
      (.istate_lens zs) 0 s.nlen (.istate_codes zs) 0 9 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inr (Or.inl rfl), lens, work, codes, by simp, by simp,
      by omega, by omega, by simp [Zlib.Inftrees.Spec.capOf, LENS, CODES]; omega,
      by simpa using lengths, (by intro impossible; cases impossible),
      fun _ => by omega, (by intro impossible; cases impossible)⟩
  obtain ⟨result, after, run, frame, tables⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_read_extent _ _ _ _ _ _ _ _ _ _ pre
  obtain ⟨result0, after0, run0, rejected, _accepted, _space⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_correct_ret (setI h zs (clLensPre zs s)) LENS
      (.istate_lens zs) 0 s.nlen (.istate_codes zs) 0 9 (.istate_work zs) 0
      pre.la pre.wa pre.ca pre.hty pre.hgl pre.hgw pre.hgc pre.hro pre.hne
      pre.hla pre.hwa pre.hca pre.hf15 pre.hcodes pre.hlens pre.hdists
  rw [run] at run0
  cases run0
  obtain ⟨capacityResult, capacityAfter, capacityRun, _, _, noRefusal⟩ :=
    Zlib.Inftrees.Proofs.BudgetExecution.inflate_table_default_payload_no_refusal pre (Or.inl ⟨rfl, count, rfl⟩)
  rw [run] at capacityRun
  cases capacityRun
  obtain ⟨semanticResult, semanticAfter, semanticRun, _semanticFrame, meaning⟩ :=
    Zlib.Inftrees.Proofs.constructor_establishes_decode_table_invariant
      _ _ _ _ _ _ _ _ _ _ pre (Or.inl rfl)
  rw [run] at semanticRun
  cases semanticRun
  have bounds := Zlib.Inftrees.Proofs.result_pointer_width_bounds frame (by decide)
    (by
      intro success
      obtain ⟨_, _, _, _, _, extent, _⟩ := tables success
      exact extent.2.1)
  obtain ⟨ret, next, bits⟩ := result
  have pointerBounds : ∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852 := by
    obtain ⟨used, bound, pointer⟩ := bounds.1
    exact ⟨used, by simpa using pointer,
      by simpa [Zlib.Inftrees.Spec.capOf, LENS, CODES] using bound⟩
  obtain ⟨wa, ca, heap, waSize, caSize, _, _, retCases⟩ := frame
  have rejection : ret = -1 ↔ ¬ Acceptable .litLen
      (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat) := by
    simpa [Zlib.Inftrees.Spec.kindOf, Zlib.Inftrees.Spec.lensList,
      Zlib.Inftrees.Proofs.lensOf, pre, CODES, LENS] using rejected
  have kinds : ret = 0 := by
    rcases retCases with ⟨zero, _⟩ | ⟨one | bad, _⟩
    · exact zero
    · exact False.elim (noRefusal one)
    · exact False.elim ((rejection.mp bad) valid)
  refine ⟨ret, next, bits, wa, ca, waSize.trans workSize, caSize.trans codeSize, pointerBounds, bounds.2, kinds, ?_, ?_⟩
  · unfold clTables clAfterLens
    rw [hc]
    have actual := run
    change inflate_table LENS _ _ _ _ _ _ = _ at actual
    simp only [clLensPre] at actual
    rw [heap, put_work_codes stored] at actual
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, clLensPre, lensP, workP, codesP,
      actual, runX_modify, setI_setI, clLensResult]
  · intro success
    obtain ⟨array, used, get, pointer, bound, extent, _, safe, _⟩ := tables success
    have actualGet : Space.get after (CodeRef.istate_codes zs) = some ca := by
      rw [heap, put_work_codes stored]
      simp [Space.get, setI, clLensPre]
    rw [actualGet] at get
    cases get
    obtain ⟨semanticArray, semanticUsed, semanticGet, semanticPointer, _semanticCapacity, invariant⟩ := meaning success
    rw [actualGet] at semanticGet
    cases semanticGet
    have usedEq : semanticUsed = used := by
      have equality := Ptr.ref.inj (semanticPointer.symm.trans pointer)
      omega
    subst semanticUsed
    have alphabet : pre.f = fun k => (s.lens.getD k 0).toNat := by
      funext k
      change (s.lens.getD (0 + k) 0).toNat = _
      rw [Nat.zero_add]
    rw [alphabet] at invariant
    exact ⟨used, by simpa using pointer, by simpa [Zlib.Inftrees.Spec.capOf, LENS, CODES] using bound,
      safe rfl, extent, invariant⟩


theorem clAfterLens_distance_success_semantics {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.ndist.toNat → (s.lens.getD (s.nlen.toNat + k) 0).toNat ≤ 15)
    (offset : Nat) (next : s.next = .ref (.istate_codes zs) offset) (room : offset ≤ 852)
    (lensAlphabet : List Nat)
    (lensInvariant : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS s.codes 0 s.lenbits.toNat offset lensAlphabet)
    (valid : Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592) ∧ bits.toNat ≤ 15 ∧ ret = 0 ∧
      runX (clAfterLens c 0) l h = runX (clAfterDist c ret) { l with ret := ret }
        (setI h zs (clDistResult s next bits work codes)) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS codes 0 s.lenbits.toNat offset lensAlphabet ∧
      (ret = 0 → ∃ used,
        next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS codes offset bits.toNat used
          (Zlib.Inftrees.Proofs.lensOf
            (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) := by
  obtain ⟨lensSize, workSize, codeSize⟩ := wf
  have stored : (setI h zs (clDistPre s)).istates zs = some (clDistPre s) := by simp
  have lens : Space.get (setI h zs (clDistPre s)) (WRef.istate_lens zs) = some s.lens := by
    simpa [clDistPre] using WRef.get_istate_lens stored
  have work : Space.get (setI h zs (clDistPre s)) (WRef.istate_work zs) = some s.work := by
    simpa [clDistPre] using WRef.get_istate_work stored
  have codes : Space.get (setI h zs (clDistPre s)) (CodeRef.istate_codes zs) = some s.codes := by
    simpa [clDistPre] using CodeRef.get_istate_codes stored
  let pre : Zlib.Inftrees.Proofs.CallPre (setI h zs (clDistPre s)) DISTS
      (.istate_lens zs) s.nlen.toNat s.ndist (.istate_codes zs) offset 6 (.istate_work zs) 0 :=
    ⟨s.lens, s.work, s.codes, Or.inr (Or.inr rfl), lens, work, codes, by simp, by simp,
      by omega, by omega, by simp [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES]; omega,
      lengths, (by intro impossible; cases impossible),
      (by intro impossible; cases impossible), fun _ => by omega⟩
  obtain ⟨result, after, array, run, frame, getArray, sameLens, newMeaning⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_preserves_decode_invariant pre (Or.inr rfl)
      lensInvariant (by omega)
  obtain ⟨result0, after0, run0, rejected, _accepted, _space⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_correct_ret (setI h zs (clDistPre s)) DISTS
      (.istate_lens zs) s.nlen.toNat s.ndist (.istate_codes zs) offset 6 (.istate_work zs) 0
      pre.la pre.wa pre.ca pre.hty pre.hgl pre.hgw pre.hgc pre.hro pre.hne
      pre.hla pre.hwa pre.hca pre.hf15 pre.hcodes pre.hlens pre.hdists
  rw [run] at run0
  cases run0
  obtain ⟨capacityResult, capacityAfter, capacityRun, _, _, noRefusal⟩ :=
    Zlib.Inftrees.Proofs.BudgetExecution.inflate_table_default_payload_no_refusal pre (Or.inr ⟨rfl, ndist, rfl⟩)
  rw [run] at capacityRun
  cases capacityRun
  have bounds := Zlib.Inftrees.Proofs.result_pointer_width_bounds frame (by decide)
    (by
      intro success
      obtain ⟨_, _, _, invariant⟩ := newMeaning success
      exact invariant.rootTable.2.1)
  obtain ⟨ret, nextResult, bits⟩ := result
  have pointerBounds : ∃ used, nextResult = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 := by
    obtain ⟨used, bound, pointer⟩ := bounds.1
    exact ⟨used, pointer, by simpa [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES] using bound⟩
  obtain ⟨wa, ca, heap, waSize, caSize, _, _, retCases⟩ := frame
  have actualGet : Space.get after (CodeRef.istate_codes zs) = some ca := by
    rw [heap, put_work_codes stored]
    simp [Space.get, setI, clDistPre]
  rw [actualGet] at getArray
  have sameArray : ca = array := Option.some.inj getArray
  subst array
  change (ret = -1 ↔ ¬ Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) at rejected
  have kinds : ret = 0 := by
    rcases retCases with ⟨zero, _⟩ | ⟨one | bad, _⟩
    · exact zero
    · exact False.elim (noRefusal one)
    · exact False.elim ((rejected.mp bad) valid)
  refine ⟨ret, nextResult, bits, wa, ca, waSize.trans workSize, caSize.trans codeSize, pointerBounds, bounds.2, kinds, ?_, sameLens, ?_⟩
  · unfold clAfterLens clAfterDist
    rw [hc]
    have actual := run
    change inflate_table DISTS _ _ _ _ _ _ = _ at actual
    rw [heap, put_work_codes stored] at actual
    have add := Ptr.add_nat_ok (off := 0) (n := s.nlen.toNat) lens (by omega : 0 + s.nlen.toNat ≤ s.lens.size)
    unfold OkOn at add
    simp only [Nat.zero_add, clDistPre, next, setI_setI] at add actual
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, clDistPre, lensP, workP, codesP,
      next, add, actual, runX_modify, setI_setI, clDistResult]
  · intro success
    obtain ⟨used, pointer, capacity, invariant⟩ := newMeaning success
    refine ⟨used, pointer, ?_, ?_⟩
    · simpa [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES] using capacity
    · have alphabet : pre.f = fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat := rfl
      rw [alphabet] at invariant
      exact invariant


theorem clTables_success_alphabets_boundary
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (validL : Acceptable .litLen (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat))
    (validD : Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) :
    ∃ (retL : Int32) (nextL : CodePtr) (bitsL : UInt32) (workL : Array UInt16) (codesL : Array Code),
      retL = 0 ∧
      runX (clTables c) l h = runX (clAfterLens c retL) { l with ret := retL }
        (setI h zs (clLensResult zs s nextL bitsL workL codesL)) ∧
      (retL = 0 → ∃ (offset : Nat) (retD : Int32) (state : InflateState),
        retD = 0 ∧ offset ≤ 852 ∧
        state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
        runX (clTables c) l h = runX (clAfterDist c retD) { l with ret := retD } (setI h zs state) ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset
          (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat) ∧
        (retD = 0 → ∃ used,
          state.next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 ∧
          Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat used
            (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat) ∧
          runX (clTables c) l h =
            if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), setI h zs { state with mode := LEN_ })
            else runX (inflate_LEN_ c) { l with ret := 0 } (setI h zs { state with mode := LEN_ }))) := by
  obtain ⟨retL, nextL, bitsL, workL, codesL, workSize, codeSize,
    _pointer, _width, kindsL, firstRun, firstMeaning⟩ :=
    clTables_lens_success_semantics (l := l) hc hs wf nlen (fun k inside => lengths k (by omega)) validL
  refine ⟨retL, nextL, bitsL, workL, codesL, kindsL, firstRun, ?_⟩
  intro successL
  obtain ⟨offset, pointer, room, _safe, _extent, meaning⟩ := firstMeaning successL
  let middle := clLensResult zs s nextL bitsL workL codesL
  have stored : (setI h zs middle).istates zs = some middle := by simp
  have middleWf : middle.WellFormed := ⟨wf.1, workSize, codeSize⟩
  obtain ⟨retD, nextD, bitsD, workD, codesD, _workSizeD, _codeSizeD,
    _pointerD, _widthD, kindsD, secondRun, retained, distance⟩ :=
    clAfterLens_distance_success_semantics (l := { l with ret := 0 }) hc stored middleWf
      nlen ndist (fun k inside => lengths (s.nlen.toNat + k) (by change k < s.ndist.toNat at inside; omega))
      offset pointer room _ meaning validD
  let state := clDistResult middle nextD bitsD workD codesD
  have source : runX (clTables c) l h = runX (clAfterDist c retD) { l with ret := retD } (setI h zs state) := by
    rw [successL] at firstRun
    simpa only [setI_setI] using firstRun.trans secondRun
  refine ⟨offset, retD, state, kindsD, room, rfl, pointer, source, retained, ?_⟩
  intro successD
  obtain ⟨used, next, capacity, invariant⟩ := distance successD
  refine ⟨used, next, capacity, invariant, ?_⟩
  rw [successD] at source
  have tail := clAfterDist_success (c := c) (l := { l with ret := 0 }) hc
    (show (setI h zs state).istates zs = some state by simp)
  simpa only [setI_setI] using source.trans tail

#print axioms clTables_lens_success_semantics
#print axioms clAfterLens_distance_success_semantics
#print axioms clTables_success_alphabets_boundary


/-- A real completed CODELENS array matching the independent decoded list
passes its actual EOB check, constructs both real payload tables with no
capacity refusal, and reaches the true LEN_ continuation in the same live
register context. No successful constructor return is a premise. -/
theorem clTail_decoded_lengths_complete
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState} {decoded : List Nat}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (wf : s.WellFormed)
    (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (count : s.«have».toNat = s.nlen.toNat + s.ndist.toNat)
    (matched : actualLengthPrefix s = decoded)
    (eob : HasEndOfBlock (decoded.take s.nlen.toNat))
    (validL : Acceptable .litLen (decoded.take s.nlen.toNat))
    (validD : Acceptable .dist (decoded.drop s.nlen.toNat)) :
    ∃ (state : InflateState) (offset used : Nat), state.mode = LEN_ ∧ offset ≤ 852 ∧ used ≤ 592 ∧
      state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
      state.next = .ref (.istate_codes zs) (offset + used) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset
        (decoded.take s.nlen.toNat) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat used
        (decoded.drop s.nlen.toNat) ∧
      runX (clTail c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), setI h zs state)
        else runX (inflate_LEN_ c) { l with ret := 0 } (setI h zs state) := by
  have slices := actualLengthPrefix_payload_slices s count
  have nonzero := actualLengthPrefix_payload_eob count matched eob
  have litMatched : Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat =
      decoded.take s.nlen.toNat := by rw [← matched, slices.1]
  have distMatched : Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat =
      decoded.drop s.nlen.toNat := by rw [← matched, slices.2]
  rw [← litMatched] at validL
  rw [← distMatched] at validD
  obtain ⟨_pointer, _safe, nlen, ndist, _have, initialized⟩ := stateInv mode
  have lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15 := by
    rw [← count]
    exact initialized
  have tailCut := clTail_eob_source_cut (l := l) hc hs wf.1 mode nonzero
  obtain ⟨retL, nextL, bitsL, workL, codesL, zeroL, _firstRun, ready⟩ :=
    clTables_success_alphabets_boundary (l := l) hc hs wf nlen ndist lengths validL validD
  obtain ⟨offset, retD, state, zeroD, room, lenPointer, distPointer, _secondRun, lenMeaning, installed⟩ := ready zeroL
  obtain ⟨used, next, capacity, distMeaning, source⟩ := installed zeroD
  rw [litMatched] at lenMeaning
  rw [distMatched] at distMeaning
  refine ⟨{ state with mode := LEN_ }, offset, used, rfl, room, capacity, lenPointer, distPointer,
    next, lenMeaning, distMeaning, tailCut.trans source⟩

#print axioms clTail_decoded_lengths_complete

end Zlib.Inflate.Proofs.PayloadTables

namespace Zlib.Inflate.Proofs.CodeLensPayload
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inftrees
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- An independently valid CodeLens parse makes the actual CODELENS body
read all lengths, pass its actual EOB check, install both real payload
decoding tables and reach LEN_ in the same live register context. -/
theorem inflate_CODELENS_format_complete
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {alphabet decoded : List Nat} {rest : List Bool}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (B : BitInv h l bs)
    (parsed : CodeLens alphabet (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (stream l bs) rest decoded)
    (eob : HasEndOfBlock (decoded.take s.nlen.toNat))
    (validL : Acceptable .litLen (decoded.take s.nlen.toNat))
    (validD : Acceptable .dist (decoded.drop s.nlen.toNat)) :
    ∃ (regs : IL) (used : Nat) (state : InflateState) (offset tableUsed : Nat),
      used ≤ bs.length ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used ∧ stream regs (bs.drop used) = rest ∧ ClRegShape l regs ∧
      BitInv (setI h zs state) { regs with ret := 0 } (bs.drop used) ∧
      state.mode = LEN_ ∧ offset ≤ 852 ∧ tableUsed ≤ 592 ∧
      state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
      state.next = .ref (.istate_codes zs) (offset + tableUsed) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset
        (decoded.take s.nlen.toNat) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat tableUsed
        (decoded.drop s.nlen.toNat) ∧
      runX (inflate_CODELENS c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { regs with ret := 0 }), setI h zs state)
        else runX (inflate_LEN_ c) { regs with ret := 0 } (setI h zs state) := by
  obtain ⟨regs, readState, used, readRun, full, frame, size, count, values, bound, readB, cursor, bitBudget, source, matched⟩ :=
    CodeLensCompletion.clRead_forward_full hr hc hz hs wf.1 mode stateInv contents B parsed
  obtain ⟨_readState, _readUsed, _get, _usedBound, _bitInv, regShape, _remaining⟩ := full.1
  have fields : readState.nlen = s.nlen ∧ readState.ndist = s.ndist ∧ readState.mode = CODELENS := by
    rw [frame]
    exact ⟨rfl, rfl, mode⟩
  have readWf : readState.WellFormed := by
    refine ⟨size, ?_, ?_⟩
    · rw [frame]
      exact wf.2.1
    · rw [frame]
      exact wf.2.2
  have readInvariant : CodeLengthInvariant zs readState := by
    obtain ⟨pointer, table, nlen, ndist, _have, _initialized⟩ := stateInv mode
    intro _
    refine ⟨?_, ?_, ?_, ?_, ?_, values⟩
    · rw [frame]
      exact pointer
    · rw [frame]
      exact table
    · rw [fields.1]
      exact nlen
    · rw [fields.2.1]
      exact ndist
    · rw [fields.1, fields.2.1]
      omega
  have readCount : readState.«have».toNat = readState.nlen.toNat + readState.ndist.toNat := by
    rw [fields.1, fields.2.1]
    exact count
  have eob' : HasEndOfBlock (decoded.take readState.nlen.toNat) := by rw [fields.1]; exact eob
  have validL' : Acceptable .litLen (decoded.take readState.nlen.toNat) := by rw [fields.1]; exact validL
  have validD' : Acceptable .dist (decoded.drop readState.nlen.toNat) := by rw [fields.1]; exact validD
  obtain ⟨state, offset, tableUsed, payloadMode, roomL, roomD, lenPointer, distPointer, next, lenMeaning, distMeaning, tailRun⟩ :=
    PayloadTables.clTail_decoded_lengths_complete (h := setI h zs readState) (s := readState) (l := regs) hc (by simp) readWf fields.2.2 readInvariant
      readCount matched eob' validL' validD'
  rw [fields.1] at lenMeaning distMeaning
  have finalB : BitInv (setI h zs state) regs (bs.drop used) := by
    simpa only [setI_setI] using readB.setI zs state
  have finalRetB : BitInv (setI h zs state) { regs with ret := 0 } (bs.drop used) :=
    ⟨finalB.have_eq, finalB.next, finalB.hold_lt⟩
  refine ⟨regs, used, state, offset, tableUsed, bound, cursor, bitBudget, source, regShape, finalRetB,
    payloadMode, roomL, roomD, lenPointer, distPointer, next, lenMeaning, distMeaning, ?_⟩
  rw [inflate_CODELENS_eq, runX_bind, readRun]
  simpa only [setI_setI] using tailRun

#print axioms inflate_CODELENS_format_complete
end Zlib.Inflate.Proofs.CodeLensPayload
