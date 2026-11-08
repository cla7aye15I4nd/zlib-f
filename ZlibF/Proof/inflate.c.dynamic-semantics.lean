import ZlibF.Proof.«inflate.c.dynamic-install»
import ZlibF.Proof.«inftrees.c.decode.install»

set_option autoImplicit false
namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inftrees

/-- `case CODELENS:`. The actual first table constructor establishes
canonical decoding meaning at its real continuation, on the same array
as the existing execution and safety result. All refusals remain included. -/
theorem clTables_lens_run_semantics {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (count : s.nlen.toNat ≤ 286)
    (lengths : ∀ k, k < s.nlen.toNat → (s.lens.getD k 0).toNat ≤ 15) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852) ∧ bits.toNat ≤ 15 ∧
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
  obtain ⟨wa, ca, heap, waSize, caSize, _, _, _⟩ := frame
  refine ⟨ret, next, bits, wa, ca, waSize.trans workSize, caSize.trans codeSize, pointerBounds, bounds.2, ?_, ?_⟩
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

#print axioms clTables_lens_run_semantics

/-- `case CODELENS:` after successful length-table construction.
The actual distance call starts at the previous returned end. It retains
that length alphabet's invariant even on refusal, and establishes the new
distance alphabet on success. The register stores and continuation are
those of the actual source. This is a local construction result. -/
theorem clAfterLens_distance_run_semantics {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.ndist.toNat → (s.lens.getD (s.nlen.toNat + k) 0).toNat ≤ 15)
    (offset : Nat) (next : s.next = .ref (.istate_codes zs) offset) (room : offset ≤ 852)
    (lensAlphabet : List Nat)
    (lensInvariant : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS s.codes 0 s.lenbits.toNat offset lensAlphabet) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592) ∧ bits.toNat ≤ 15 ∧
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
  have bounds := Zlib.Inftrees.Proofs.result_pointer_width_bounds frame (by decide)
    (by
      intro success
      obtain ⟨_, _, _, invariant⟩ := newMeaning success
      exact invariant.rootTable.2.1)
  obtain ⟨ret, nextResult, bits⟩ := result
  have pointerBounds : ∃ used, nextResult = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 := by
    obtain ⟨used, bound, pointer⟩ := bounds.1
    exact ⟨used, pointer, by simpa [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES] using bound⟩
  obtain ⟨wa, ca, heap, waSize, caSize, _, _, _⟩ := frame
  have actualGet : Space.get after (CodeRef.istate_codes zs) = some ca := by
    rw [heap, put_work_codes stored]
    simp [Space.get, setI, clDistPre]
  rw [actualGet] at getArray
  have sameArray : ca = array := Option.some.inj getArray
  subst array
  refine ⟨ret, nextResult, bits, wa, ca, waSize.trans workSize, caSize.trans codeSize, pointerBounds, bounds.2, ?_, sameLens, ?_⟩
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

#print axioms clAfterLens_distance_run_semantics

/-- `case CODELENS:`. Compose both actual constructors. Length-table
refusal retains its original continuation; on length success, the actual
distance continuation has both table meanings on one returned array.
The public mode loop and bitstream refinement are separate obligations. -/
theorem clTables_both_run_semantics {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lenLengths : ∀ k, k < s.nlen.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (distLengths : ∀ k, k < s.ndist.toNat → (s.lens.getD (s.nlen.toNat + k) 0).toNat ≤ 15) :
    ∃ (retL : Int32) (nextL : CodePtr) (bitsL : UInt32) (workL : Array UInt16) (codesL : Array Code),
      runX (clTables c) l h = runX (clAfterLens c retL) { l with ret := retL }
        (setI h zs (clLensResult zs s nextL bitsL workL codesL)) ∧
      (retL = 0 → ∃ (offset : Nat) (retD : Int32) (nextD : CodePtr) (bitsD : UInt32)
          (workD : Array UInt16) (codesD : Array Code),
        nextL = .ref (.istate_codes zs) offset ∧ offset ≤ 852 ∧
        runX (clTables c) l h = runX (clAfterDist c retD) { l with ret := retD }
          (setI h zs (clDistResult (clLensResult zs s nextL bitsL workL codesL) nextD bitsD workD codesD)) ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS codesD 0 bitsL.toNat offset
          (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat) ∧
        (retD = 0 → ∃ used, nextD = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 ∧
          Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS codesD offset bitsD.toNat used
            (Zlib.Inftrees.Proofs.lensOf
              (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat))) := by
  obtain ⟨retL, nextL, bitsL, workL, codesL, workSize, codeSize, _pointer, _width, firstRun, firstMeaning⟩ :=
    clTables_lens_run_semantics hc hs wf nlen lenLengths
  refine ⟨retL, nextL, bitsL, workL, codesL, firstRun, ?_⟩
  intro success
  obtain ⟨offset, pointer, room, _safe, _extent, meaning⟩ := firstMeaning success
  let middle := clLensResult zs s nextL bitsL workL codesL
  have stored : (setI h zs middle).istates zs = some middle := by simp
  have middleWF : middle.WellFormed := ⟨wf.1, workSize, codeSize⟩
  obtain ⟨retD, nextD, bitsD, workD, codesD, _workDSize, _codeDSize, _pointerD, _widthD,
      secondRun, retained, distance⟩ :=
    clAfterLens_distance_run_semantics (l := { l with ret := retL }) hc stored middleWF
      nlen ndist distLengths offset pointer room _ meaning
  refine ⟨offset, retD, nextD, bitsD, workD, codesD, pointer, room, ?_, retained, distance⟩
  rw [success] at firstRun secondRun
  simpa only [setI_setI] using firstRun.trans secondRun

#print axioms clTables_both_run_semantics

/-- `case CODELENS:`. The installed fields explicitly name the two
independently meaningful tables. Keeping these equalities in the theorem
makes the field-store obligation distinct from the constructor model. -/
theorem clTables_both_installed_semantics {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lenLengths : ∀ k, k < s.nlen.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (distLengths : ∀ k, k < s.ndist.toNat → (s.lens.getD (s.nlen.toNat + k) 0).toNat ≤ 15) :
    ∃ (retL : Int32) (nextL : CodePtr) (bitsL : UInt32) (workL : Array UInt16) (codesL : Array Code),
      runX (clTables c) l h = runX (clAfterLens c retL) { l with ret := retL }
        (setI h zs (clLensResult zs s nextL bitsL workL codesL)) ∧
      (retL = 0 → ∃ (offset : Nat) (retD : Int32) (nextD : CodePtr) (bitsD : UInt32) (state : InflateState),
        nextL = .ref (.istate_codes zs) offset ∧ offset ≤ 852 ∧
        state.lencode = .ref (.istate_codes zs) 0 ∧
        state.distcode = .ref (.istate_codes zs) offset ∧
        state.lenbits = bitsL ∧ state.distbits = bitsD ∧ state.next = nextD ∧
        runX (clTables c) l h = runX (clAfterDist c retD) { l with ret := retD } (setI h zs state) ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset
          (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat) ∧
        (retD = 0 → ∃ used, state.next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 ∧
          Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat used
            (Zlib.Inftrees.Proofs.lensOf
              (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat))) := by
  obtain ⟨retL, nextL, bitsL, workL, codesL, firstRun, built⟩ :=
    clTables_both_run_semantics hc hs wf nlen ndist lenLengths distLengths
  refine ⟨retL, nextL, bitsL, workL, codesL, firstRun, ?_⟩
  intro success
  obtain ⟨offset, retD, nextD, bitsD, workD, codesD, pointer, room, run, lengthMeaning, distanceMeaning⟩ := built success
  let state := clDistResult (clLensResult zs s nextL bitsL workL codesL) nextD bitsD workD codesD
  refine ⟨offset, retD, nextD, bitsD, state, pointer, room, rfl, pointer, rfl, rfl, rfl, run,
    lengthMeaning, distanceMeaning⟩

#print axioms clTables_both_installed_semantics

end Zlib.Inflate.Proofs
