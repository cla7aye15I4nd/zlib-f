import ZlibF.Proof.«inflate.c.dynamic-table-completion»
import ZlibF.Proof.«inftrees.c.decode.stability-rejection»
import ZlibF.Proof.«inflate.c.codelens-dispatch»

/-!
# inflate.c: the `CODELENS` tables decode their codes for every continuation

`clTables_lens_success_semantics` and `clAfterLens_distance_success_semantics`
with the suffix stability of each installed table
(`constructor_establishes_query_stability`), and the stability of the
literal/length table kept when the distance table is written after it
(`query_stability_of_prefix`). `clTail_valid_tables` composes them from a
completed `CODELENS` lens array with valid alphabets.
-/

namespace Zlib.Inflate.Proofs.MeaningDynamicTables
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inftrees
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.PayloadTables
set_option autoImplicit false

theorem clTables_lens_stable {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
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
          (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat) ∧
        Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS codes 0 bits.toNat) := by
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
  obtain ⟨stableResult, stableAfter, stableRun, stableMeaning⟩ :=
    Zlib.Inftrees.Proofs.constructor_establishes_query_stability
      _ _ _ _ _ _ _ _ _ _ pre (Or.inl rfl)
  rw [run] at stableRun
  cases stableRun
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
      safe rfl, extent, invariant, stableMeaning success ca actualGet⟩


theorem clAfterLens_distance_stable {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.ndist.toNat → (s.lens.getD (s.nlen.toNat + k) 0).toNat ≤ 15)
    (offset : Nat) (next : s.next = .ref (.istate_codes zs) offset) (room : offset ≤ 852)
    (lensAlphabet : List Nat)
    (lensInvariant : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS s.codes 0 s.lenbits.toNat offset lensAlphabet)
    (lensStable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS s.codes 0 s.lenbits.toNat)
    (valid : Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592) ∧ bits.toNat ≤ 15 ∧ ret = 0 ∧
      runX (clAfterLens c 0) l h = runX (clAfterDist c ret) { l with ret := ret }
        (setI h zs (clDistResult s next bits work codes)) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS codes 0 s.lenbits.toNat offset lensAlphabet ∧
      Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS codes 0 s.lenbits.toNat ∧
      (ret = 0 → ∃ used,
        next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS codes offset bits.toNat used
          (Zlib.Inftrees.Proofs.lensOf
            (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat) ∧
        Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS codes offset bits.toNat) := by
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
  obtain ⟨stableResult, stableAfter, stableRun, stableMeaning⟩ :=
    Zlib.Inftrees.Proofs.constructor_establishes_query_stability
      _ _ _ _ _ _ _ _ _ _ pre (Or.inr rfl)
  rw [run] at stableRun
  cases stableRun
  have bounds := Zlib.Inftrees.Proofs.result_pointer_width_bounds frame (by decide)
    (by
      intro success
      obtain ⟨_, _, _, invariant⟩ := newMeaning success
      exact invariant.rootTable.2.1)
  obtain ⟨ret, nextResult, bits⟩ := result
  have pointerBounds : ∃ used, nextResult = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 := by
    obtain ⟨used, bound, pointer⟩ := bounds.1
    exact ⟨used, pointer, by simpa [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES] using bound⟩
  obtain ⟨wa, ca, heap, waSize, caSize, _, codeFrame, retCases⟩ := frame
  have actualGet : Space.get after (CodeRef.istate_codes zs) = some ca := by
    rw [heap, put_work_codes stored]
    simp [Space.get, setI, clDistPre]
  have keptStable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca 0 s.lenbits.toNat :=
    Zlib.Inftrees.Proofs.query_stability_of_prefix LENS s.codes ca 0 s.lenbits.toNat offset (Or.inl rfl)
      lensInvariant.readExtent lensStable (fun i _ inside => codeFrame i (Or.inl (by omega)))
  rw [actualGet] at getArray
  have sameArray : ca = array := Option.some.inj getArray
  subst array
  change (ret = -1 ↔ ¬ Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) at rejected
  have kinds : ret = 0 := by
    rcases retCases with ⟨zero, _⟩ | ⟨one | bad, _⟩
    · exact zero
    · exact False.elim (noRefusal one)
    · exact False.elim ((rejected.mp bad) valid)
  refine ⟨ret, nextResult, bits, wa, ca, waSize.trans workSize, caSize.trans codeSize, pointerBounds, bounds.2, kinds, ?_, sameLens, keptStable, ?_⟩
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
      exact ⟨invariant, stableMeaning success ca actualGet⟩



/-- A completed `CODELENS` lens array with valid alphabets passes the
end-of-block check, installs both tables with `Inv` and suffix-stable
queries, and reaches `LEN_`. -/
theorem clTail_valid_tables
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (wf : s.WellFormed)
    (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (count : s.«have».toNat = s.nlen.toNat + s.ndist.toNat)
    (eob : HasEndOfBlock ((actualLengthPrefix s).take s.nlen.toNat))
    (validL : Acceptable .litLen ((actualLengthPrefix s).take s.nlen.toNat))
    (validD : Acceptable .dist ((actualLengthPrefix s).drop s.nlen.toNat)) :
    ∃ (nextL : CodePtr) (bitsL : UInt32) (workL : Array UInt16) (codesL : Array Code)
      (nextD : CodePtr) (bitsD : UInt32) (workD : Array UInt16) (codesD : Array Code) (offset : Nat),
      let state := { clDistResult (clLensResult zs s nextL bitsL workL codesL) nextD bitsD workD codesD with
        mode := LEN_ }
      state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
      (∃ used, Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat used
        ((actualLengthPrefix s).take s.nlen.toNat)) ∧
      Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS state.codes 0 state.lenbits.toNat ∧
      (∃ used, Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat used
        ((actualLengthPrefix s).drop s.nlen.toNat)) ∧
      Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS state.codes offset state.distbits.toNat ∧
      runX (clTail c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), setI h zs state)
        else runX (inflate_LEN_ c) { l with ret := 0 } (setI h zs state) := by
  have slices := actualLengthPrefix_payload_slices s count
  have nonzero := actualLengthPrefix_payload_eob count rfl eob
  rw [slices.1] at validL
  rw [slices.2] at validD
  obtain ⟨_pointer, _safe, nlen, ndist, _have, initialized⟩ := stateInv mode
  have lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15 := by
    rw [← count]
    exact initialized
  have tailCut := clTail_eob_source_cut (l := l) hc hs wf.1 mode nonzero
  obtain ⟨retL, nextL, bitsL, workL, codesL, workSize, codeSize,
    _pointer, _width, zeroL, firstRun, firstMeaning⟩ :=
    clTables_lens_stable (l := l) hc hs wf nlen (fun k inside => lengths k (by omega)) validL
  obtain ⟨offset, pointer, room, _safe, _extent, meaning, stableL⟩ := firstMeaning zeroL
  let middle := clLensResult zs s nextL bitsL workL codesL
  have stored : (setI h zs middle).istates zs = some middle := by simp
  have middleWf : middle.WellFormed := ⟨wf.1, workSize, codeSize⟩
  obtain ⟨retD, nextD, bitsD, workD, codesD, _workSizeD, _codeSizeD,
    _pointerD, _widthD, zeroD, secondRun, retained, retainedStable, distance⟩ :=
    clAfterLens_distance_stable (l := { l with ret := 0 }) hc stored middleWf
      nlen ndist (fun k inside => lengths (s.nlen.toNat + k) (by change k < s.ndist.toNat at inside; omega))
      offset pointer room _ meaning stableL validD
  obtain ⟨used, _next, _capacity, invariantD, stableD⟩ := distance zeroD
  let state := clDistResult middle nextD bitsD workD codesD
  have source : runX (clTables c) l h = runX (clAfterDist c retD) { l with ret := retD } (setI h zs state) := by
    rw [zeroL] at firstRun
    simpa only [setI_setI] using firstRun.trans secondRun
  rw [zeroD] at source
  have tail := clAfterDist_success (c := c) (l := { l with ret := 0 }) hc
    (show (setI h zs state).istates zs = some state by simp)
  refine ⟨nextL, bitsL, workL, codesL, nextD, bitsD, workD, codesD, offset, rfl, pointer,
    ⟨offset, ?_⟩, retainedStable, ⟨used, ?_⟩, stableD, ?_⟩
  · rw [slices.1]; exact retained
  · rw [slices.2]; exact invariantD
  · rw [tailCut, source]
    simpa only [setI_setI] using tail

/-- A missing end-of-block length goes to `BAD`. -/
theorem clTail_missing_eob {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (zero : (s.lens.getD 256 0).toNat = 0) :
    ∃ i, runX (clTail c) l h = .ok ((.ok (), l), tcBadHeap h r zs z s i) := by
  have inside : 0 + 256 < s.lens.size := by omega
  have read := Ptr.index_ok (off := 0) (i := 256) (WRef.get_istate_lens hs) inside
  have value : s.lens[0 + 256] = 0 := by
    have cell : s.lens.getD 256 0 = s.lens[0 + 256] := by simp [Array.getD, inside]
    rw [← cell]
    exact UInt16.toNat_inj.mp zero
  have actual : Ptr.index (lensP c.st) 256 h = .ok ((0 : UInt16), h) := by
    rw [hc, ← value]; exact read
  have modeRead : rdS c.st (·.mode) h = .ok (CODELENS, h) := by
    rw [hc, rdI_eq, hs]
    simp only [mode]
  have distinct : CODELENS ≠ BAD := by decide
  obtain ⟨i, _, bad⟩ := tcBadMode_run (c := c) "invalid code -- missing end-of-block" lit_missing_eob
    hr hc hz hs
  refine ⟨i, ?_⟩
  simp [clTail, runX_bind, runX_lift_ok modeRead, distinct, runX_lift_ok actual, runX_lift_ok bad, runX_pure]

/-- A completed `CODELENS` lens array that fails the end-of-block check or
has an unacceptable literal/length or distance code goes to `BAD`; only the
return register changes. -/
theorem clTail_invalid
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (wf : s.WellFormed)
    (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (count : s.«have».toNat = s.nlen.toNat + s.ndist.toNat) (nlenLow : 257 ≤ s.nlen.toNat)
    (invalid : ¬ (HasEndOfBlock ((actualLengthPrefix s).take s.nlen.toNat) ∧
      Acceptable .litLen ((actualLengthPrefix s).take s.nlen.toNat) ∧
      Acceptable .dist ((actualLengthPrefix s).drop s.nlen.toNat))) :
    ∃ l' h', runX (clTail c) l h = .ok ((.ok (), l'), h') ∧ l'.in_ = l.in_ ∧ l'.have_ = l.have_ ∧
      ∀ zs' s', c.st = some (.tab zs') → h'.istates zs' = some s' → s'.mode = BAD := by
  have slices := actualLengthPrefix_payload_slices s count
  obtain ⟨_pointer, _safe, nlen, ndist, _have, initialized⟩ := stateInv mode
  have lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15 := by
    rw [← count]
    exact initialized
  have badMode' : ∀ (h1 : Heap) (s1 : InflateState) (i : Nat) zs' s',
      c.st = some (.tab zs') → (tcBadHeap h1 r zs z s1 i).istates zs' = some s' → s'.mode = BAD := by
    intro h1 s1 i zs' s' st' hs'
    rw [hc] at st'
    cases st'
    simp only [tcBadHeap, setI_istates_same, Option.some.injEq] at hs'
    rw [← hs']
  by_cases eob : HasEndOfBlock ((actualLengthPrefix s).take s.nlen.toNat)
  · have nonzero := actualLengthPrefix_payload_eob count rfl eob
    have tailCut := clTail_eob_source_cut (l := l) hc hs wf.1 mode nonzero
    by_cases validL : Acceptable .litLen ((actualLengthPrefix s).take s.nlen.toNat)
    · have validD : ¬ Acceptable .dist ((actualLengthPrefix s).drop s.nlen.toNat) :=
        fun v => invalid ⟨eob, validL, v⟩
      rw [slices.1] at validL
      rw [slices.2] at validD
      obtain ⟨retL, nextL, bitsL, workL, codesL, workSize, codeSize,
        _pointer, _width, zeroL, firstRun, firstMeaning⟩ :=
        clTables_lens_success_semantics (l := l) hc hs wf nlen (fun k inside => lengths k (by omega)) validL
      obtain ⟨offset, pointer, room, _safe, _extent, meaning⟩ := firstMeaning zeroL
      let middle := clLensResult zs s nextL bitsL workL codesL
      have stored : (setI h zs middle).istates zs = some middle := by simp
      have middleWf : middle.WellFormed := ⟨wf.1, workSize, codeSize⟩
      obtain ⟨retD, nextD, bitsD, workD, codesD, _workSizeD, _codeSizeD,
        _pointerD, _widthD, secondRun, _retained, distance⟩ :=
        clAfterLens_distance_run_semantics (l := { l with ret := 0 }) hc stored middleWf
          nlen ndist (fun k inside => lengths (s.nlen.toNat + k) (by change k < s.ndist.toNat at inside; omega))
          offset pointer room _ meaning
      have notZero : retD ≠ 0 := by
        intro zero
        obtain ⟨_, _, _, inv⟩ := distance zero
        exact validD inv.acceptable
      let state := clDistResult middle nextD bitsD workD codesD
      have stored2 : (setI h zs state).istates zs = some state := by simp
      obtain ⟨i, _, bad⟩ := clAfterDist_error (l := { l with ret := retD }) hr hc
        (by simpa using hz) stored2 notZero
      refine ⟨{ l with ret := retD }, tcBadHeap (setI h zs state) r zs z state i, ?_, rfl, rfl, badMode' _ _ _⟩
      rw [tailCut, firstRun, zeroL, secondRun]
      simpa only [setI_setI] using bad
    · rw [slices.1] at validL
      obtain ⟨retL, nextL, bitsL, workL, codesL, _workSize, _codeSize,
        _pointer, _width, firstRun, firstMeaning⟩ :=
        clTables_lens_run_semantics (l := l) hc hs wf nlen (fun k inside => lengths k (by omega))
      have notZero : retL ≠ 0 := by
        intro zero
        obtain ⟨_, _, _, _, _, inv⟩ := firstMeaning zero
        exact validL inv.acceptable
      let middle := clLensResult zs s nextL bitsL workL codesL
      have stored : (setI h zs middle).istates zs = some middle := by simp
      obtain ⟨i, _, bad⟩ := clAfterLens_error (l := { l with ret := retL }) hr hc
        (by simpa using hz) stored notZero
      refine ⟨{ l with ret := retL }, tcBadHeap (setI h zs middle) r zs z middle i, ?_, rfl, rfl, badMode' _ _ _⟩
      rw [tailCut, firstRun]
      exact bad
  · have zero : (s.lens.getD 256 0).toNat = 0 := by
      apply Decidable.byContradiction
      intro nz
      apply eob
      rw [slices.1]
      unfold HasEndOfBlock
      rw [Zlib.Inftrees.Proofs.lensOf_getD _ (by omega)]
      exact nz
    obtain ⟨i, bad⟩ := clTail_missing_eob (l := l) hr hc hz hs wf.1 mode zero
    exact ⟨l, tcBadHeap h r zs z s i, bad, rfl, rfl, badMode' _ _ _⟩

#print axioms clTail_invalid

#print axioms clTables_lens_stable
#print axioms clAfterLens_distance_stable
#print axioms clTail_valid_tables

end Zlib.Inflate.Proofs.MeaningDynamicTables
