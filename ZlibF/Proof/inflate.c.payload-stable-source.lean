import ZlibF.Proof.«inflate.c.dynamic-table-completion»
import ZlibF.Proof.«inftrees.c.default-table-stability»

namespace Zlib.Inflate.Proofs.PayloadStable
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inftrees
open Zlib.Inflate.Proofs
open Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false

/-- Recorded actual constructor provenance. The precondition is produced
from the real caller fields, and Result retains its actual pointwise
work/code write frames. This relation is an output, never a callee premise. -/
def CallTrace (h : Heap) (type : UInt32) (rl : WRef) (ol : Nat) (count : UInt32)
    (rc : CodeRef) (oc : Nat) (bits : UInt32) (rw : WRef) (ow : Nat)
    (result : Int32 × CodePtr × UInt32) (codes : Array Code) : Prop :=
  ∃ pre : Zlib.Inftrees.Proofs.CallPre h type rl ol count rc oc bits rw ow, ∃ after,
    C.run (inflate_table type (.ref rl ol) count (.ref rc oc) bits (.ref rw ow)) h = .ok (result, after) ∧
    Zlib.Inftrees.Spec.Result h rw rc ow oc (Zlib.Inftrees.Spec.capOf type) count.toNat pre.wa pre.ca
      (.ref rc oc) bits result after ∧ Space.get after rc = some codes

theorem clTables_lens_success_stable {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (count : s.nlen.toNat ≤ 286)
    (lengths : ∀ k, k < s.nlen.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (valid : Acceptable .litLen (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat)) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852) ∧ bits.toNat ≤ 15 ∧ ret = 0 ∧
      CallTrace (setI h zs (clLensPre zs s)) LENS (.istate_lens zs) 0 s.nlen (.istate_codes zs) 0 9
        (.istate_work zs) 0 (ret, next, bits) codes ∧
      runX (clTables c) l h = runX (clAfterLens c ret) { l with ret := ret }
        (setI h zs (clLensResult zs s next bits work codes)) ∧
      (ret = 0 → ∃ used, next = .ref (.istate_codes zs) used ∧ used ≤ 852 ∧
        Zlib.Inffast.Spec.LenTableSafe codes 0 bits.toNat ∧
        Zlib.Inftrees.Spec.TableReadExtent LENS codes 0 bits.toNat used ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS codes 0 bits.toNat used
          (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat) ∧
        StableQuery LENS codes 0 bits.toNat) := by
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
  obtain ⟨stableResult, stableHeap, stableRun, stable⟩ :=
    Zlib.Inftrees.Proofs.constructor_establishes_query_stability _ _ _ _ _ _ _ _ _ _ pre (Or.inl rfl)
  rw [run] at stableRun
  cases stableRun
  have originalFrame := frame
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
  refine ⟨ret, next, bits, wa, ca, waSize.trans workSize, caSize.trans codeSize, pointerBounds, bounds.2, kinds, ?_, ?_, ?_⟩
  · refine ⟨pre, after, run, originalFrame, ?_⟩
    rw [heap, put_work_codes stored]
    simp [Space.get, setI, clLensPre]
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
      safe rfl, extent, invariant, stable success ca actualGet⟩


theorem clAfterLens_distance_success_stable {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.ndist.toNat → (s.lens.getD (s.nlen.toNat + k) 0).toNat ≤ 15)
    (offset : Nat) (next : s.next = .ref (.istate_codes zs) offset) (room : offset ≤ 852)
    (lensAlphabet : List Nat)
    (lensInvariant : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS s.codes 0 s.lenbits.toNat offset lensAlphabet)
    (lensSafe : Zlib.Inffast.Spec.LenTableSafe s.codes 0 s.lenbits.toNat)
    (lensStable : StableQuery LENS s.codes 0 s.lenbits.toNat)
    (valid : Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) :
    ∃ (ret : Int32) (next : CodePtr) (bits : UInt32) (work : Array UInt16) (codes : Array Code),
      work.size = 288 ∧ codes.size = 1444 ∧
      (∃ used, next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592) ∧ bits.toNat ≤ 15 ∧ ret = 0 ∧
      CallTrace (setI h zs (clDistPre s)) DISTS (.istate_lens zs) s.nlen.toNat s.ndist (.istate_codes zs) offset 6
        (.istate_work zs) 0 (ret, next, bits) codes ∧
      runX (clAfterLens c 0) l h = runX (clAfterDist c ret) { l with ret := ret }
        (setI h zs (clDistResult s next bits work codes)) ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS codes 0 s.lenbits.toNat offset lensAlphabet ∧
      Zlib.Inffast.Spec.LenTableSafe codes 0 s.lenbits.toNat ∧
      StableQuery LENS codes 0 s.lenbits.toNat ∧
      (ret = 0 → ∃ used,
        next = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 ∧
        Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS codes offset bits.toNat used
          (Zlib.Inftrees.Proofs.lensOf
            (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat) ∧
        StableQuery DISTS codes offset bits.toNat ∧ Zlib.Inffast.Spec.DistTableSafe codes offset bits.toNat) := by
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
  obtain ⟨result, after, array, run, frame, getArray, sameLens, sameStable, newMeaning⟩ :=
    Zlib.Inftrees.Proofs.DefaultStability.constructor_preserves_installed_stable pre (Or.inr rfl)
      lensInvariant lensStable (by omega)
  obtain ⟨safeResult, safeHeap, safeArray, safeRun, _safeFrame, safeGet, retainedSafe, _extentSafe, _querySafe⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_dists_preserves_lens pre (by omega) lensSafe lensInvariant.readExtent
  rw [run] at safeRun
  cases safeRun
  have sameSafeArray : safeArray = array := Option.some.inj (safeGet.symm.trans getArray)
  subst safeArray
  obtain ⟨extentResult, extentHeap, extentRun, _extentFrame, distanceSafe⟩ :=
    Zlib.Inftrees.Proofs.inflate_table_read_extent _ _ _ _ _ _ _ _ _ _ pre
  rw [run] at extentRun
  cases extentRun
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
      obtain ⟨_, _, _, invariant, _stable⟩ := newMeaning success
      exact invariant.rootTable.2.1)
  obtain ⟨ret, nextResult, bits⟩ := result
  have pointerBounds : ∃ used, nextResult = .ref (.istate_codes zs) (offset + used) ∧ used ≤ 592 := by
    obtain ⟨used, bound, pointer⟩ := bounds.1
    exact ⟨used, pointer, by simpa [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES] using bound⟩
  have originalFrame := frame
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
  refine ⟨ret, nextResult, bits, wa, ca, waSize.trans workSize, caSize.trans codeSize, pointerBounds, bounds.2, kinds, ?_, ?_, sameLens, retainedSafe, sameStable, ?_⟩
  · exact ⟨pre, after, run, originalFrame, actualGet⟩
  · unfold clAfterLens clAfterDist
    rw [hc]
    have actual := run
    change inflate_table DISTS _ _ _ _ _ _ = _ at actual
    rw [heap, put_work_codes stored] at actual
    have add := Ptr.add_nat_ok (off := 0) (n := s.nlen.toNat) lens (by omega : 0 + s.nlen.toNat ≤ s.lens.size)
    unfold OkOn at add
    simp only [Nat.zero_add, clDistPre, next, setI_setI] at add actual
    simp [runX_bind, runX_lift, wrI_eq, ldI_eq, hs, clDistPre, lensP, workP,
      next, add, actual, runX_modify, setI_setI, clDistResult]
  · intro success
    obtain ⟨used, pointer, capacity, invariant, stable⟩ := newMeaning success
    obtain ⟨safeArray, _safeUsed, safeGet, _safePointer, _safeCapacity, _safeExtent, _safeCode, _safeLen, safeDist⟩ := distanceSafe success
    have sameSafe : safeArray = ca := Option.some.inj (safeGet.symm.trans actualGet)
    subst safeArray
    refine ⟨used, pointer, ?_, ?_, stable, safeDist rfl⟩
    · simpa [Zlib.Inftrees.Spec.capOf, LENS, DISTS, CODES] using capacity
    · have alphabet : pre.f = fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat := rfl
      rw [alphabet] at invariant
      exact invariant




/-- Both constructor executions and actual write frames, retained at the
LEN_ boundary. The earlier LENS storage is the actual input of DISTS. -/
def PairTrace (h : Heap) (zs : Nat) (before middle state : InflateState) (offset : Nat) : Prop :=
  ∃ (nextL : CodePtr) (bitsL : UInt32) (workL : Array UInt16) (codesL : Array Code)
    (nextD : CodePtr) (bitsD : UInt32) (workD : Array UInt16) (codesD : Array Code),
    middle = clLensResult zs before nextL bitsL workL codesL ∧
    state = { clDistResult middle nextD bitsD workD codesD with mode := LEN_ } ∧
    nextL = .ref (.istate_codes zs) offset ∧
    CallTrace (setI h zs (clLensPre zs before)) LENS (.istate_lens zs) 0 before.nlen (.istate_codes zs) 0 9
      (.istate_work zs) 0 (0, nextL, bitsL) codesL ∧
    CallTrace (setI (setI h zs middle) zs (clDistPre middle)) DISTS (.istate_lens zs) middle.nlen.toNat middle.ndist
      (.istate_codes zs) offset 6 (.istate_work zs) 0 (0, nextD, bitsD) codesD

/-- Actual default LENS and DISTS constructors install both decoder
invariants and suffix-stable query representations. Independent alphabet
validity derives both successful returns and budget guards. Only table
metadata fields change; the live input/output registers are retained. -/
theorem clTables_success_alphabets_stable_boundary
    {c : Ctx} {l : IL} {h : Heap} {zs : Nat} {s : InflateState}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (wf : s.WellFormed) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (validL : Acceptable .litLen (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat))
    (validD : Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)) :
    ∃ (middle state : InflateState) (offset used : Nat),
      state.mode = LEN_ ∧ state.WellFormed ∧ offset ≤ 852 ∧ used ≤ 592 ∧
      state.lencode = .ref (.istate_codes zs) 0 ∧ state.distcode = .ref (.istate_codes zs) offset ∧
      state.next = .ref (.istate_codes zs) (offset + used) ∧
      state = { s with next := state.next, lencode := state.lencode, distcode := state.distcode, lenbits := state.lenbits, distbits := state.distbits, work := state.work, codes := state.codes, mode := state.mode } ∧
      PairTrace h zs s middle state offset ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset
        (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat) ∧
      Zlib.Inffast.Spec.LenTableSafe state.codes 0 state.lenbits.toNat ∧
      StableQuery LENS state.codes 0 state.lenbits.toNat ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat used
        (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat) ∧
      StableQuery DISTS state.codes offset state.distbits.toNat ∧
      Zlib.Inffast.Spec.DistTableSafe state.codes offset state.distbits.toNat ∧
      runX (clTables c) l h =
        if c.flush = Z_TREES then .ok ((.error Ex.leave, { l with ret := 0 }), setI h zs state)
        else runX (inflate_LEN_ c) { l with ret := 0 } (setI h zs state) := by
  obtain ⟨retL, nextL, bitsL, workL, codesL, workSize, codeSize,
    _pointer, _width, zeroL, firstTrace, firstRun, firstMeaning⟩ :=
    clTables_lens_success_stable (l := l) hc hs wf nlen (fun k inside => lengths k (by omega)) validL
  subst retL
  obtain ⟨offset, pointer, room, _safe, _extent, meaning, stable⟩ := firstMeaning rfl
  let middle := clLensResult zs s nextL bitsL workL codesL
  have stored : (setI h zs middle).istates zs = some middle := by simp
  have middleWf : middle.WellFormed := ⟨wf.1, workSize, codeSize⟩
  obtain ⟨retD, nextD, bitsD, workD, codesD, workSizeD, codeSizeD,
    _pointerD, _widthD, zeroD, secondTrace, secondRun, retained, retainedSafe, retainedStable, distance⟩ :=
    clAfterLens_distance_success_stable (l := { l with ret := 0 }) hc stored middleWf
      nlen ndist (fun k inside => lengths (s.nlen.toNat + k) (by change k < s.ndist.toNat at inside; omega))
      offset pointer room _ meaning _safe stable validD
  subst retD
  obtain ⟨used, next, capacity, distInv, distStable, distSafe⟩ := distance rfl
  let state := { clDistResult middle nextD bitsD workD codesD with mode := LEN_ }
  have source : runX (clTables c) l h = runX (clAfterDist c 0) { l with ret := 0 }
      (setI h zs (clDistResult middle nextD bitsD workD codesD)) := by
    simpa only [setI_setI] using firstRun.trans secondRun
  have tail := clAfterDist_success (c := c) (l := { l with ret := 0 }) hc
    (show (setI h zs (clDistResult middle nextD bitsD workD codesD)).istates zs =
      some (clDistResult middle nextD bitsD workD codesD) by simp)
  refine ⟨middle, state, offset, used, rfl, ⟨wf.1, workSizeD, codeSizeD⟩, room, capacity, rfl, pointer, next,
    rfl, ⟨nextL, bitsL, workL, codesL, nextD, bitsD, workD, codesD, rfl, rfl, pointer, firstTrace, secondTrace⟩,
    retained, retainedSafe, retainedStable, distInv, distStable, distSafe, ?_⟩
  simpa only [setI_setI] using source.trans tail

#print axioms clTables_lens_success_stable
#print axioms clAfterLens_distance_success_stable
#print axioms clTables_success_alphabets_stable_boundary
end Zlib.Inflate.Proofs.PayloadStable
