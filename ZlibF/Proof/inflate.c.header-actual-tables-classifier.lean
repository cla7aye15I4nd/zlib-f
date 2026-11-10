import ZlibF.Proof.«inflate.c.header-actual-distance-rejection»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public Zlib.Inftrees
open Zlib.Inflate.Proofs
open Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Rejection provenance retains the real first/second call heaps and
both returned storage frames when DISTS rejected after LENS succeeded. -/
def RejectedConstructorTrace (h : Heap) (zs : Nat) (s state : InflateState) : Prop :=
  (∃ next root work codes,
    state = clLensResult zs s next root work codes ∧
    PayloadStable.CallTrace (setI h zs (clLensPre zs s)) LENS (.istate_lens zs) 0 s.nlen (.istate_codes zs) 0 9
      (.istate_work zs) 0 (-1, next, root) codes) ∨
  (∃ nextL bitsL workL codesL middle offset nextD bitsD workD codesD,
    middle = clLensResult zs s nextL bitsL workL codesL ∧ nextL = .ref (.istate_codes zs) offset ∧
    state = clDistResult middle nextD bitsD workD codesD ∧
    PayloadStable.CallTrace (setI h zs (clLensPre zs s)) LENS (.istate_lens zs) 0 s.nlen (.istate_codes zs) 0 9
      (.istate_work zs) 0 (0, nextL, bitsL) codesL ∧
    PayloadStable.CallTrace (setI (setI h zs middle) zs (clDistPre middle)) DISTS (.istate_lens zs) middle.nlen.toNat middle.ndist
      (.istate_codes zs) offset 6 (.istate_work zs) 0 (-1, nextD, bitsD) codesD)

structure TablesRejected (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState) (l : IL) where
  state : InflateState
  message : Nat
  frame : state = {s with next := state.next, lencode := state.lencode, distcode := state.distcode, lenbits := state.lenbits, distbits := state.distbits, work := state.work, codes := state.codes, mode := state.mode}
  calls : RejectedConstructorTrace h zs s state
  actual : runX (clTables c) l h = .ok ((.ok (), {l with ret := -1}), tcBadHeap h r zs z state message)

structure TablesReady (c : Ctx) (h : Heap) (zs : Nat) (s : InflateState) (l : IL) where
  middle : InflateState
  state : InflateState
  offset : Nat
  used : Nat
  mode : state.mode = LEN_
  wf : state.WellFormed
  roomL : offset ≤ 852
  roomD : used ≤ 592
  lenPtr : state.lencode = .ref (.istate_codes zs) 0
  distPtr : state.distcode = .ref (.istate_codes zs) offset
  nextPtr : state.next = .ref (.istate_codes zs) (offset + used)
  frame : state = {s with next := state.next, lencode := state.lencode, distcode := state.distcode, lenbits := state.lenbits, distbits := state.distbits, work := state.work, codes := state.codes, mode := state.mode}
  calls : PayloadStable.PairTrace h zs s middle state offset
  lens : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS state.codes 0 state.lenbits.toNat offset
    (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat)
  safeL : Zlib.Inffast.Spec.LenTableSafe state.codes 0 state.lenbits.toNat
  stableL : StableQuery LENS state.codes 0 state.lenbits.toNat
  dists : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS state.codes offset state.distbits.toNat used
    (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)
  stableD : StableQuery DISTS state.codes offset state.distbits.toNat
  safeD : Zlib.Inffast.Spec.DistTableSafe state.codes offset state.distbits.toNat
  actual : runX (clTables c) l h = if c.flush = Z_TREES then .ok ((.error Ex.leave, {l with ret := 0}), setI h zs state)
    else runX (inflate_LEN_ c) {l with ret := 0} (setI h zs state)

/-- The real two constructors automatically reject or produce exact
stable payload tables. No acceptable alphabet or constructor success is
assumed. Branch selection examines the actual input lens array. -/
theorem clTables_branch_classifier
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {l : IL}
    (E : Env c h r zs z s) (wf : s.WellFormed)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15) :
    Nonempty (TablesRejected c h r zs z s l) ∨ Nonempty (TablesReady c h zs s l) := by
  by_cases validL : Acceptable .litLen (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD k 0).toNat) s.nlen.toNat)
  · by_cases validD : Acceptable .dist (Zlib.Inftrees.Proofs.lensOf (fun k => (s.lens.getD (s.nlen.toNat + k) 0).toNat) s.ndist.toNat)
    · obtain ⟨middle, state, offset, used, mode, stateWf, roomL, roomD, lenPtr, distPtr, nextPtr, frame,
        calls, lens, safeL, stableL, dists, stableD, safeD, actual⟩ :=
        PayloadStable.clTables_success_alphabets_stable_boundary E.st E.hs wf nlen ndist lengths validL validD
      exact Or.inr ⟨⟨middle, state, offset, used, mode, stateWf, roomL, roomD, lenPtr, distPtr, nextPtr, frame,
        calls, lens, safeL, stableL, dists, stableD, safeD, actual⟩⟩
    · obtain ⟨retL, nextL, bitsL, workL, codesL, workSize, codeSize, _pointer, _width, zero, firstCall, firstRun, accepted⟩ :=
        PayloadStable.clTables_lens_success_stable (l := l) E.st E.hs wf nlen (fun k inside => lengths k (by omega)) validL
      obtain ⟨offset, pointer, room, _safe, _extent, _inv, _stable⟩ := accepted zero
      let middle := clLensResult zs s nextL bitsL workL codesL
      have middleE : Env c (setI h zs middle) r zs z middle := ⟨E.strm, E.st, by rw [ZStreamRef.get_setI]; exact E.hz, setI_istates_same ..⟩
      have middleWf : middle.WellFormed := ⟨wf.1, workSize, codeSize⟩
      obtain ⟨nextD, bitsD, workD, codesD, i, distanceCall, distanceRun⟩ :=
        invalid_distance_source (l := {l with ret := 0}) middleE middleWf nlen ndist
          (fun k inside => lengths (s.nlen.toNat + k) (by change k < s.ndist.toNat at inside; omega)) pointer room validD
      rw [zero] at firstRun firstCall
      let state := clDistResult middle nextD bitsD workD codesD
      have actual := firstRun.trans distanceRun
      apply Or.inl
      refine ⟨⟨state, i, by rfl, Or.inr ⟨nextL, bitsL, workL, codesL, middle, offset, nextD, bitsD, workD, codesD,
        rfl, pointer, rfl, firstCall, distanceCall⟩, ?_⟩⟩
      simpa only [state, middle, tcBadHeap, ZStreamRef.put_setI, setI_setI] using actual
  · obtain ⟨next, root, work, codes, i, call, actual⟩ := invalid_lens_source (l := l) E wf nlen (fun k inside => lengths k (by omega)) validL
    apply Or.inl
    refine ⟨⟨clLensResult zs s next root work codes, i, rfl, Or.inl ⟨next, root, work, codes, rfl, call⟩, ?_⟩⟩
    simpa only [tcBadHeap, ZStreamRef.put_setI, setI_setI] using actual

#print axioms clTables_branch_classifier
end Zlib.Inflate.Proofs.ActualHeader
