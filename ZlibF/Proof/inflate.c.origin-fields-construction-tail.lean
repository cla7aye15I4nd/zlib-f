import ZlibF.Proof.«inflate.c.origin-fields-dictionary»
import ZlibF.Proof.«inflate.c.dynamic-semantics»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Length reading only changes the initialized lens prefix and its count,
or the error mode/message. This observes the actual complete loop. -/
theorem originFieldFrameX_clRead (r : ZStreamRef) (c : Ctx) (root : c.strm = some r) :
    OriginFieldFrameX r c.st (clRead c) := by
  unfold clRead
  origin_fields_frame_mode r, c.st, root

/-- Both real constructors install the dynamic literal-table base. The
source refusal paths and real LEN_ continuation retain that installation. -/
theorem clTables_origin_fields {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (wf : s.WellFormed)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15)
    (actual : runX (clTables c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) :
    state.flags = s.flags ∧ state.lencode = .ref (.istate_codes zs) 0 := by
  obtain ⟨retL, nextL, bitsL, workL, codesL, lensRun, built⟩ :=
    clTables_both_run_semantics E.st E.hs wf nlen ndist
      (fun k bound => lengths k (by omega)) (fun k bound => lengths (s.nlen.toNat + k) (by omega))
  let lensState := clLensResult zs s nextL bitsL workL codesL
  have lensGet : (setI h zs lensState).istates zs = some lensState := setI_istates_same ..
  have lensStream : r.get (setI h zs lensState) = some z := by rw [ZStreamRef.get_setI]; exact E.hz
  by_cases lensOk : retL = 0
  · obtain ⟨offset, retD, nextD, bitsD, workD, codesD, _, _, distRun, _, _⟩ := built lensOk
    let distState := clDistResult lensState nextD bitsD workD codesD
    have distGet : (setI h zs distState).istates zs = some distState := setI_istates_same ..
    have distStream : r.get (setI h zs distState) = some z := by rw [ZStreamRef.get_setI]; exact E.hz
    by_cases distOk : retD = 0
    · rw [distOk] at distRun
      rw [clAfterDist_success E.st distGet] at distRun
      by_cases trees : c.flush = Z_TREES
      · rw [if_pos trees] at distRun
        have same : after = setI (setI h zs distState) zs { distState with mode := LEN_ } :=
          congrArg Prod.snd (Except.ok.inj (actual.symm.trans distRun))
        rw [same, setI_istates_same] at get
        cases Option.some.inj get
        exact ⟨rfl, rfl⟩
      · rw [if_neg trees] at distRun
        have source := distRun.symm.trans actual
        have fields := (originFieldFrameX_inflate_LEN_ r c E.strm _ _ _ _ _ source).state_fields
          (setI_istates_same (setI h zs distState) zs { distState with mode := LEN_ }) get
        exact ⟨fields.1, fields.2.1⟩
    · obtain ⟨i, _, errorRun⟩ := clAfterDist_error (l := { l with ret := retD })
        E.strm E.st distStream distGet distOk
      have same : after = tcBadHeap (setI h zs distState) r zs z distState i :=
        congrArg Prod.snd (Except.ok.inj (actual.symm.trans (distRun.trans errorRun)))
      rw [same] at get
      simp only [tcBadHeap, setI_istates_same] at get
      cases Option.some.inj get
      exact ⟨rfl, rfl⟩
  · obtain ⟨i, _, errorRun⟩ := clAfterLens_error (l := { l with ret := retL })
      E.strm E.st lensStream lensGet lensOk
    have same : after = tcBadHeap (setI h zs lensState) r zs z lensState i :=
      congrArg Prod.snd (Except.ok.inj (actual.symm.trans (lensRun.trans errorRun)))
    rw [same] at get
    simp only [tcBadHeap, setI_istates_same] at get
    cases Option.some.inj get
    exact ⟨rfl, rfl⟩

/-- Actual clTail either keeps BAD, reports a missing end code or calls
the real constructors. The flag and legal table origin follow each branch. -/
theorem clTail_origin_fields {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s state : InflateState} {l regs : IL} {outcome : Except Ex Unit}
    (E : Env c h r zs z s) (before : DefaultOriginState h r zs z s)
    (modes : s.mode = BAD ∨ s.mode = CODELENS)
    (done : s.mode = CODELENS → s.«have».toNat = s.nlen.toNat + s.ndist.toNat)
    (actual : runX (clTail c) l h = .ok ((outcome, regs), after))
    (get : after.istates zs = some state) : state.flags = s.flags ∧ CopyTableOrigin zs state := by
  have modeRead : rdS c.st (·.mode) h = .ok (s.mode, h) := by rw [E.st, rdI_eq, E.hs]
  by_cases bad : s.mode = BAD
  · have source : runX (clTail c) l h = .ok ((.ok (), l), h) := by
      simp [clTail, runX_bind, runX_lift_ok modeRead, bad, runX_pure]
    have same : after = h := congrArg Prod.snd (Except.ok.inj (actual.symm.trans source))
    rw [same, E.hs] at get
    cases Option.some.inj get
    exact ⟨rfl, before.tableOrigin⟩
  · have mode : s.mode = CODELENS := modes.resolve_left bad
    obtain ⟨_, _, nlen, ndist, _, initialized⟩ := before.lengths mode
    have lengths : ∀ k, k < s.nlen.toNat + s.ndist.toNat → (s.lens.getD k 0).toNat ≤ 15 := by
      rw [← done mode]
      exact initialized
    have inside : 0 + 256 < s.lens.size := by rw [before.good.inv.wf.1]; decide
    have read := Ptr.index_ok (off := 0) (i := 256) (WRef.get_istate_lens E.hs) inside
    let value : UInt16 := s.lens[0 + 256]
    have read' : Ptr.index (lensP c.st) 256 h = .ok (value, h) := by rw [E.st]; exact read
    have cut : runX (clTail c) l h =
        if value = 0 then runX (do badMode c "invalid code -- missing end-of-block"; pure ()) l h
        else runX (clTables c) l h := by
      by_cases zero : value = 0 <;>
        simp [clTail, runX_bind, runX_lift_ok modeRead, bad, runX_lift_ok read', zero]
    rw [cut] at actual
    by_cases zero : value = 0
    · rw [if_pos zero] at actual
      have frame : OriginFieldFrameX r c.st (do badMode c "invalid code -- missing end-of-block"; pure ()) := by
        origin_fields_frame_mode r, c.st, E.strm
      obtain ⟨flags, lengths, distances⟩ := (frame _ _ _ _ _ actual).state_fields E.hs get
      exact ⟨flags, by simpa only [CopyTableOrigin, lengths, distances] using before.tableOrigin⟩
    · rw [if_neg zero] at actual
      obtain ⟨flags, pointer⟩ := clTables_origin_fields E before.good.inv.wf nlen ndist lengths actual get
      exact ⟨flags, Or.inl pointer⟩

#print axioms clTables_origin_fields
#print axioms clTail_origin_fields
end Zlib.Inflate.Proofs
