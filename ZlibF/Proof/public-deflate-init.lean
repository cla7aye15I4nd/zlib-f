import ZlibF.Proof.«deflate.c.init.failure»

/-! # The default deflate initialization entry

The default entry expands the translated fixed-parameter call directly.
The universal deflateInit2_ theorem is not a proof dependency.
-/

namespace ZlibF.Spec.Public.Proofs.DeflateInit
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Proofs.DefaultInit
open Zlib.Trees.Proofs.Out (TreesStatic)
set_option autoImplicit false

def settings (level : Int32) : Api.DeflParams := ⟨level.toInt.toNat, .zlib, 15, 8, 0⟩

theorem parameters_equiv (level : Int32) :
    Api.deflInit? level.toInt 8 15 8 0 =
      if levelValue level < 0 || levelValue level > 9 then none else some (settings (levelValue level)) := by
  by_cases hd : level = Z_DEFAULT_COMPRESSION
  · subst level
    decide +kernel
  · have hi : level.toInt ≠ -1 := by
      intro hi
      apply hd
      apply Int32.toInt_inj.mp
      simpa only [show Z_DEFAULT_COMPRESSION.toInt = -1 from rfl] using hi
    simp [Api.deflInit?, settings, levelValue, hd, hi,
      Int32.lt_iff_toInt_lt]

def resultState (h : Heap) (r : ZStreamRef) (level : Int32) (a1 a2 a3 : Array CtData) : DeflateState :=
  finalState h.nextBlk r level (h.nextBlk + 1) (h.nextBlk + 2) (h.nextBlk + 3) (h.nextBlk + 4) a1 a2 a3

/-- All five successful requests establish DGood by actual execution,
including hash clearing. No callee or initialized-state invariant is assumed. -/
theorem allocate_success {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hu : Uniq h) (hz : r.get h = some z) (hd : DefAlloc z)
    (hs : TreesStatic h.static) (ha : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9) :
    ∃ (a1 a2 a3 : Array CtData) (qa : Array UInt16),
      allocate (some r) level h = .ok (Z_OK, successHeap h r z level a1 a2 a3 qa) ∧
      DGood (successHeap h r z level a1 a2 a3 qa) r h.nextBlk (resultStream h r z level)
        (resultState h r level a1 a2 a3) ∧
      (∀ x, (successHeap h r z level a1 a2 a3 qa).live x ↔
        h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk + 5) := by
  let ph := publishedHeap h r z
  have ha0 : h.allocOk h.nalloc = true := by simpa using ha 0 (by decide)
  have ha4 : ∀ j, j < 4 → ph.allocOk (ph.nalloc + j) = true := by
    intro j hj
    simpa [ph, publishedHeap, stateHeap, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ha (j + 1) (by omega)
  have hfp := (shape_put hz (stateStream z h.nextBlk)).fresh (by simp) hf
  have hup := (shape_put hz (stateStream z h.nextBlk)).uniq hu
  have hfP : Fresh ph := fresh_stateHeap hfp _
  have huP : Uniq ph := uniq_stateHeap hup hfp _
  have hzP : r.get ph = some (stateStream z h.nextBlk) := by
    simp [ph, publishedHeap, ZStreamRef.get_put_same hz]
  have hdP : DefAlloc (stateStream z h.nextBlk) := hd
  have hsP : ph.dstates h.nextBlk = some (baseState r) := by simp [ph, publishedHeap, stateHeap]
  have hst : TreesStatic ph.static := by simpa [ph, publishedHeap, stateHeap] using hs
  obtain ⟨hlR, htR, hbR, huR, hfR⟩ := ready_storage level hfP huP hzP hsP
    (by simp [ph, publishedHeap, stateHeap]) hdP rfl hst ha4
  obtain ⟨a1, a2, a3, qa, s1, s2, s3, hqa, hreset, hG, hLive⟩ :=
    reset_construct level hlR htR hbR huR hfR hl0 hl9
  refine ⟨a1, a2, a3, qa, ?_, ?_, ?_⟩
  · rw [allocate_to_finish hf hz hd.1 ha0, finish_to_reset _ _ _ _ ha4, hreset]
    rfl
  · simpa only [successHeap, resultStream, resultState, finalState,
      ph, publishedHeap, stateHeap, ZStreamRef.put_nextBlk, Nat.add_assoc] using hG
  · intro x
    have hc := ready_live hz level ha4 x
    have hr := hLive x
    simpa only [successHeap, resultStream] using hr.trans hc

theorem globals_trees {h : Heap} (hg : LibraryGlobals h) : TreesStatic h.static := by
  rw [hg]
  rfl

theorem result_owned (h : Heap) (r : ZStreamRef) (level : Int32)
    (a1 a2 a3 : Array CtData) (x : Nat) :
    DeflateOwned h.nextBlk (resultState h r level a1 a2 a3) x ↔
      h.nextBlk ≤ x ∧ x < h.nextBlk + 5 := by
  simp only [DeflateOwned, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
    Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState,
    baseState]
  simp only [Ptr.ref.injEq, BRef.blk.injEq, WRef.blk.injEq, and_true]
  omega

/-- Actual successful default allocation establishes the exact public
initial relation, with old-object frame and the five-object ledger. -/
theorem success_initial {h : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hu : Uniq h) (hg : LibraryGlobals h) (hz : r.get h = some z)
    (ha : DefaultOrNull z) (allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9) :
    ∃ after, allocate (some r) level (r.put h (preparedStream z)) = .ok (Z_OK, after) ∧
      DeflateInitial h after r (settings level) := by
  let zp := preparedStream z
  let hp := r.put h zp
  have shape := shape_put hz zp
  have hfP : Fresh hp := shape.fresh (by simp [hp]) hf
  have huP : Uniq hp := shape.uniq hu
  have hzP : r.get hp = some zp := ZStreamRef.get_put_same hz _
  have haP : DefAlloc zp := prepared_allocators ha
  have globalsP : TreesStatic hp.static := by simpa [hp] using globals_trees hg
  have allP : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
    intro j hj
    simpa [hp] using allok j hj
  obtain ⟨a1, a2, a3, qa, hrun, hG, hLive⟩ := allocate_success hfP huP hzP haP globalsP allP level hl0 hl9
  let after := successHeap hp r zp level a1 a2 a3 qa
  let zf := resultStream hp r zp level
  let sf := resultState hp r level a1 a2 a3
  have nb : hp.nextBlk = h.nextBlk := by simp [hp]
  have hGood : DGood after r h.nextBlk zf sf := by simpa only [nb] using hG
  have owned : ∀ x, DeflateOwned h.nextBlk sf x ↔ h.nextBlk ≤ x ∧ x < h.nextBlk + 5 := by
    intro x
    simpa only [nb] using result_owned hp r level a1 a2 a3 x
  have hFrame : Frame h after (StreamRoot r) := frame_trans r (frame_put r zp hf)
    (success_frame r zp level a1 a2 a3 qa hfP)
  refine ⟨after, hrun, zf, sf, hGood, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hFrame, ?_, owned⟩
  · simpa [zf, resultStream, rkZ, stateStream] using haP.1
  · simpa [zf, resultStream, rkZ, stateStream] using haP.2
  · simp only [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, settings]
    omega
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, settings]
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings]
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings]
  · simp [sf, resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid, absWrap,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec, readyState, allocatedState, baseState, settings]
  · intro x
    simp only [LiveChange, not_false_eq_true, and_true] at *
    change after.live x ↔ h.live x ∨ DeflateOwned h.nextBlk sf x
    rw [owned]
    have live := hLive x
    rw [shape.live] at live
    simpa only [nb] using live

theorem allocate_success_count {h after : Heap} {r : ZStreamRef} {z : ZStream}
    (hf : Fresh h) (hu : Uniq h) (hz : r.get h = some z) (hd : DefAlloc z)
    (hs : TreesStatic h.static) (ha : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true)
    (level : Int32) (hl0 : 0 ≤ level.toInt) (hl9 : level.toInt ≤ 9)
    (hrun : allocate (some r) level h = .ok (Z_OK, after)) :
    after.nalloc = h.nalloc + 5 := by
  obtain ⟨a1, a2, a3, qa, hr, _, _⟩ := allocate_success hf hu hz hd hs ha level hl0 hl9
  rw [hr] at hrun
  cases hrun
  simp only [successHeap, setD_nalloc, setW, readyHeap, successfulBuffers,
    publishedHeap, stateHeap, ZStreamRef.put_nalloc, Nat.add_assoc]

theorem same_objects_refl (h : Heap) : SameObjects h h := by
  exact ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Nat.le_refl _, Nat.le_refl _⟩

/-- The exact public default-entry goal, including arbitrary levels, every
allocation outcome, cleanup, ownership and the initialized invariant.
The translated fixed-parameter call is expanded; the general Init2 goal
is not assumed. -/
theorem deflateInit_proof : Goal.deflateInit_ := by
  intro level
  refine ⟨version_refusal level, null_stream level, ?_⟩
  intro h r z version hf hu hg hz ha hv
  let zp := preparedStream z
  let hp := r.put h zp
  let lev := levelValue level
  have hshape := shape_put hz zp
  have hfP : Fresh hp := hshape.fresh (by simp [hp]) hf
  have huP : Uniq hp := hshape.uniq hu
  have hzP : r.get hp = some zp := ZStreamRef.get_put_same hz _
  have haP : DefAlloc zp := prepared_allocators ha
  have entry := entry_run hz hv level
  simp only [show (8 : Int32).toInt = (8 : Int) from rfl,
    show (15 : Int32).toInt = (15 : Int) from rfl,
    show (0 : Int32).toInt = (0 : Int) from rfl]
  rw [parameters_equiv]
  by_cases bad : (levelValue level < 0 || levelValue level > 9) = true
  · refine ⟨Z_STREAM_ERROR, hp, ?_, ?_⟩
    · simpa only [C.run, ite_eq_left bad] using entry
    · simp only [ite_eq_left bad]
      exact ⟨True.intro, same_objects_refl hp, by simp [hp]⟩
  · have bounds : 0 ≤ lev.toInt ∧ lev.toInt ≤ 9 := by
      have bn := bad
      simp only [Bool.or_eq_true, decide_eq_true_eq, Int32.lt_iff_toInt_lt] at bn
      change ¬ (lev.toInt < 0 ∨ 9 < lev.toInt) at bn
      omega
    have entry' : deflateInit_ (some r) level version 112 h = allocate (some r) lev hp := by
      simpa only [ite_eq_right bad] using entry
    simp only [ite_eq_right bad]
    by_cases first : h.allocOk h.nalloc = false
    · refine ⟨Z_MEM_ERROR, { hp with nalloc := hp.nalloc + 1 }, ?_, ?_⟩
      · change deflateInit_ (some r) level version 112 h = _
        rw [entry']
        exact allocate_state_fail hzP haP.1 (by simpa [hp] using first) lev
      · simp only [ite_eq_left first]
        refine ⟨True.intro, by simp [hp], ?_⟩
        dsimp [SameObjects]
        exact ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          Nat.le_refl _, by simp [hp]⟩
    · have firstT : h.allocOk h.nalloc = true := by cases he : h.allocOk h.nalloc <;> simp_all
      simp only [ite_eq_right first]
      by_cases all : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true
      · have allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true := by
          simpa only [List.all_eq_true, List.mem_range] using all
        obtain ⟨after, hr, hi⟩ := success_initial hf hu hg hz ha allok lev bounds.1 bounds.2
        refine ⟨Z_OK, after, ?_, ?_⟩
        · change deflateInit_ (some r) level version 112 h = _
          rw [entry']
          exact hr
        · refine ⟨?_, ?_⟩
          · have count := allocate_success_count hfP huP hzP haP
              (by simpa [hp] using globals_trees hg)
              (by simpa [hp] using allok) lev bounds.1 bounds.2 hr
            simpa [hp] using count
          · simpa only [ite_eq_left all] using (show Z_OK = Z_OK ∧ DeflateInitial h after r (settings lev) from ⟨rfl, hi⟩)
      · let ph := publishedHeap hp r zp
        have failed : ((bufferPointers ph).1 == .null || (bufferPointers ph).2.1 == .null ||
            (bufferPointers ph).2.2.1 == .null || (bufferPointers ph).2.2.2 == .null) = true := by
          apply Classical.byContradiction
          intro hn
          have hb : ((bufferPointers ph).1 == .null || (bufferPointers ph).2.1 == .null ||
              (bufferPointers ph).2.2.1 == .null || (bufferPointers ph).2.2.2 == .null) = false := by
            cases he : ((bufferPointers ph).1 == .null || (bufferPointers ph).2.1 == .null ||
              (bufferPointers ph).2.2.1 == .null || (bufferPointers ph).2.2.2 == .null) <;> simp_all
          obtain ⟨h0, h1, h2, h3⟩ := (buffers_failed_iff ph).mp hb
          apply all
          rw [List.all_eq_true]
          intro j hj
          have hj5 := List.mem_range.mp hj
          have hn : ph.nalloc = h.nalloc + 1 := by simp [ph, publishedHeap, stateHeap, hp]
          have ao : ph.allocOk = h.allocOk := by simp [ph, publishedHeap, stateHeap, hp]
          rw [ao, hn] at h0 h1 h2 h3
          have cases5 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
          rcases cases5 with h | h | h | h | h <;> subst j <;>
            simpa only [Nat.add_assoc, Nat.add_zero] using (by assumption)
        obtain ⟨m, hm⟩ := finish_failure hzP haP lev failed
        let after := failureHeap hp r zp m
        refine ⟨Z_MEM_ERROR, after, ?_, ?_⟩
        · change deflateInit_ (some r) level version 112 h = _
          rw [entry', allocate_to_finish hfP hzP haP.1 (by simpa [hp] using firstT)]
          exact hm
        · refine ⟨by simpa [after, hp] using failure_count hp r zp m, ?_⟩
          simp only [ite_eq_right all]
          refine ⟨True.intro, ⟨_, failure_stream_cleared hzP m, rfl⟩, ?_, ?_⟩
          · intro x
            simpa only [not_false_eq_true, and_true, or_false] using
              ((failure_shape hzP hfP m).live x).trans (hshape.live x)
          · exact frame_trans r (frame_put r zp hf) (failure_frame r zp m hfP)

/-- A concrete caller heap. The version and stream are distinct live
objects, and every default allocation request succeeds. -/
def witnessHeap : Heap :=
  { Heap.empty with
    streams := upd Heap.empty.streams 0 (some default)
    bytes := upd Heap.empty.bytes 1 (some #[49, 0])
    nextBlk := 2
    static := Zlib.Crc32.initStatics
      (Zlib.Inftrees.initStatics (Zlib.Trees.trees_statics Heap.empty.static)) }

theorem witness_fresh : Fresh witnessHeap := by
  intro b hb hl
  have h0 : b ≠ 0 := by change 2 ≤ b at hb; omega
  have h1 : b ≠ 1 := by change 2 ≤ b at hb; omega
  simp [Heap.live, witnessHeap, Heap.empty, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1] at hl

theorem witness_uniq : Uniq witnessHeap := by
  intro b
  by_cases h0 : b = 0
  · subst b; simp [witnessHeap, Heap.empty, cnt]
  by_cases h1 : b = 1
  · subst b; simp [witnessHeap, Heap.empty, cnt]
  simp [witnessHeap, Heap.empty, cnt, upd_ne _ _ _ _ h0, upd_ne _ _ _ _ h1]

theorem witness_version : VersionValue witnessHeap (.ref (.blk 1) 0) (some 49) := by
  right
  refine ⟨49, rfl, Or.inr ⟨.blk 1, 0, #[49, 0], rfl, ?_, ?_, ?_⟩⟩ <;>
    simp [Space.get, witnessHeap, Heap.empty]

/-- Non-vacuity: a concrete default caller actually returns an initialized
stream whose representation invariant was established by the entry. -/
theorem default_init_witness :
    ∃ after, C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
      witnessHeap = .ok (Z_OK, after) ∧
      DeflateInitial witnessHeap after (.tab 0) (settings 6) := by
  obtain ⟨rc, after, hr, hp⟩ := (deflateInit_proof Z_DEFAULT_COMPRESSION).2.2
    witnessHeap (.tab 0) default (.ref (.blk 1) 0) witness_fresh witness_uniq rfl
    (by simp [ZStreamRef.get, witnessHeap]) ⟨Or.inl rfl, Or.inl rfl⟩ witness_version
  change after.nalloc = 5 ∧ rc = Z_OK ∧ DeflateInitial witnessHeap after (.tab 0) (settings 6) at hp
  rw [hp.2.1] at hr
  exact ⟨after, hr, hp.2.2⟩

end ZlibF.Spec.Public.Proofs.DeflateInit
