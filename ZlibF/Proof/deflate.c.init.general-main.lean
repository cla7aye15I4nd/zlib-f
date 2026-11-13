import ZlibF.Proof.«deflate.c.init.general-success»
import ZlibF.Proof.«public-deflate-init»

/-! # deflate.c: `deflateInit2_` for every argument tuple and allocation outcome

Skeleton lemma `init2_main`: for every signed level, method, window, memory level and strategy,
`deflateInit2_` refuses exactly the tuples `Api.deflInit?` refuses (with the prepared stream and no
allocation), reports a failed state allocation, cleans up exactly when any of the four buffer
allocations fails, and otherwise establishes `DeflateInitial` with the parameters of
`Api.deflInit?`.
-/

namespace Zlib.Deflate.Proofs.GeneralInit
open C Zlib.Deflate Zlib.Deflate.Spec ZlibF.Spec.Public
open DefaultInit
open ZlibF.Spec.Public.Proofs.DeflateInit (globals_trees same_objects_refl)
set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The ranges that `Api.deflInit?` guarantees. -/
theorem params_ranges {level method wb mem strategy : Int} {p : ZlibF.Spec.Api.DeflParams}
    (h : ZlibF.Spec.Api.deflInit? level method wb mem strategy = some p) :
    method = 8 ∧ p.level ≤ 9 ∧ 9 ≤ p.wbits ∧ p.wbits ≤ 15 ∧ 1 ≤ p.memLevel ∧ p.memLevel ≤ 9 ∧
      p.memLevel = mem.toNat ∧ 0 ≤ strategy ∧ strategy ≤ 4 ∧ p.strategy = strategy.toNat := by
  unfold ZlibF.Spec.Api.deflInit? at h
  have fin : ∀ (wr : ZlibF.Spec.Api.DWrap) (b : Int),
      (if mem < 1 ∨ mem > 9 ∨ method ≠ 8 ∨ b < 8 ∨ b > 15 ∨
          (if level = -1 then 6 else level) < 0 ∨ (if level = -1 then 6 else level) > 9 ∨
          strategy < 0 ∨ strategy > 4 ∨ (b = 8 ∧ wr ≠ .zlib) then none
        else some (⟨(if level = -1 then 6 else level).toNat, wr, (if b = 8 then 9 else b).toNat,
          mem.toNat, strategy.toNat⟩ : ZlibF.Spec.Api.DeflParams)) = some p →
      method = 8 ∧ p.level ≤ 9 ∧ 9 ≤ p.wbits ∧ p.wbits ≤ 15 ∧ 1 ≤ p.memLevel ∧ p.memLevel ≤ 9 ∧
        p.memLevel = mem.toNat ∧ 0 ≤ strategy ∧ strategy ≤ 4 ∧ p.strategy = strategy.toNat := by
    intro wr b e
    by_cases ok : mem < 1 ∨ mem > 9 ∨ method ≠ 8 ∨ b < 8 ∨ b > 15 ∨
          (if level = -1 then 6 else level) < 0 ∨ (if level = -1 then 6 else level) > 9 ∨
          strategy < 0 ∨ strategy > 4 ∨ (b = 8 ∧ wr ≠ .zlib)
    · rw [if_pos ok] at e; cases e
    · rw [if_neg ok, Option.some.injEq] at e
      simp only [not_or] at ok
      subst e
      refine ⟨by omega, ?_, ?_, ?_, by dsimp only; omega, by dsimp only; omega, rfl, by omega, by omega, rfl⟩
      · dsimp only; split <;> omega
      · dsimp only; split <;> omega
      · dsimp only; split <;> omega
  simp only [] at h
  by_cases hw : wb < 0
  · by_cases hl : wb < -15
    · rw [if_pos hw, if_pos hl] at h; cases h
    · rw [if_pos hw, if_neg hl] at h
      exact fin _ _ h
  · by_cases hg : wb > 15
    · rw [if_neg hw, if_pos hg] at h
      exact fin _ _ h
    · rw [if_neg hw, if_neg hg] at h
      exact fin _ _ h

/-- **`init2_main`**: every argument tuple and every allocation outcome. -/
theorem init2_main (level method wb mem strategy : Int32) :
    ∀ h r z version, Fresh h → Zlib.Deflate.Spec.Uniq h → LibraryGlobals h →
      r.get h = some z → DefaultOrNull z → VersionValue h version (some 49) →
      ∃ rc after, C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h =
          .ok (rc, after) ∧
        (match ZlibF.Spec.Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
        | none => rc = Z_STREAM_ERROR ∧ SameObjects (r.put h (preparedStream z)) after ∧
            after.nalloc = h.nalloc
        | some p =>
          if h.allocOk h.nalloc = false then
            rc = Z_MEM_ERROR ∧ after.nalloc = h.nalloc + 1 ∧
            SameObjects (r.put h (preparedStream z)) after
          else after.nalloc = h.nalloc + 5 ∧
            if (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) then
              rc = Z_OK ∧ DeflateInitial h after r p
            else rc = Z_MEM_ERROR ∧
              (∃ z', r.get after = some z' ∧ z'.state = none) ∧
              LiveChange h after (fun _ => False) (fun _ => False) ∧
              Frame h after (StreamRoot r)) := by
  intro h r z version hf hu hg hz ha hv
  let zp := preparedStream z
  let hp := r.put h zp
  have hshape := shape_put hz zp
  have hfP : Fresh hp := hshape.fresh (by simp [hp]) hf
  have huP : Uniq hp := hshape.uniq hu
  have hzP : r.get hp = some zp := ZStreamRef.get_put_same hz _
  have haP : DefAlloc zp := prepared_allocators ha
  have entry : C.run (deflateInit2_ (some r) level method wb mem strategy version 112) h =
      (match ZlibF.Spec.Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
      | none => pure Z_STREAM_ERROR
      | some p => alloc (some r) (Int32.ofNat p.level) (wrapCode p.wrap) p.wbits p.memLevel method strategy) hp := by
    rw [C.run, entry_run hz hv, tail_params]
    rfl
  cases params : ZlibF.Spec.Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt with
  | none =>
    rw [params] at entry
    exact ⟨Z_STREAM_ERROR, hp, entry, rfl, same_objects_refl hp, by simp [hp]⟩
  | some p =>
    rw [params] at entry
    dsimp only at entry
    obtain ⟨m8, l9, w9, w15, m1, m9, mEq, s0, s4, sEq⟩ := params_ranges params
    have meth : method = 8 := Int32.toInt_inj.mp (by rw [m8]; rfl)
    subst meth
    let lev : Int32 := Int32.ofNat p.level
    have levInt : lev.toInt = p.level := Int32.toInt_ofNat_of_lt (by omega)
    simp only []
    by_cases first : h.allocOk h.nalloc = false
    · refine ⟨Z_MEM_ERROR, { hp with nalloc := hp.nalloc + 1 }, ?_, ?_⟩
      · rw [entry]
        exact alloc_state_fail hzP haP.1 (by simpa [hp] using first) _ _ _ _ _ _
      · simp only [ite_eq_left first]
        refine ⟨trivial, by simp [hp], ?_⟩
        dsimp [SameObjects]
        exact ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          Nat.le_refl _, by simp [hp]⟩
    · have firstT : h.allocOk h.nalloc = true := by cases he : h.allocOk h.nalloc <;> simp_all
      simp only [ite_eq_right first]
      by_cases all : (List.range 5).all (fun j => h.allocOk (h.nalloc + j)) = true
      · have allok : ∀ j, j < 5 → h.allocOk (h.nalloc + j) = true := by
          simpa only [List.all_eq_true, List.mem_range] using all
        obtain ⟨after, hr, hi⟩ := success_initial (wrapCode p.wrap) p.wbits p.memLevel hf hu hg hz ha allok
          lev strategy (by omega) (by omega) s0 s4 p.wrap rfl w9 w15 m1 m9
        have same : settings p.wrap p.wbits p.memLevel lev strategy = p := by
          have e1 : lev.toInt.toNat = p.level := by omega
          have e2 : strategy.toInt.toNat = p.strategy := by omega
          simp only [settings, e1, e2]
        rw [same] at hi
        have countP : ∀ j, j < 5 → hp.allocOk (hp.nalloc + j) = true := by
          intro j hj
          simpa [hp] using allok j hj
        obtain ⟨a1, a2, a3, qa, hsucc, -, -, -, -⟩ := allocate_success (wrapCode p.wrap) p.wbits p.memLevel
          hfP huP hzP haP (by simpa [hp] using globals_trees hg) countP lev strategy (by omega) (by omega)
          s0 s4 (by cases p.wrap <;> decide) (by cases p.wrap <;> decide) w9 w15 m1 m9
        refine ⟨Z_OK, after, ?_, ?_, ?_⟩
        · rw [entry]; exact hr
        · have eq : after = successHeap (wrapCode p.wrap) p.wbits p.memLevel hp r zp lev strategy a1 a2 a3 qa := by
            have := hr.symm.trans hsucc
            simp only [Except.ok.injEq, Prod.mk.injEq] at this
            exact this.2
          rw [eq]
          simp only [successHeap, setD_nalloc, setW, readyHeap, successfulBuffers,
            publishedHeap, stateHeap, ZStreamRef.put_nalloc, Nat.add_assoc, hp]
        · simpa only [ite_eq_left all] using (show Z_OK = Z_OK ∧ DeflateInitial h after r p from ⟨rfl, hi⟩)
      · let ph := publishedHeap hp r zp (wrapCode p.wrap) p.wbits p.memLevel
        have failed : ((bufferPointers ph p.wbits p.memLevel).1 == .null ||
            (bufferPointers ph p.wbits p.memLevel).2.1 == .null ||
            (bufferPointers ph p.wbits p.memLevel).2.2.1 == .null ||
            (bufferPointers ph p.wbits p.memLevel).2.2.2 == .null) = true := by
          apply Classical.byContradiction
          intro hn
          have hb : ((bufferPointers ph p.wbits p.memLevel).1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.2.1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.2.2 == .null) = false := by
            cases he : ((bufferPointers ph p.wbits p.memLevel).1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.2.1 == .null ||
              (bufferPointers ph p.wbits p.memLevel).2.2.2 == .null) <;> simp_all
          obtain ⟨h0, h1, h2, h3⟩ := (buffers_failed_iff p.wbits p.memLevel ph).mp hb
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
        obtain ⟨m, hm⟩ := finish_failure (wrapCode p.wrap) p.wbits p.memLevel hzP haP lev strategy 8 failed
        let after := failureHeap (wrapCode p.wrap) p.wbits p.memLevel hp r zp m
        refine ⟨Z_MEM_ERROR, after, ?_, ?_⟩
        · rw [entry, alloc_to_finish hfP hzP haP.1 (by simpa [hp] using firstT)]
          exact hm
        · refine ⟨by simpa [after, hp] using failure_count (wrapCode p.wrap) p.wbits p.memLevel hp r zp m, ?_⟩
          simp only [ite_eq_right all]
          refine ⟨trivial, ⟨_, failure_stream_cleared (wrapCode p.wrap) p.wbits p.memLevel hzP m, rfl⟩, ?_, ?_⟩
          · intro x
            simpa only [not_false_eq_true, and_true, or_false] using
              ((failure_shape (wrapCode p.wrap) p.wbits p.memLevel hzP hfP m).live x).trans (hshape.live x)
          · exact frame_trans r (frame_put r zp hf) (failure_frame (wrapCode p.wrap) p.wbits p.memLevel r zp m hfP)

end Zlib.Deflate.Proofs.GeneralInit
