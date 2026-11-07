import ZlibF.Spec.Public.Lifecycle
import ZlibF.Proof.«inflate.c.public-setdict-success»

open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Adler32.Proofs ZlibF.Spec.Public

namespace ZlibF.Spec.Public.Proofs

theorem setdict_allocation_failure_public
    {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    {source : BPtr} {len : UInt32} {xs : List UInt8}
    (hg : Good h r i z s) (hza : z.zalloc = .fn "zcalloc")
    (hn : source ≠ .null) (hb : Bytes h source len.toNat xs)
    (hwrap : s.wrap = 0 ∨ s.mode = DICT)
    (hcheck : s.mode = DICT → (ZlibF.Spec.adler32 xs).toUInt64 = s.check)
    (hw : s.window = .null) (hok : h.allocOk h.nalloc = false) :
    ∃ after, C.run (inflateSetDictionary (some r) source len) h = .ok (Z_MEM_ERROR, after) ∧
      AllocationFailed h after ∧
      Good after r i z { s with mode := MEM } ∧
      Frame h after (fun b => StreamRoot r b ∨ InflateOwned i s b) ∧
      (∃ s', h.istates i = some s ∧ after.istates i = some s' ∧
        LiveChange h after (fun b => InflateOwned i s' b ∧ ¬ h.live b) (fun _ => False)) := by
  let after := setI (setI { h with nalloc := h.nalloc + 1 } i s) i { s with mode := MEM }
  have hfalse : ¬ h.allocOk h.nalloc = true := by rw [hok]; decide
  have hr : C.run (inflateSetDictionary (some r) source len) h = .ok (Z_MEM_ERROR, after) := by
    rcases hb with ⟨he, _, _⟩ | ⟨ref, off, a, rfl, ha, hf, hs⟩
    · exact (hn he).elim
    · have hseg := seg_eq_slice a off len.toNat hf
      rw [← hseg] at hs
      subst xs
      exact inflateSetDictionary_alloc_fail_any hg hza ha hf hwrap hcheck hw hfalse
  have hshape1 : Shape h (setI { h with nalloc := h.nalloc + 1 } i s) :=
    shape_setI hg.live.hs s
  have hshape2 : Shape (setI { h with nalloc := h.nalloc + 1 } i s) after :=
    shape_setI (s0 := s) (by simp) _
  have hshape : Shape h after := hshape1.trans hshape2
  refine ⟨after, hr, ?_, inflateSetDictionary_alloc_fail_good hg, ?_, ?_⟩
  · exact ⟨h.nalloc, Nat.le_refl _, by simp [after, setI], hok⟩
  · simp only [Frame, after, setI, true_and]
    refine ⟨Nat.le_refl _, Nat.le_succ _, ?_⟩
    intro b _ hb
    have hbi : b ≠ i := fun e => hb (Or.inr (Or.inl e))
    simp [upd_ne, hbi]
  · refine ⟨{ s with mode := MEM }, hg.live.hs, by simp [after], ?_⟩
    intro b
    have hl := hshape.live b
    have howned : InflateOwned i { s with mode := MEM } b → h.live b := by
      intro ho
      rcases ho with he | he
      · subst b
        simp [Heap.live, hg.live.hs]
      · simp [hw] at he
    simp only [LiveChange, not_false_eq_true, and_true]
    constructor
    · intro ha; exact Or.inl (hl.mp ha)
    · intro ha
      rcases ha with ha | ⟨ho, hn⟩
      · exact hl.mpr ha
      · exact (hn (howned ho)).elim

private theorem frame_unchanged (h : Heap) (changed : Nat → Prop) : Frame h h changed := by
  refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
  intro b _ _
  simp

private theorem owned_already_live {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (hg : Good h r i z s) : ∀ b, InflateOwned i s b → h.live b := by
  intro b ho
  rcases ho with hi | hw
  · subst b
    simp [Heap.live, hg.live.hs]
  · rcases hg.inv.win.block with hn | ⟨w, a, hwin, ha, _, _⟩
    · rw [hn] at hw
      cases hw
    · rw [hwin] at hw
      cases hw
      simp [Heap.live, ha]

private theorem live_unchanged {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (hg : Good h r i z s) :
    LiveChange h h (fun b => InflateOwned i s b ∧ ¬ h.live b) (fun _ => False) := by
  intro b
  simp only [LiveChange, not_false_eq_true, and_true]
  constructor
  · exact Or.inl
  · intro hh
    rcases hh with hl | ⟨ho, hn⟩
    · exact hl
    · exact (hn (owned_already_live hg b ho)).elim

/-- `int inflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`
satisfies all public rejection, content, frame and allocation clauses. -/
theorem inflateSetDictionary_public : Goal.inflateSetDictionary := by
  intro h r i z s source n xs old hg hza hold hb hsep _
  by_cases hrefused : source = .null ∨ (s.wrap ≠ 0 ∧ s.mode ≠ DICT)
  · refine ⟨Z_STREAM_ERROR, h, inflateSetDictionary_refused_any hg.live source n hrefused, ?_, ?_,
      frame_unchanged h _, ⟨s, hg.live.hs, hg.live.hs, live_unchanged hg⟩⟩
    · intro _; exact ⟨rfl, rfl⟩
    · intro hn hwrap
      rcases hrefused with he | ⟨hwrap', hm⟩
      · exact (hn he).elim
      · rcases hwrap with he | he
        · exact (hwrap' he).elim
        · exact (hm he).elim
  · have hn : source ≠ .null := fun he => hrefused (Or.inl he)
    have hwrap : s.wrap = 0 ∨ s.mode = DICT := by
      by_cases hw : s.wrap = 0
      · exact Or.inl hw
      · by_cases hm : s.mode = DICT
        · exact Or.inr hm
        · exact (hrefused (Or.inr ⟨hw, hm⟩)).elim
    have hbytes := hb hn
    by_cases hbad : s.mode = DICT ∧ s.check ≠ (ZlibF.Spec.adler32 xs).toUInt64
    · have hrun : C.run (inflateSetDictionary (some r) source n) h = .ok (Z_DATA_ERROR, h) := by
        rcases hbytes with ⟨he, _, _⟩ | ⟨ref, off, a, rfl, ha, hf, hs⟩
        · exact (hn he).elim
        · rw [← seg_eq_slice a off n.toNat hf] at hs
          subst xs
          exact inflateSetDictionary_dataerr_any hg.live ha hf hbad.1 (Ne.symm hbad.2)
      refine ⟨Z_DATA_ERROR, h, hrun, ?_, ?_, frame_unchanged h _,
        ⟨s, hg.live.hs, hg.live.hs, live_unchanged hg⟩⟩
      · intro he; exact (hrefused he).elim
      · intro _ _; simp [hbad]
    · have hcheck : s.mode = DICT → (ZlibF.Spec.adler32 xs).toUInt64 = s.check := by
        intro hm
        by_cases he : (ZlibF.Spec.adler32 xs).toUInt64 = s.check
        · exact he
        · exact (hbad ⟨hm, Ne.symm he⟩).elim
      rcases hbytes with ⟨he, _, _⟩ | ⟨ref, off, a, hsource, ha, hf, hxs⟩
      · exact (hn he).elim
      · subst source
        have hcheck' : s.mode = DICT → (ZlibF.Spec.adler32 (seg a off n.toNat)).toUInt64 = s.check := by
          rw [seg_eq_slice a off n.toNat hf]
          simpa [hxs] using hcheck
        obtain ⟨rc, after, state, hr, hgood, hcase⟩ :=
          inflateSetDictionary_success_public hg hza ha hf hxs hold hsep hwrap hcheck'
        rcases hcase with ⟨hrc, hhavedict, hmode, hdict, hframe, hlive⟩ |
          ⟨hrc, hmode, hwin, halloc⟩
        · refine ⟨rc, after, hr, ?_, ?_, hframe, ⟨state, hg.live.hs, hgood.live.hs, hlive⟩⟩
          · intro he; exact (hrefused he).elim
          · intro _ _
            simp only [ite_eq_right hbad]
            exact Or.inr ⟨hrc, state, hgood, hhavedict, hmode, hdict⟩
        · obtain ⟨failed, hf, hallocation, hgood', hframe, hlive⟩ :=
            setdict_allocation_failure_public hg hza (by simp) (Or.inr ⟨ref, off, a, rfl, ha, hf, hxs⟩)
              hwrap hcheck hwin halloc
          have he : after = failed := by
            rw [hrc] at hr
            rw [hr] at hf
            cases hf
            rfl
          subst failed
          refine ⟨rc, after, hr, ?_, ?_, hframe, hlive⟩
          · intro he; exact (hrefused he).elim
          · intro _ _
            simp only [ite_eq_right hbad]
            exact Or.inl ⟨hrc, hallocation, { s with mode := MEM }, hgood', rfl⟩

#print axioms setdict_allocation_failure_public
#print axioms inflateSetDictionary_public

end ZlibF.Spec.Public.Proofs
