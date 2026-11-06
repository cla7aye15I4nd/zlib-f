import ZlibF.Proof.«gzlib.c.base»

/-!
# gzlib.c: `gz_error` without a message, `gz_reset`, `gzclearerr`

`gz_error(state, err, NULL)` frees the old message, records `err` and clears the message. `gz_reset` is made of plain
field writes and one such call. Both keep `GzGood` (the message block is the only block that goes away) and give the
ownership statement: the live blocks afterwards are those before, without the old message block.
-/

namespace Zlib.Gzlib.Spec
open C Zlib.GzFs Zlib.Gzguts

/-- The record `gz_error(state, err, NULL)` leaves: no message, the new error code. -/
def errNull (s : GzState) (e : Int32) : GzState := { s with msg := .null, err := e }

/-- The record `gz_reset` leaves (`gz_reset(state)` after `gz_open` and in `gzrewind`): the buffered bytes and the
position are cleared, the reader goes back to `LOOK`, the writer clears `reset`, the error is `Z_OK` without a message,
and the embedded stream has no input. -/
def resetRec (s : GzState) : GzState :=
  { (if s.mode == GZ_READ then { s with eof := 0, how := LOOK, junk := -1 } else { s with reset := 0 }) with
    x := { s.x with «have» := 0, pos := 0 }, past := 0, again := 0, skip := 0, msg := .null, err := Z_OK,
    strm := { s.strm with avail_in := 0 } }

end Zlib.Gzlib.Spec

namespace Zlib.Gzlib.Proofs
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzlib.Spec

theorem blk_ne_msg {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) {mb : Nat} (hm : s.msg = .ref (.blk mb) 0) :
    (∀ b, s.path = .ref (.blk b) 0 → b ≠ mb) ∧ (∀ b, s.in = .ref (.blk b) 0 → b ≠ mb) ∧
    (∀ b, s.out = .ref (.blk b) 0 → b ≠ mb) := by
  have hn := hG.nodup
  rcases hG.path with ⟨pb, hp, -⟩
  rcases hG.inb with hi | ⟨ib, ia, hi, -⟩ <;> rcases hG.outb with ho | ⟨ob, oa, ho, -⟩ <;>
    simp [hp, hm, hi, ho, ptrBlk, List.nodup_cons] at hn ⊢ <;> omega

theorem Uniq.freeBytes {h : Heap} (hU : Uniq h) (mb : Nat) : Uniq { h with bytes := upd h.bytes mb none } := by
  intro b
  by_cases hb : b = mb
  · subst hb
    have := hU b
    simp only [upd_same, cnt_none]
    omega
  · have := hU b
    simpa only [upd_ne _ _ _ _ hb] using this

theorem live_freeBytes {h : Heap} (hU : Uniq h) {mb : Nat} {a : Array UInt8} (ha : h.bytes mb = some a) (b : Nat) :
    ({ h with bytes := upd h.bytes mb none } : Heap).live b ↔ h.live b ∧ b ≠ mb := by
  by_cases hb : b = mb
  · subst hb
    have := hU b
    simp only [Heap.live, ha, cnt_some] at this ⊢
    simp only [upd_same]
    have h1 : h.words b = none := by
      cases hh : h.words b <;> simp [hh] at this ⊢ <;> omega
    have h2 : h.streams b = none := by
      cases hh : h.streams b <;> simp [hh] at this ⊢ <;> omega
    have h3 : h.gzheaders b = none := by
      cases hh : h.gzheaders b <;> simp [hh] at this ⊢ <;> omega
    have h4 : h.dstates b = none := by
      cases hh : h.dstates b <;> simp [hh] at this ⊢ <;> omega
    have h5 : h.istates b = none := by
      cases hh : h.istates b <;> simp [hh] at this ⊢ <;> omega
    have h6 : h.gzstates b = none := by
      cases hh : h.gzstates b <;> simp [hh] at this ⊢ <;> omega
    simp [h1, h2, h3, h4, h5, h6]
  · simp [Heap.live, upd_ne _ _ _ _ hb, hb]

theorem Fresh.freeBytes {h : Heap} (hF : Fresh h) (mb : Nat) : Fresh { h with bytes := upd h.bytes mb none } := by
  intro b hb hl
  apply hF b hb
  by_cases hbm : b = mb
  · subst hbm
    simp only [Heap.live, upd_same] at hl ⊢
    rcases hl with hl | hl
    · exact absurd rfl hl
    · exact Or.inr hl
  · simpa [Heap.live, upd_ne _ _ _ _ hbm] using hl

theorem nodup_drop_msg {a c d : BPtr} (b : BPtr) (hn : ([a, b, c, d].filterMap ptrBlk).Nodup) :
    ([a, (.null : BPtr), c, d].filterMap ptrBlk).Nodup := by
  have e : ([a, (.null : BPtr), c, d].filterMap ptrBlk) = ([a, c, d].filterMap ptrBlk) := by
    simp [List.filterMap_cons, ptrBlk]
  rw [e]
  exact List.Nodup.sublist (List.Sublist.filterMap ptrBlk (by simp)) hn

/-- `gz_error(state, e, NULL)` keeps the invariant (the old message block is freed). -/
theorem GzGood.afterErr {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (e : Int32) :
    GzGood (setS (freeStr h s.msg) gs (errNull s e)) gs (errNull s e) := by
  rcases hG.msg with hn | ⟨mb, hm, a, ha, hro, k, hz⟩
  · rw [hn]; simp only [freeStr_null]
    exact GzGood.withRec hG (Or.inl rfl) rfl (by simp [errNull, hn]) rfl rfl (by simp [errNull])
  · obtain ⟨hpn, hin, hon⟩ := blk_ne_msg hG hm
    rw [hm]; simp only [freeStr_blk]
    have hU := Uniq.freeBytes hG.uniq mb
    have hF := Fresh.freeBytes hG.fresh mb
    have hS := shape_setS (h := ({ h with bytes := upd h.bytes mb none } : Heap)) (gs := gs) (s0 := s) hG.hs (errNull s e)
    refine ⟨by simp, hG.mode, ?_, Or.inl rfl, ?_, ?_, nodup_drop_msg s.msg hG.nodup, fun _ => rfl,
      Shape.uniq hS hU, Shape.fresh hS rfl hF⟩
    · obtain ⟨pb, hp, a', ha', hro', k', hz'⟩ := hG.path
      have hne := hpn pb hp
      exact ⟨pb, hp, a', by simp [setS, upd_ne _ _ _ _ hne, ha'], by simpa using hro', k', hz'⟩
    · rcases hG.inb with hi | ⟨ib, ia, hi, hia, hiro⟩
      · exact Or.inl hi
      · have hne := hin ib hi
        exact Or.inr ⟨ib, ia, hi, by simp [setS, upd_ne _ _ _ _ hne, hia], by simpa using hiro⟩
    · rcases hG.outb with hi | ⟨ib, ia, hi, hia, hiro⟩
      · exact Or.inl hi
      · have hne := hon ib hi
        exact Or.inr ⟨ib, ia, hi, by simp [setS, upd_ne _ _ _ _ hne, hia], by simpa using hiro⟩


@[simp] theorem freeStr_setS (h : Heap) (gs : Nat) (s : GzState) (p : BPtr) :
    freeStr (setS h gs s) p = setS (freeStr h p) gs s := by
  cases p with
  | null => rfl
  | ref r o => cases r <;> rfl

theorem freeB_blk_run {h : Heap} {mb : Nat} {a : Array UInt8} (ha : h.bytes mb = some a) (hro : h.ro mb = false) :
    freeB (.ref (.blk mb) 0) h = .ok ((), { h with bytes := upd h.bytes mb none }) := by
  simp [freeB, ha, hro]

theorem freeB_blk_setS {h : Heap} {mb : Nat} {a : Array UInt8} (ha : h.bytes mb = some a) (hro : h.ro mb = false)
    (gs : Nat) (s' : GzState) :
    freeB (.ref (.blk mb) 0) (setS h gs s') = .ok ((), setS { h with bytes := upd h.bytes mb none } gs s') := by
  simp [freeB, setS, ha, hro]

theorem record_msg_null {s : GzState} (hn : s.msg = .null) : { s with msg := .null } = s := by
  cases s; simp_all

/-- `gz_error(state, err, NULL)`: the old message is freed (the only change of the heap besides the record), the error
code is `err` and there is no message. -/
theorem gz_error_null_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) (e : Int32) :
    gz_error (some (.tab gs)) e .null h = .ok ((), setS (freeStr h s.msg) gs (errNull s e)) := by
  have hs := hG.hs
  unfold gz_error
  rcases hG.msg with hn | ⟨mb, hm, a, ha, hro, k, hz⟩
  · gsimp [hs, hn, errNull]
  · have hne : s.err ≠ Z_MEM_ERROR := fun h' => by have := hG.memerr h'; rw [hm] at this; cases this
    gsimp [hs, hm, hne, freeB_blk_run ha hro, freeB_blk_setS ha hro, errNull]


/-- `gz_reset(state)`. -/
theorem gz_reset_run {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) :
    gz_reset (some (.tab gs)) h = .ok ((), setS (freeStr h s.msg) gs (resetRec s)) := by
  have hs := hG.hs
  unfold gz_reset
  rcases hG.msg with hn | ⟨mb, hm, a, ha, hro, k, hz⟩
  · by_cases hmo : s.mode = GZ_READ
    · gsimp [hs, hn, hmo, gz_error, resetRec]
    · gsimp [hs, hn, hmo, gz_error, resetRec]
  · have hne : s.err ≠ Z_MEM_ERROR := fun h' => by have := hG.memerr h'; rw [hm] at this; cases this
    by_cases hmo : s.mode = GZ_READ
    · gsimp [hs, hm, hne, hmo, freeB_blk_setS ha hro, gz_error, resetRec]
    · gsimp [hs, hm, hne, hmo, freeB_blk_setS ha hro, gz_error, resetRec]

theorem GzGood.afterReset {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) :
    GzGood (setS (freeStr h s.msg) gs (resetRec s)) gs (resetRec s) := by
  have h1 := GzGood.withRec (GzGood.afterErr hG Z_OK) (s' := resetRec s) (Or.inl (by unfold resetRec errNull; split <;> rfl))
    (by unfold resetRec errNull; split <;> rfl) (by unfold resetRec errNull; split <;> rfl)
    (by unfold resetRec errNull; split <;> rfl) (by unfold resetRec errNull; split <;> rfl)
    (by intro _; unfold resetRec; split <;> rfl)
  simpa using h1

/-- **gz_reset, safety and effect.** On a handle that satisfies the invariant the call does not fault; the old message
block is the only block freed; the record is `resetRec s`. -/
theorem gz_reset_safe {h : Heap} {gs : Nat} {s : GzState} (hG : GzGood h gs s) :
    ∃ h', C.run (gz_reset (some (.tab gs))) h = .ok ((), h') ∧ h' = setS (freeStr h s.msg) gs (resetRec s) ∧
      GzGood h' gs (resetRec s) ∧
      (∀ S, h.Owns S → h'.Owns (fun b => S b ∧ s.msg ≠ .ref (.blk b) 0)) := by
  refine ⟨_, gz_reset_run hG, rfl, GzGood.afterReset hG, ?_⟩
  intro S hO
  rcases hG.msg with hn | ⟨mb, hm, a, ha, hro, k, hz⟩
  · simp only [hn, freeStr_null]
    have := Shape.owns (shape_setS hG.hs (resetRec s)) hO
    simpa [hn] using this
  · rw [hm]; simp only [freeStr_blk]
    have hO1 : ({ h with bytes := upd h.bytes mb none } : Heap).Owns (fun b => S b ∧ b ≠ mb) := by
      intro b; rw [live_freeBytes hG.uniq ha b, hO b]
    have := Shape.owns (shape_setS (h := ({ h with bytes := upd h.bytes mb none } : Heap)) (gs := gs) (s0 := s) hG.hs (resetRec s)) hO1
    intro b
    rw [this b]
    simp [hm, eq_comm]

end Zlib.Gzlib.Proofs
