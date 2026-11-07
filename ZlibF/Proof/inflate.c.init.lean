import ZlibF.Proof.«inflate.c.reset»

/-!
# inflate.c: `inflateReset2`, `inflateInit2_`, `inflateInit_`, `inflateEnd`, `inflatePrime`
-/

namespace Zlib.Inflate.Spec
open C

/-- The window bits and wrapper a `windowBits` argument asks for, as `(wrap, wbits)`, and `none` when it is refused
(`docs/api/inflate-stream.md`): negative values (raw, `-15` to `-8`) have wrapper 0; 0 and 8 to 15 give
wrapper 5, 16 and 24 to 31 give 6, 32 and 40 to 47 give 7; everything else is refused. -/
def reset2Req (w : Int) : Option (Int × Int) :=
  match (if w < 0 then (if w < -15 then none else some ((0 : Int), -w))
         else some (w / 16 + 5, if w < 48 then w % 16 else w)) with
  | none => none
  | some (wrap, wb) => if wb ≠ 0 ∧ (wb < 8 ∨ 15 < wb) then none else some (wrap, wb)

/-- The window bits are refused: not 0 and not 8 to 15. -/
def badBits (wb : Int32) : Bool := wb != 0 && (wb < 8 || wb > 15)

/-- The same computation on `int`, with the operations of the C (the arithmetic of `chkI32` never overflows here). -/
def reset2Params (w : Int32) : Option (Int32 × Int32) :=
  let check := fun (wrap wb : Int32) => if badBits wb then none else some (wrap, wb)
  if w < 0 then (if w < -15 then none else check 0 (Int32.ofInt (-w.toInt)))
  else check (Int32.ofInt ((w >>> 4).toInt + 5)) (if w < 48 then w &&& 15 else w)

/-- The state record after `inflateReset2` made its changes and before `inflateReset` runs. -/
def reset2Pre (wrap wb : Int32) (st : InflateState) : InflateState :=
  { (if st.wbits != Zlib.Inflate.i2u wb then { st with window := .null } else st) with
    wrap := wrap, reqwrap := wrap, wbits := Zlib.Inflate.i2u wb, reqbits := Zlib.Inflate.i2u wb }

/-- The heap after the window was freed, if `inflateReset2` frees it. -/
def reset2Heap (h : Heap) (wb : Int32) (st : InflateState) : Heap :=
  if st.wbits != Zlib.Inflate.i2u wb then freeWin h st.window else h

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem int32_shr4 (w : Int32) : (w >>> 4).toInt = w.toInt / 16 := by
  have : (w >>> 4) = ⟨⟨BitVec.sshiftRight' w.toBitVec ((4 : Int32).toBitVec.smod 32)⟩⟩ := rfl
  rw [this]
  show (BitVec.sshiftRight' w.toBitVec ((4 : Int32).toBitVec.smod 32)).toInt = _
  rw [BitVec.toInt_sshiftRight', Int.shiftRight_eq_div_pow]
  have h4 : ((4 : Int32).toBitVec.smod 32).toNat = 4 := by decide
  rw [h4]
  rfl

theorem int32_neg (w : Int32) (h1 : -15 ≤ w.toInt) (h2 : w.toInt < 0) : (-w).toInt = - w.toInt := by
  rw [Int32.toInt_neg]
  have := w.toInt_lt
  have := w.le_toInt
  rw [Int.bmod_eq_of_le (by omega) (by omega)]

/-- `int` constants of the C, as integers. -/
theorem int32_ofInt_toInt (k : Int) (h1 : -2147483648 ≤ k) (h2 : k < 2147483648) : (Int32.ofInt k).toInt = k := by
  rw [Int32.toInt_ofInt]
  simp only [Int32.size]
  exact Int.bmod_eq_of_le (by omega) (by omega)


theorem chkI32_ok {v : Int} (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) : chkI32 v = pure (Int32.ofInt v) := by
  simp [chkI32, h1, h2]

theorem int32_lt_zero (w : Int32) : w < 0 ↔ w.toInt < 0 := by
  rw [Int32.lt_iff_toInt_lt]; rfl

theorem int32_lt_c (w : Int32) (k : Int) (hk : -2147483648 ≤ k) (hk2 : k < 2147483648) :
    w < Int32.ofInt k ↔ w.toInt < k := by
  rw [Int32.lt_iff_toInt_lt, int32_ofInt_toInt k hk hk2]

theorem reset2_head_ok {w : Int32} (hw : ¬ w < -15) (hn : w < 0) :
    chkI32 (-(w.toInt)) = pure (Int32.ofInt (-w.toInt)) := by
  have h1 := w.le_toInt
  have h2 := (int32_lt_zero w).1 hn
  have h3 : -15 ≤ w.toInt := by
    by_cases hc : w.toInt < -15
    · exfalso
      apply hw
      have : (-15 : Int32) = Int32.ofInt (-15) := rfl
      rw [this, int32_lt_c w (-15) (by omega) (by omega)]
      exact hc
    · omega
  exact chkI32_ok (by omega) (by omega)

theorem reset2_wrap_ok (w : Int32) : chkI32 ((w >>> 4).toInt + 5) = pure (Int32.ofInt ((w >>> 4).toInt + 5)) := by
  have := w.le_toInt
  have := w.toInt_lt
  rw [int32_shr4]
  exact chkI32_ok (by omega) (by omega)


theorem reset2_okB {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) (hf : z.zfree = .fn "zcfree") (hwo : WindowOk h st.window) {w : Int32}
    (h1 : w < 0) (h2 : ¬ w < -15) (hb : badBits (-w) = false) :
    inflateReset2 (some r) w h = .ok (Z_OK, setI (r.put (reset2Heap h (-w) st)
      (resetKeepStream z (resetPre (reset2Pre (0) (-w) st)))) zs (resetKeepState zs (resetPre (reset2Pre (0) (-w) st)))) := by
  have hz := hL.hz
  have hs := hL.hs
  have hb' : ¬ (¬ w = 0 ∧ (-w < 8 ∨ 15 < -w)) := by simpa [badBits] using hb
  unfold inflateReset2
  by_cases hne : st.wbits = i2u (-w)
  · isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_head_ok h2 h1, hb', hne]
    rw [inflateReset_run]
    rotate_left
    · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
    · exact hf
    · exact Or.inl rfl
    · have e : reset2Heap h (-w) st = h := by simp [reset2Heap, hne]
      rw [e]
      simp [resetHeap, resetPre, reset2Pre, hne, resetKeepState, resetKeepStream]
  · by_cases hw : st.window = .null
    · isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_head_ok h2 h1, hb', hne, hw]
      rw [inflateReset_run]
      rotate_left
      · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
      · exact hf
      · exact Or.inl rfl
      · have e : reset2Heap h (-w) st = h := by simp [reset2Heap, hne, hw, freeWin_null]
        rw [e]
        simp [resetHeap, resetPre, reset2Pre, hne, hw, resetKeepState, resetKeepStream]
    · obtain ⟨b, a, hb0, hba, hro⟩ : ∃ b a, st.window = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false := by
        rcases hwo with hn | hb
        · exact absurd hn hw
        · exact hb
      isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_head_ok h2 h1, hb', hne, hw, zfreeB_run hz hf (Or.inr ⟨b, a, hb0, hba, hro⟩)]
      rw [inflateReset_run]
      rotate_left
      · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
      · exact hf
      · exact Or.inl rfl
      · simp [resetHeap, resetPre, reset2Pre, reset2Heap, hne, hw, resetKeepState, resetKeepStream]

theorem reset2_okC1 {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) (hf : z.zfree = .fn "zcfree") (hwo : WindowOk h st.window) {w : Int32}
    (h1 : ¬ w < 0) (h2 : w < 48) (hb : badBits (w &&& 15) = false) :
    inflateReset2 (some r) w h = .ok (Z_OK, setI (r.put (reset2Heap h (w &&& 15) st)
      (resetKeepStream z (resetPre (reset2Pre (Int32.ofInt ((w >>> 4).toInt + 5)) (w &&& 15) st)))) zs (resetKeepState zs (resetPre (reset2Pre (Int32.ofInt ((w >>> 4).toInt + 5)) (w &&& 15) st)))) := by
  have hz := hL.hz
  have hs := hL.hs
  have hb' : ¬ (¬ w &&& 15 = 0 ∧ (w &&& 15 < 8 ∨ 15 < w &&& 15)) := by simpa [badBits] using hb
  unfold inflateReset2
  by_cases hne : st.wbits = i2u (w &&& 15)
  · isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_wrap_ok w, hb', hne]
    rw [inflateReset_run]
    rotate_left
    · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
    · exact hf
    · exact Or.inl rfl
    · have e : reset2Heap h (w &&& 15) st = h := by simp [reset2Heap, hne]
      rw [e]
      simp [resetHeap, resetPre, reset2Pre, hne, resetKeepState, resetKeepStream]
  · by_cases hw : st.window = .null
    · isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_wrap_ok w, hb', hne, hw]
      rw [inflateReset_run]
      rotate_left
      · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
      · exact hf
      · exact Or.inl rfl
      · have e : reset2Heap h (w &&& 15) st = h := by simp [reset2Heap, hne, hw, freeWin_null]
        rw [e]
        simp [resetHeap, resetPre, reset2Pre, hne, hw, resetKeepState, resetKeepStream]
    · obtain ⟨b, a, hb0, hba, hro⟩ : ∃ b a, st.window = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false := by
        rcases hwo with hn | hb
        · exact absurd hn hw
        · exact hb
      isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_wrap_ok w, hb', hne, hw, zfreeB_run hz hf (Or.inr ⟨b, a, hb0, hba, hro⟩)]
      rw [inflateReset_run]
      rotate_left
      · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
      · exact hf
      · exact Or.inl rfl
      · simp [resetHeap, resetPre, reset2Pre, reset2Heap, hne, hw, resetKeepState, resetKeepStream]

theorem reset2_okC2 {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) (hf : z.zfree = .fn "zcfree") (hwo : WindowOk h st.window) {w : Int32}
    (h1 : ¬ w < 0) (h2 : ¬ w < 48) (hb : badBits w = false) :
    inflateReset2 (some r) w h = .ok (Z_OK, setI (r.put (reset2Heap h (w) st)
      (resetKeepStream z (resetPre (reset2Pre (Int32.ofInt ((w >>> 4).toInt + 5)) (w) st)))) zs (resetKeepState zs (resetPre (reset2Pre (Int32.ofInt ((w >>> 4).toInt + 5)) (w) st)))) := by
  have hz := hL.hz
  have hs := hL.hs
  have hb' : ¬ (¬ w = 0 ∧ (w < 8 ∨ 15 < w)) := by simpa [badBits] using hb
  unfold inflateReset2
  by_cases hne : st.wbits = i2u (w)
  · isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_wrap_ok w, hb', hne]
    rw [inflateReset_run]
    rotate_left
    · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
    · exact hf
    · exact Or.inl rfl
    · have e : reset2Heap h (w) st = h := by simp [reset2Heap, hne]
      rw [e]
      simp [resetHeap, resetPre, reset2Pre, hne, resetKeepState, resetKeepStream]
  · by_cases hw : st.window = .null
    · isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_wrap_ok w, hb', hne, hw]
      rw [inflateReset_run]
      rotate_left
      · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
      · exact hf
      · exact Or.inl rfl
      · have e : reset2Heap h (w) st = h := by simp [reset2Heap, hne, hw, freeWin_null]
        rw [e]
        simp [resetHeap, resetPre, reset2Pre, hne, hw, resetKeepState, resetKeepStream]
    · obtain ⟨b, a, hb0, hba, hro⟩ : ∃ b a, st.window = .ref (.blk b) 0 ∧ h.bytes b = some a ∧ h.ro b = false := by
        rcases hwo with hn | hb
        · exact absurd hn hw
        · exact hb
      isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_wrap_ok w, hb', hne, hw, zfreeB_run hz hf (Or.inr ⟨b, a, hb0, hba, hro⟩)]
      rw [inflateReset_run]
      rotate_left
      · exact ⟨by simp [hz], by first | exact setI_istates_same _ _ _ | (rw [freeWin_istates]; exact setI_istates_same _ _ _), hL.zst, by simp [hL.back], by simpa using hL.mode, hL.zalloc, hL.zfree⟩
      · exact hf
      · exact Or.inl rfl
      · simp [resetHeap, resetPre, reset2Pre, reset2Heap, hne, hw, resetKeepState, resetKeepStream]


theorem reset2_errA {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) {w : Int32} (h1 : w < 0) (h2 : w < -15) :
    inflateReset2 (some r) w h = .ok (Z_STREAM_ERROR, h) := by
  have hz := hL.hz
  have hs := hL.hs
  unfold inflateReset2
  isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2]

theorem reset2_errB {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) {w : Int32} (h1 : w < 0) (h2 : ¬ w < -15) (hb : badBits (-w) = true) :
    inflateReset2 (some r) w h = .ok (Z_STREAM_ERROR, h) := by
  have hz := hL.hz
  have hs := hL.hs
  have hb' : (¬ w = 0 ∧ (-w < 8 ∨ 15 < -w)) := by simpa [badBits] using hb
  unfold inflateReset2
  isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_head_ok h2 h1, hb']

theorem reset2_errC1 {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) {w : Int32} (h1 : ¬ w < 0) (h2 : w < 48) (hb : badBits (w &&& 15) = true) :
    inflateReset2 (some r) w h = .ok (Z_STREAM_ERROR, h) := by
  have hz := hL.hz
  have hs := hL.hs
  have hb' : (¬ w &&& 15 = 0 ∧ (w &&& 15 < 8 ∨ 15 < w &&& 15)) := by simpa [badBits] using hb
  unfold inflateReset2
  isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_wrap_ok w, hb']

theorem reset2_errC2 {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) {w : Int32} (h1 : ¬ w < 0) (h2 : ¬ w < 48) (hb : badBits w = true) :
    inflateReset2 (some r) w h = .ok (Z_STREAM_ERROR, h) := by
  have hz := hL.hz
  have hs := hL.hs
  have hb' : (¬ w = 0 ∧ (w < 8 ∨ 15 < w)) := by simpa [badBits] using hb
  unfold inflateReset2
  isimp [stateCheck_live hL, hL.zst, hz, hs, h1, h2, reset2_wrap_ok w, hb']

/-- **inflateReset2, evaluation.** For an initialised stream, `inflateReset2` refuses exactly the `windowBits` for which
`reset2Params` is `none` (`Z_STREAM_ERROR`, nothing changed) and otherwise returns `Z_OK` with the heap `reset2Heap` and
the records `resetKeepStream`/`resetKeepState` of `resetPre (reset2Pre wrap wb st)`. -/
theorem inflateReset2_run {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hL : Live h r zs z st) (hf : z.zfree = .fn "zcfree") (hwo : WindowOk h st.window) (w : Int32) :
    match reset2Params w with
    | none => inflateReset2 (some r) w h = .ok (Z_STREAM_ERROR, h)
    | some (wrap, wb) => badBits wb = false ∧ inflateReset2 (some r) w h = .ok (Z_OK, setI (r.put (reset2Heap h wb st)
        (resetKeepStream z (resetPre (reset2Pre wrap wb st)))) zs (resetKeepState zs (resetPre (reset2Pre wrap wb st)))) := by
  cases hp : reset2Params w with
  | none =>
    simp only [hp]
    unfold reset2Params at hp
    by_cases h1 : w < 0
    · by_cases h2 : w < -15
      · exact reset2_errA hL h1 h2
      · have e : Int32.ofInt (-w.toInt) = -w := by simp
        simp only [h1, h2, ite_true, ite_false, e] at hp
        have hb : badBits (-w) = true := by
          by_cases hb : badBits (-w) = true
          · exact hb
          · simp [hb] at hp
        exact reset2_errB hL h1 h2 hb
    · by_cases h2 : w < 48
      · simp only [h1, h2, ite_true, ite_false] at hp
        have hb : badBits (w &&& 15) = true := by
          by_cases hb : badBits (w &&& 15) = true
          · exact hb
          · simp [hb] at hp
        exact reset2_errC1 hL h1 h2 hb
      · simp only [h1, h2, ite_true, ite_false] at hp
        have hb : badBits w = true := by
          by_cases hb : badBits w = true
          · exact hb
          · simp [hb] at hp
        exact reset2_errC2 hL h1 h2 hb
  | some p =>
    obtain ⟨wrap, wb⟩ := p
    simp only [hp]
    unfold reset2Params at hp
    by_cases h1 : w < 0
    · by_cases h2 : w < -15
      · simp [h1, h2] at hp
      · have e : Int32.ofInt (-w.toInt) = -w := by simp
        simp only [h1, h2, ite_true, ite_false, e] at hp
        have hb : badBits (-w) = false := by
          by_cases hb : badBits (-w) = true
          · simp [hb] at hp
          · simpa using hb
        simp only [hb, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨hb, reset2_okB hL hf hwo h1 h2 hb⟩
    · by_cases h2 : w < 48
      · simp only [h1, h2, ite_true, ite_false] at hp
        have hb : badBits (w &&& 15) = false := by
          by_cases hb : badBits (w &&& 15) = true
          · simp [hb] at hp
          · simpa using hb
        simp only [hb, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨hb, reset2_okC1 hL hf hwo h1 h2 hb⟩
      · simp only [h1, h2, ite_true, ite_false] at hp
        have hb : badBits w = false := by
          by_cases hb : badBits w = true
          · simp [hb] at hp
          · simpa using hb
        simp only [hb, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨hb, reset2_okC2 hL hf hwo h1 h2 hb⟩


theorem strm_pre (wrap wb : Int32) (st : InflateState) : (resetPre (reset2Pre wrap wb st)).strm = st.strm := by
  unfold resetPre reset2Pre
  repeat' split
  all_goals rfl

theorem bits15 {wb : Int32} (hb : badBits wb = false) : (i2u wb).toNat ≤ 15 := by
  have hb' : ¬ (¬ wb = 0 ∧ (wb < 8 ∨ 15 < wb)) := by simpa [badBits] using hb
  by_cases h0 : wb = 0
  · subst h0; decide
  · have h1 : ¬ wb < 8 := fun h => hb' ⟨h0, Or.inl h⟩
    have h2 : ¬ 15 < wb := fun h => hb' ⟨h0, Or.inr h⟩
    have h1' : ¬ wb < Int32.ofInt 8 := h1
    have h2' : ¬ Int32.ofInt 15 < wb := h2
    rw [int32_lt_c wb 8 (by omega) (by omega)] at h1'
    rw [Int32.lt_iff_toInt_lt, int32_ofInt_toInt 15 (by omega) (by omega)] at h2'
    have hlo := wb.le_toInt
    have hhi := wb.toInt_lt
    obtain ⟨k, hk⟩ : ∃ k, k = wb.toInt := ⟨_, rfl⟩
    have hw : wb = Int32.ofInt k := by rw [hk]; exact (Int32.ofInt_toInt wb).symm
    have hk1 : 8 ≤ k := by omega
    have hk2 : k ≤ 15 := by omega
    rw [hw]
    have hc : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem winInv_reset2 {h : Heap} {st : InflateState} (hW : WinInv h st) {wb : Int32} (hb : (i2u wb).toNat ≤ 15) (wrap : Int32) :
    WinInv (reset2Heap h wb st) (resetPre (reset2Pre wrap wb st)) := by
  by_cases hne : st.wbits = i2u wb
  · have e : reset2Heap h wb st = h := by simp [reset2Heap, hne]
    rw [e]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [resetPre, reset2Pre, hne] using hb
    · have := hW.block
      rw [hne] at this
      simpa [resetPre, reset2Pre, hne] using this
    · intro _; simp [resetPre, reset2Pre, hne]
    · simp [resetPre, reset2Pre, hne]
    · simp [resetPre, reset2Pre, hne]
    · simp [resetPre, reset2Pre, hne]
    · intro hh; simp [resetPre, reset2Pre, hne] at hh
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [resetPre, reset2Pre, hne] using hb
    · left; simp [resetPre, reset2Pre, hne]
    · intro _; simp [resetPre, reset2Pre, hne]
    · simp [resetPre, reset2Pre, hne]
    · simp [resetPre, reset2Pre, hne]
    · simp [resetPre, reset2Pre, hne]
    · intro hh; simp [resetPre, reset2Pre, hne] at hh

theorem reset2Heap_owns {h : Heap} {st : InflateState} (hU : Uniq h) (hW : WinInv h st) {wb : Int32} {S : Nat → Prop}
    (hO : h.Owns S) : (reset2Heap h wb st).Owns (fun b => S b ∧ ¬ (st.wbits ≠ i2u wb ∧ WinBlk st b)) := by
  have e : reset2Heap h wb st = resetHeap h { st with reqbits := i2u wb } := by simp [reset2Heap, resetHeap]
  rw [e]
  exact resetHeap_owns (st := { st with reqbits := i2u wb }) hU ⟨hW.wbits, hW.block, hW.nullws, hW.ws, hW.hv, hW.wn, hW.eq⟩ hO

theorem uniq_reset2Heap {h : Heap} (hU : Uniq h) (wb : Int32) (st : InflateState) : Uniq (reset2Heap h wb st) := by
  unfold reset2Heap; split
  · exact uniq_freeWin hU _
  · exact hU

theorem fresh_reset2Heap {h : Heap} (hF : Fresh h) (wb : Int32) (st : InflateState) : Fresh (reset2Heap h wb st) := by
  unfold reset2Heap; split
  · exact fresh_freeWin hF _
  · exact hF


/-- **inflateReset2, safety.** On an initialised stream with the default `zfree`, for every `windowBits`: the call never
faults. A refused value (`reset2Params w = none`) gives `Z_STREAM_ERROR` and changes nothing. An accepted value gives
`Z_OK`; the window is freed if its size differs from the new one (nothing else is allocated or freed); the stream is
initialised again with the invariants intact; the live blocks are the old ones minus the window block that was freed. -/
theorem inflateReset2_safe {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState}
    (hG : Good h r zs z st) (hf : z.zfree = .fn "zcfree") (w : Int32) :
    ∃ v h', C.run (inflateReset2 (some r) w) h = .ok (v, h') ∧
      (match reset2Params w with
       | none => v = Z_STREAM_ERROR ∧ h' = h
       | some (wrap, wb) => v = Z_OK ∧
          h' = setI (r.put (reset2Heap h wb st) (resetKeepStream z (resetPre (reset2Pre wrap wb st)))) zs
            (resetKeepState zs (resetPre (reset2Pre wrap wb st))) ∧
          Good h' r zs (resetKeepStream z (resetPre (reset2Pre wrap wb st))) (resetKeepState zs (resetPre (reset2Pre wrap wb st))) ∧
          (∀ S, h.Owns S → h'.Owns (fun b => S b ∧ ¬ (st.wbits ≠ i2u wb ∧ WinBlk st b)))) := by
  have hL := hG.live
  have hrun := inflateReset2_run hL hf (windowBlock hG.inv.win) w
  cases hp : reset2Params w with
  | none =>
    rw [hp] at hrun
    exact ⟨_, _, hrun, rfl, rfl⟩
  | some p =>
    obtain ⟨wrap, wb⟩ := p
    rw [hp] at hrun
    obtain ⟨hb, hrun⟩ := hrun
    have hU := uniq_reset2Heap hG.uniq wb st
    have hF := fresh_reset2Heap hG.fresh wb st
    have hz0 : r.get (reset2Heap h wb st) = some z := by unfold reset2Heap; split <;> simp [hL.hz]
    have hs0 : (reset2Heap h wb st).istates zs = some st := by unfold reset2Heap; split <;> simp [hL.hs]
    have hw := winInv_reset2 hG.inv.win (bits15 hb) wrap
    have hI : StInv (reset2Heap h wb st) zs (resetKeepState zs (resetPre (reset2Pre wrap wb st))) := by
      refine ⟨?_, ?_, ?_, by simp [resetKeepState], ?_⟩
      · exact wf_resetKeepState (wf_resetPre (by unfold reset2Pre; split <;> exact hG.inv.wf))
      · exact ⟨hw.wbits, hw.block, hw.nullws, hw.ws, hw.hv, hw.wn, hw.eq⟩
      · simpa [resetKeepState, reqbits_resetPre, reset2Pre] using bits15 hb
      · refine (StInv.resetKeep (st := resetPre (reset2Pre wrap wb st)) ⟨?_, hw, ?_, ?_, ?_⟩).ptr
        · exact wf_resetPre (by unfold reset2Pre; split <;> exact hG.inv.wf)
        · simpa [reqbits_resetPre, reset2Pre] using bits15 hb
        · exact bits_resetPre (by unfold reset2Pre; split <;> exact hG.inv.bits)
        · exact ptr_resetPre (by unfold reset2Pre; split <;> exact hG.inv.ptr)
    refine ⟨_, _, hrun, rfl, rfl, ?_, ?_⟩
    · refine good_set hz0 hs0 hU hF (by simp [resetKeepStream, hL.zst]) (by simpa [resetKeepStream] using hL.zalloc)
        (by simpa [resetKeepStream] using hL.zfree)
        (by simpa [resetKeepState, strm_pre] using hL.back)
        (by simpa [resetKeepState] using mode_head) hI
    · intro S hO
      have hO' := reset2Heap_owns (wb := wb) hG.uniq hG.inv.win hO
      exact ((shape_put hz0 _).trans (shape_setI (by simpa using hs0) _)).owns hO'

end Zlib.Inflate.Proofs
