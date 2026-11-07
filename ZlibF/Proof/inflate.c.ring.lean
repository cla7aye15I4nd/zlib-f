import ZlibF.Proof.«inflate.c.uw»

namespace Zlib.Inflate.Spec

/-- The slot of the ring buffer (of size `ws`, next write position `wn`, `wh` valid bytes) that holds the `j`-th oldest
valid byte: the valid bytes end just before `wn` and wrap around the end of the buffer. -/
def ringSlot (ws wn wh j : Nat) : Nat :=
  if wh ≤ wn then wn - wh + j else if j < wh - wn then ws - (wh - wn) + j else j - (wh - wn)

/-- The history the ring buffer `win` holds, oldest byte first: the last `wh` bytes written. -/
def ringList (win : Array UInt8) (ws wn wh : Nat) : List UInt8 :=
  (List.range wh).map (fun j => win[ringSlot ws wn wh j]!)

/-- The `c` bytes of the buffer `e` that end at offset `eo`. -/
def newBytes (e : Array UInt8) (eo c : Nat) : List UInt8 := (List.range c).map (fun i => e[eo - c + i]!)

end Zlib.Inflate.Spec

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec

theorem copyRange_succ (d s : Array UInt8) (doff soff n : Nat) :
    copyRange d s doff soff (n + 1) = (copyRange d s doff soff n).set! (doff + n) s[soff + n]! := by
  unfold copyRange
  rw [List.range_succ, List.foldl_append]
  rfl

theorem copyRange_getElem? (d s : Array UInt8) (doff soff n : Nat) (hd : doff + n ≤ d.size) (hs : soff + n ≤ s.size) (i : Nat) :
    (copyRange d s doff soff n)[i]? = if doff ≤ i ∧ i < doff + n then s[soff + (i - doff)]? else d[i]? := by
  induction n generalizing i with
  | zero =>
    simp only [copyRange, List.range_zero, List.foldl_nil]
    by_cases h : doff ≤ i ∧ i < doff + 0
    · omega
    · rw [ite_eq_right h]
  | succ n ih =>
    rw [copyRange_succ, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, ih (by omega) (by omega)]
    have hsz : (copyRange d s doff soff n).size = d.size := size_copyRange ..
    by_cases h1 : doff + n = i
    · subst h1
      have : ¬ (doff ≤ doff + n ∧ doff + n < doff + n) := by omega
      have h3 : doff + n < (copyRange d s doff soff n).size := by omega
      have h4 : soff + n < s.size := by omega
      simp [h3, getElem!_pos s (soff + n) h4, Array.getElem?_eq_getElem h4]
    · by_cases h2 : doff ≤ i ∧ i < doff + (n + 1)
      · have h5 : doff ≤ i ∧ i < doff + n := by omega
        simp [h1, h2, h5]
      · have h5 : ¬ (doff ≤ i ∧ i < doff + n) := by omega
        simp [h1, h2, h5]

/-- The four ways `uwPost` fills the ring buffer, in terms of `Nat` (`ws` = `wsize`, `wn` = `wnext`, `wh` = `whave`). -/
theorem uwPost_nat {st : InflateState} {a ebytes : Array UInt8} {eo : Nat} {copy : UInt32}
    (hpos : st.wsize.toNat ≠ 0)
    (hv : st.whave.toNat ≤ st.wsize.toNat) (hwn : st.wnext.toNat < st.wsize.toNat)
    (heq : st.whave.toNat < st.wsize.toNat → st.wnext.toNat = st.whave.toNat) (hw32 : st.wsize.toNat ≤ 2 ^ 16) :
    let ws := st.wsize.toNat; let wn := st.wnext.toNat; let wh := st.whave.toNat; let c := copy.toNat
    let P := uwPost st a ebytes eo copy
    (ws ≤ c ∧ P.1 = copyRange a ebytes 0 (eo - ws) ws ∧ P.2.wnext.toNat = 0 ∧ P.2.whave.toNat = ws) ∨
    (wn + c < ws ∧ P.1 = copyRange a ebytes wn (eo - c) c ∧ P.2.wnext.toNat = wn + c ∧
      P.2.whave.toNat = (if wh < ws then wh + c else wh)) ∨
    (wn + c = ws ∧ c < ws ∧ P.1 = copyRange a ebytes wn (eo - c) c ∧ P.2.wnext.toNat = 0 ∧
      P.2.whave.toNat = (if wh < ws then wh + c else wh)) ∨
    (ws < wn + c ∧ c < ws ∧
      P.1 = copyRange (copyRange a ebytes wn (eo - c) (ws - wn)) ebytes 0 (eo - (c - (ws - wn))) (c - (ws - wn)) ∧
      P.2.wnext.toNat = c - (ws - wn) ∧ P.2.whave.toNat = ws) := by
  intro ws wn wh c P
  have e1 := st.wsize.toNat_lt
  have e2 := st.wnext.toNat_lt
  have e3 := st.whave.toNat_lt
  have e4 := copy.toNat_lt
  simp only [ws, wn, wh, c, P]
  unfold uwPost
  repeat' split
  all_goals
    simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.toNat_add, UInt32.toNat_sub, gt_iff_lt, beq_iff_eq,
      bne_iff_ne, ne_eq, ← UInt32.toNat_inj, UInt32.toNat_zero, Nat.not_lt, Nat.not_le] at *
  all_goals first
    | (refine Or.inl ⟨?_, ?_, ?_, ?_⟩ <;> first | omega | rfl | trivial | (congr 1 <;> first | omega | (congr 1 <;> first | omega | (congr 1 <;> omega))))
    | (refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_⟩) <;> first | omega | rfl | trivial | (congr 1 <;> first | omega | (congr 1 <;> first | omega | (congr 1 <;> omega))))
    | (refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩)) <;> first | omega | rfl | trivial | (congr 1 <;> first | omega | (congr 1 <;> first | omega | (congr 1 <;> omega))))
    | (refine Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩)) <;> first | omega | rfl | trivial | (congr 1 <;> first | omega | (congr 1 <;> first | omega | (congr 1 <;> omega))))

theorem copyRange_bang (d s : Array UInt8) (doff soff n : Nat) (hd : doff + n ≤ d.size) (hs : soff + n ≤ s.size) (i : Nat)
    (hi : i < d.size) :
    (copyRange d s doff soff n)[i]! = if doff ≤ i ∧ i < doff + n then s[soff + (i - doff)]! else d[i]! := by
  have hsz : (copyRange d s doff soff n).size = d.size := size_copyRange ..
  have := copyRange_getElem? d s doff soff n hd hs i
  rw [getElem!_pos _ _ (by omega)]
  by_cases h : doff ≤ i ∧ i < doff + n
  · rw [ite_eq_left h] at this ⊢
    rw [getElem!_pos s _ (by omega)]
    have h2 : soff + (i - doff) < s.size := by omega
    rw [Array.getElem?_eq_getElem h2, Array.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this
  · rw [ite_eq_right h] at this ⊢
    rw [getElem!_pos d _ hi]
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this

set_option hygiene false in
/-- One element of the ring after the copy: evaluate the slots, split the cases, compare the indices. -/
macro "ring_tail" : tactic => `(tactic| (
  simp only [ringList, newBytes, List.getElem_drop, List.getElem_append, List.getElem_map, List.getElem_range,
    List.length_map, List.length_range] at h1 h2 ⊢
  subst hA'
  rw [hwn', hwh'] at *
  unfold ringSlot
  repeat' split
  all_goals (rw [copyRange_bang _ _ _ _ _ (by omega) (by omega) _ (by omega)]; repeat' split)
  all_goals (try (rw [copyRange_bang _ _ _ _ _ (by omega) (by omega) _ (by omega)]; repeat' split))
  all_goals first | rfl | (exfalso; omega) | (congr 1 <;> omega)))

/-- **The ring buffer after `updatewindow` holds the last `wsize` bytes of the history.** The history before the call is
the ring (`ringList`); the call appends the `copy` bytes that end at offset `eo` of the buffer; the new ring is the last
`min wsize (whave + copy)` bytes of that concatenation. -/
theorem ring_spec {st : InflateState} {a ebytes : Array UInt8} {eo : Nat} {copy : UInt32}
    (hpos : st.wsize.toNat ≠ 0)
    (hv : st.whave.toNat ≤ st.wsize.toNat) (hwn : st.wnext.toNat < st.wsize.toNat)
    (heq : st.whave.toNat < st.wsize.toNat → st.wnext.toNat = st.whave.toNat) (hw32 : st.wsize.toNat ≤ 2 ^ 16)
    (hasz : st.wsize.toNat ≤ a.size) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) (hA : a.size = st.wsize.toNat) :
    ringList (uwPost st a ebytes eo copy).1 st.wsize.toNat (uwPost st a ebytes eo copy).2.wnext.toNat
        (uwPost st a ebytes eo copy).2.whave.toNat =
      ((ringList a st.wsize.toNat st.wnext.toNat st.whave.toNat ++ newBytes ebytes eo copy.toNat).drop
        (st.whave.toNat + copy.toNat - (uwPost st a ebytes eo copy).2.whave.toNat)) := by
  have hn := uwPost_nat (a := a) (ebytes := ebytes) (eo := eo) (copy := copy) hpos hv hwn heq hw32
  simp only at hn
  have hsz := uwPost_size st a ebytes eo copy
  generalize uwPost st a ebytes eo copy = P at *
  obtain ⟨A', st'⟩ := P
  simp only at *
  rcases hn with ⟨c1, hA', hwn', hwh'⟩ | ⟨c1, hA', hwn', hwh'⟩ | ⟨c1, c2, hA', hwn', hwh'⟩ | ⟨c1, c2, hA', hwn', hwh'⟩
  · apply List.ext_getElem
    · simp [ringList, newBytes, hwh'] <;> omega
    · intro j h1 h2; ring_tail
  · by_cases hw : st.whave.toNat < st.wsize.toNat
    · have hq := heq hw
      simp only [hw, ite_true] at hwh'
      apply List.ext_getElem
      · simp [ringList, newBytes, hwh'] <;> omega
      · intro j h1 h2; ring_tail
    · simp only [hw, ite_false] at hwh'
      apply List.ext_getElem
      · simp [ringList, newBytes, hwh'] <;> omega
      · intro j h1 h2; ring_tail
  · by_cases hw : st.whave.toNat < st.wsize.toNat
    · have hq := heq hw
      simp only [hw, ite_true] at hwh'
      apply List.ext_getElem
      · simp [ringList, newBytes, hwh'] <;> omega
      · intro j h1 h2; ring_tail
    · simp only [hw, ite_false] at hwh'
      apply List.ext_getElem
      · simp [ringList, newBytes, hwh'] <;> omega
      · intro j h1 h2; ring_tail
  · by_cases hw : st.whave.toNat < st.wsize.toNat
    · have hq := heq hw
      apply List.ext_getElem
      · simp [ringList, newBytes, hwh'] <;> omega
      · intro j h1 h2
        have hin : (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize.toNat - st.wnext.toNat)).size = a.size := size_copyRange ..
        ring_tail
    · apply List.ext_getElem
      · simp [ringList, newBytes, hwh'] <;> omega
      · intro j h1 h2
        have hin : (copyRange a ebytes st.wnext.toNat (eo - copy.toNat) (st.wsize.toNat - st.wnext.toNat)).size = a.size := size_copyRange ..
        ring_tail

/-- **The indices after `updatewindow`.** `whave` becomes `min wsize (whave + copy)`; `wnext` advances by `copy`
modulo `wsize` (it is 0 when `copy ≥ wsize`). -/
theorem uwPost_counts {st : InflateState} {a ebytes : Array UInt8} {eo : Nat} {copy : UInt32}
    (hpos : st.wsize.toNat ≠ 0)
    (hv : st.whave.toNat ≤ st.wsize.toNat) (hwn : st.wnext.toNat < st.wsize.toNat)
    (heq : st.whave.toNat < st.wsize.toNat → st.wnext.toNat = st.whave.toNat) (hw32 : st.wsize.toNat ≤ 2 ^ 16) :
    (uwPost st a ebytes eo copy).2.whave.toNat = min st.wsize.toNat (st.whave.toNat + copy.toNat) ∧
    ((st.wsize.toNat ≤ copy.toNat ∧ (uwPost st a ebytes eo copy).2.wnext.toNat = 0) ∨
     (st.wnext.toNat + copy.toNat < st.wsize.toNat ∧ copy.toNat < st.wsize.toNat ∧
       (uwPost st a ebytes eo copy).2.wnext.toNat = st.wnext.toNat + copy.toNat) ∨
     (st.wsize.toNat ≤ st.wnext.toNat + copy.toNat ∧ copy.toNat < st.wsize.toNat ∧
       (uwPost st a ebytes eo copy).2.wnext.toNat = st.wnext.toNat + copy.toNat - st.wsize.toNat)) := by
  have hn := uwPost_nat (a := a) (ebytes := ebytes) (eo := eo) (copy := copy) hpos hv hwn heq hw32
  simp only at hn
  generalize uwPost st a ebytes eo copy = P at *
  obtain ⟨A', st'⟩ := P
  simp only at *
  rcases hn with ⟨c1, -, hwn', hwh'⟩ | ⟨c1, -, hwn', hwh'⟩ | ⟨c1, c2, -, hwn', hwh'⟩ | ⟨c1, c2, -, hwn', hwh'⟩
  all_goals
    by_cases hw : st.whave.toNat < st.wsize.toNat
    all_goals first
      | (have hq := heq hw; simp only [hw, ite_true] at hwh'; omega)
      | (simp only [hw, ite_false] at hwh'; omega)
      | omega

/-- **updatewindow, window content.** On a good stream whose window block exists, the window after the call, read as a
ring (`ringList`), is the last `wsize` bytes of the history before the call (the ring read from the state with `wsize`
set, empty when it was just set) followed by the `copy` bytes that end at offset `eo` of the caller's buffer;
`whave` is `min wsize (whave + copy)`. -/
theorem updatewindow_ring {H : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {st : InflateState} {w eb eo : Nat}
    {a ebytes : Array UInt8} {copy : UInt32}
    (hG : Good H r zs z st) (hw : st.window = .ref (.blk w) 0) (ha : H.bytes w = some a) (hro : H.ro w = false)
    (hasz : a.size = 2 ^ st.wbits.toNat)
    (heb : H.bytes eb = some ebytes) (hne : w ≠ eb) (hc : copy.toNat ≤ eo) (hoff : eo ≤ ebytes.size) :
    ∃ H' st' A', updatewindow (some r) (.ref (.blk eb) eo) copy H = .ok (0, H') ∧ Good H' r zs z st' ∧
      H'.bytes w = some A' ∧
      ringList A' (initWinS st).wsize.toNat st'.wnext.toNat st'.whave.toNat =
        ((ringList a (initWinS st).wsize.toNat (initWinS st).wnext.toNat (initWinS st).whave.toNat ++
            newBytes ebytes eo copy.toNat).drop ((initWinS st).whave.toNat + copy.toNat - st'.whave.toNat)) ∧
      st'.whave.toNat = min (initWinS st).wsize.toNat ((initWinS st).whave.toNat + copy.toNat) := by
  have hI := hG.inv
  obtain ⟨f1, f2, f3, hv1, hwn1, heq1, -⟩ := initWinS_facts hI.win.wbits hI.win.ws hI.win.hv hI.win.wn hI.win.eq
  have hwb := hI.win.wbits
  have hle : (initWinS st).wsize.toNat ≤ 2 ^ 16 := by
    rw [f1]; have := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : st.wbits.toNat ≤ 16); omega
  have hposn : (initWinS st).wsize.toNat ≠ 0 := by rw [f1]; exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)
  obtain ⟨H', st', hrun, hH', hst', hG', -, hb', -, -, -, -⟩ := uw_post hG hw ha hro hasz heb hne hc hoff
  refine ⟨H', st', _, hrun, hG', hb', ?_, ?_⟩
  · rw [hst']
    exact ring_spec hposn hv1 hwn1 heq1 hle (by rw [f1]; omega) hc hoff (by rw [f1]; omega)
  · rw [hst']
    exact (uwPost_counts hposn hv1 hwn1 heq1 hle).1

end Zlib.Inflate.Proofs
