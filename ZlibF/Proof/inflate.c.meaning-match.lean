import ZlibF.Proof.«inflate.c.meaning-copy»
import ZlibF.Proof.«inflate.c.meaning-accept»
import ZlibF.Proof.«inflate.c.match-step»
import ZlibF.Math.LZ77History

/-!
# inflate.c: `MATCH` keeps the format meaning

`case MATCH` copies the next bytes of a pending match. `copy = out - left` is
the number of bytes this call has written (the check base is the call's output
start in the body). A distance within them copies from the output, possibly
overlapping; a longer one copies from the window ring, and a distance beyond
the window is rejected as too far back. The copy is cut at the window
segment's end, the match length and the output room. With the match done the
mode becomes `LEN` and the parse reaches the end of the token
(`DeflateParsed.token`); otherwise the parse stays inside the match
(`DeflateParsed.partialCopy` with more bytes written).

The too-far exit dooms the input: with a full window (width 15, which the
header and the configuration fix) the window keeps every byte within 32768,
so zlib's check means the distance exceeds the dictionary and output before
the token, against the token's own bound.
-/

namespace Zlib.Inflate.Proofs.MeaningMatch
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningWrite Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningCopy
set_option autoImplicit false

/-! ## Lists: the bytes of a match -/

/-- The first `k` bytes of a match are the match of length `k`. -/
theorem copyBack_take (dict out0 : List UInt8) (dist len k : Nat) (le : k ≤ len) :
    (copyBack dict dist len out0).take (out0.length + k) = copyBack dict dist k out0 := by
  have compose := ZlibF.Math.LZ77History.copy_back_compose dict out0 dist k (len - k)
  rw [Nat.add_sub_cancel' le] at compose
  rw [compose]
  obtain ⟨pre, _⟩ := ZlibF.Math.LZ77History.copy_back_extends_history dict
    (copyBack dict dist k out0) dist (len - k)
  have len0 := (ZlibF.Math.LZ77History.copy_back_extends_history dict out0 dist k).2
  rw [← len0]
  exact (List.prefix_iff_eq_take.mp pre).symm

/-- A match that does not reach its own bytes appends a slice of the history. -/
theorem copyBack_far (dict : List UInt8) (dist : Nat) :
    ∀ (n : Nat) (h : List UInt8), n ≤ dist → dist ≤ (dict ++ h).length →
      copyBack dict dist n h = h ++ ((dict ++ h).drop ((dict ++ h).length - dist)).take n
  | 0, h, _, _ => by simp [copyBack]
  | n + 1, h, le, bound => by
    obtain ⟨x, hx⟩ : ∃ x, (dict ++ h).getD ((dict ++ h).length - dist) 0 = x := ⟨_, rfl⟩
    have ih := copyBack_far dict dist n (h ++ [x])
      (by omega) (by simp only [List.length_append, List.length_singleton] at bound ⊢; omega)
    simp only [copyBack]
    rw [hx, ih]
    have lt : (dict ++ h).length - dist < (dict ++ h).length := by omega
    have xe : (dict ++ h)[(dict ++ h).length - dist] = x := by
      rw [← hx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lt]
      rfl
    rw [List.drop_eq_getElem_cons lt, xe]
    rw [← List.append_assoc dict h [x], List.length_append, List.length_singleton,
      List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp only [List.length_drop]; omega)]
    rw [show (dict ++ h).length + 1 - dist = (dict ++ h).length - dist + 1 by omega]
    simp

/-! ## Arrays: the bytes the copy loop writes -/

open ZlibF.Math.InflateMatchCopy in
/-- A copy from fixed bytes writes exactly those bytes. -/
theorem copy_saved_get (saved : Array UInt8) :
    ∀ (n so oo : Nat) (A : Array UInt8) (i : Nat), oo + n ≤ A.size → i < n →
      (copy false saved n so oo A).getD (oo + i) 0 = saved.getD (so + i) 0
  | 0, _, _, _, _, _, lt => absurd lt (by omega)
  | n + 1, so, oo, A, i, fit, lt => by
    rw [copy_succ]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases i with
    | zero =>
      rw [copy_get_outside false saved n (so + 1) (oo + 1) _ (oo + 0) (by omega)]
      simp only [Nat.add_zero, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?]
      rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)]
      simp
    | succ i =>
      have := copy_saved_get saved n (so + 1) (oo + 1) (A.set! oo (saved.getD so 0)) i
        (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; omega) (by omega)
      rw [show oo + (i + 1) = oo + 1 + i by omega, this, show so + 1 + i = so + (i + 1) by omega]


open ZlibF.Math.InflateMatchCopy in
/-- A copy from fixed bytes writes exactly those bytes, as a list. -/
theorem copy_saved_slice (saved A : Array UInt8) (n so oo : Nat) (fitA : oo + n ≤ A.size)
    (fitS : so + n ≤ saved.size) :
    ((copy false saved n so oo A).toList.drop oo).take n = (saved.toList.drop so).take n := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, Array.length_toList, copy_size]
    omega
  · intro j h1 h2
    have jn : j < n := by simp only [List.length_take] at h1; omega
    have eq := copy_saved_get saved n so oo A j fitA jn
    have b1 : oo + j < (copy false saved n so oo A).size := by rw [copy_size]; omega
    have b2 : so + j < saved.size := by omega
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem b1,
      Array.getElem?_eq_getElem b2, Option.getD_some] at eq
    simpa only [List.getElem_take, List.getElem_drop, Array.getElem_toList] using eq

/-- A written list slice read back through `getD`. -/
theorem slice_getD {A : Array UInt8} {o0 : Nat} {cur : List UInt8}
    (view : (A.toList.drop o0).take cur.length = cur) {j : Nat} (lt : j < cur.length) :
    cur.getD j 0 = A.getD (o0 + j) 0 := by
  obtain ⟨k, hk⟩ : ∃ k, cur.length = k := ⟨_, rfl⟩
  rw [hk] at view lt
  subst view
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, Array.getD_eq_getD_getElem?, lt]

/-- Storing one byte right after a written slice extends the slice. -/
theorem slice_set_end {A : Array UInt8} {o0 : Nat} {cur : List UInt8} (v : UInt8)
    (view : (A.toList.drop o0).take cur.length = cur) (fit : o0 + cur.length < A.size) :
    ((A.set! (o0 + cur.length) v).toList.drop o0).take (cur.length + 1) = cur ++ [v] := by
  obtain ⟨k, hk⟩ : ∃ k, cur.length = k := ⟨_, rfl⟩
  rw [hk] at view fit ⊢
  subst view
  rw [set_toList]
  have m : min k (A.size - o0) = k := by omega
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_set, List.getElem?_append,
    List.length_take, List.length_drop, Array.length_toList, m]
  by_cases jk : j < k
  · have a : ¬ k = j := by omega
    simp [jk, a, show j < k + 1 by omega]
  · by_cases je : j = k
    · subst je
      simp [fit]
    · have c : ¬ j < k + 1 := by omega
      have d : j - k ≠ 0 := by omega
      simp [c, jk, d]

open ZlibF.Math.InflateMatchCopy in
/-- A copy from the output `dist` bytes back, overlapping or not, extends the
written slice by the match. -/
theorem copy_output (saved : Array UInt8) :
    ∀ (n : Nat) (A : Array UInt8) (cur : List UInt8) (o0 dist : Nat),
      (A.toList.drop o0).take cur.length = cur → o0 + cur.length + n ≤ A.size → 0 < dist →
      dist ≤ cur.length →
      ((copy true saved n (o0 + cur.length - dist) (o0 + cur.length) A).toList.drop o0).take
        (cur.length + n) = copyBack [] dist n cur
  | 0, A, cur, o0, dist, view, _, _, _ => by
    simpa [copy_zero, copyBack] using view
  | n + 1, A, cur, o0, dist, view, fit, pos, le => by
    rw [copy_succ]
    simp only [↓reduceIte]
    have value : ([] ++ cur).getD (([] ++ cur).length - dist) 0 = A.getD (o0 + cur.length - dist) 0 := by
      rw [List.nil_append, slice_getD view (by omega)]
      congr 1
      omega
    have view' := slice_set_end (A.getD (o0 + cur.length - dist) 0) view (by omega)
    have ih := copy_output saved n (A.set! (o0 + cur.length) (A.getD (o0 + cur.length - dist) 0))
      (cur ++ [A.getD (o0 + cur.length - dist) 0]) o0 dist
      (by simpa only [List.length_append, List.length_singleton] using view')
      (by simp only [List.length_append, List.length_singleton, Array.set!_eq_setIfInBounds,
        Array.size_setIfInBounds]; omega) pos
      (by simp only [List.length_append, List.length_singleton]; omega)
    simp only [List.length_append, List.length_singleton] at ih
    rw [show o0 + (cur.length + 1) - dist = o0 + cur.length - dist + 1 by omega,
      show o0 + (cur.length + 1) = o0 + cur.length + 1 by omega,
      show cur.length + 1 + n = cur.length + (n + 1) by omega] at ih
    rw [ih, copyBack, value]

/-- The slice of `k + n` bytes is the slice of `k` followed by the next `n`. -/
theorem slice_split (A : Array UInt8) (o0 k n : Nat) :
    (A.toList.drop o0).take (k + n) = (A.toList.drop o0).take k ++ (A.toList.drop (o0 + k)).take n := by
  rw [List.take_add, List.drop_drop]

/-! ## The window ring -/

/-- A distance within the bytes before the write cursor. -/
theorem ring_near (a : List UInt8) (off wn wh d n : Nat) (h1 : wn ≤ wh) (fit : off + wh ≤ a.length)
    (hd : d ≤ wn) (hn : n ≤ d) :
    ((((a.drop (off + wn)).take (wh - wn) ++ (a.drop off).take wn).drop
        (((a.drop (off + wn)).take (wh - wn) ++ (a.drop off).take wn).length - d)).take n) =
      (a.drop (off + (wn - d))).take n := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop, List.length_append, List.length_take,
    List.length_drop, List.getElem?_append]
  split
  · split
    · omega
    · rw [if_pos (by omega)]
      congr 1
      omega
  · rfl

/-- A distance reaching past the write cursor in a full ring. -/
theorem ring_far (a : List UInt8) (off wn ws d n : Nat) (h1 : wn ≤ ws) (fit : off + ws ≤ a.length)
    (hd1 : wn < d) (hd2 : d ≤ ws) (hn : n ≤ d - wn) :
    ((((a.drop (off + wn)).take (ws - wn) ++ (a.drop off).take wn).drop
        (((a.drop (off + wn)).take (ws - wn) ++ (a.drop off).take wn).length - d)).take n) =
      (a.drop (off + (ws - (d - wn)))).take n := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop, List.length_append, List.length_take,
    List.length_drop, List.getElem?_append]
  split
  · split
    · rw [if_pos (by omega)]
      congr 1
      omega
    · omega
  · rfl

/-- A window distance in the format: the bytes come from the retained
history before the call. -/
theorem window_history (dict logOut callOut : List UInt8) (ws dist n : Nat)
    (far : callOut.length < dist)
    (reach : dist - callOut.length ≤
      ((dict ++ logOut).drop ((dict ++ logOut).length - ws)).length)
    (hn : n ≤ dist - callOut.length) :
    copyBack dict dist n (logOut ++ callOut) = logOut ++ callOut ++
      ((((dict ++ logOut).drop ((dict ++ logOut).length - ws)).drop
        (((dict ++ logOut).drop ((dict ++ logOut).length - ws)).length -
          (dist - callOut.length))).take n) := by
  simp only [List.length_drop] at reach
  rw [copyBack_far dict dist n _ (by omega) (by simp only [List.length_append] at reach ⊢; omega)]
  congr 1
  rw [← List.append_assoc dict logOut callOut]
  generalize dict ++ logOut = H at reach ⊢
  rw [List.length_append, show H.length + callOut.length - dist = H.length - (dist - callOut.length)
    by omega, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega), List.drop_drop,
    List.length_drop]
  congr 2
  omega

/-- The number of bytes a window holds. -/
theorem dictionary_length {h : Heap} {s : InflateState} {xs : List UInt8}
    (bounds : s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) (dictionary : InflateDictionary h s xs) :
    s.whave.toNat = xs.length := by
  have nextLe : s.wnext.toNat ≤ s.whave.toNat := UInt32.le_iff_toNat_le.mp bounds.1
  have haveLe : s.whave.toNat ≤ s.wsize.toNat := UInt32.le_iff_toNat_le.mp bounds.2
  rcases dictionary with ⟨zero, rfl⟩ | ⟨r, off, a, _, _, fits, rfl⟩
  · rw [zero]; rfl
  · rw [UInt32.toNat_sub_of_le _ _ bounds.1]
    simp only [List.length_append, List.length_take, List.length_drop, Array.length_toList]
    omega

/-- The window after a write elsewhere, for a state with the same window. -/
theorem dictionary_put_ne {h : Heap} {dest : BRef} {arr : Array UInt8} {zs : Nat}
    {s s' sv : InflateState} {xs : List UInt8}
    (window : sv.window = s.window) (wsize : sv.wsize = s.wsize) (wnext : sv.wnext = s.wnext)
    (whave : sv.whave = s.whave) (priv : ∀ w o, s.window = .ref w o → w ≠ dest)
    (dictionary : InflateDictionary h s xs) :
    InflateDictionary (setI (Space.put h dest arr) zs s') sv xs := by
  unfold InflateDictionary at dictionary ⊢
  rw [window, wsize, wnext, whave]
  rcases dictionary with empty | ⟨r, off, a, w, g, f, c⟩
  · exact Or.inl empty
  · exact Or.inr ⟨r, off, a, w, by rw [byte_view_get_setI, byte_view_get_put_ne h (priv r off w)]; exact g,
      f, c⟩

theorem window_put_ne {h : Heap} {dest : BRef} {arr : Array UInt8} {zs : Nat}
    {s s' sv : InflateState} {dict out : List UInt8}
    (window : sv.window = s.window) (wsize : sv.wsize = s.wsize) (wnext : sv.wnext = s.wnext)
    (whave : sv.whave = s.whave) (priv : ∀ w o, s.window = .ref w o → w ≠ dest)
    (meaning : WindowMeaning h s dict out) :
    WindowMeaning (setI (Space.put h dest arr) zs s') sv dict out := by
  rcases meaning with ⟨nonzero, dictionary⟩ | ⟨z1, z2, z3⟩
  · refine Or.inl ⟨by rw [wsize]; exact nonzero, ?_⟩
    rw [wsize]
    exact dictionary_put_ne window wsize wnext whave priv dictionary
  · exact Or.inr ⟨by rw [wsize]; exact z1, by rw [whave]; exact z2, z3⟩

/-! ## Stage, parse and configuration facts -/

/-- The only stage a `MATCH` state can stand for. -/
theorem stage_of_match {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage) (mode : s.mode = MATCH) :
    ∃ header out final L D remaining dist,
      stage = .body header ⟨out, final, .codes L D (.copy remaining dist)⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rw [mode] at lo hi
    exact absurd hi (by decide)
  · have := stageFacts
    simp only [LoopStageMatches] at this
    rw [mode] at this
    exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      exact absurd m (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m | m | m <;> (rw [mode] at m; exact absurd m (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · rw [mode] at rest; rcases rest.1 with m | m <;> exact absurd m (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · rw [mode] at rest; exact absurd rest.1 (by decide)
      · exact ⟨header, out, final, L, D, remaining, dist, rfl⟩
      · rw [mode] at rest; exact absurd rest.1 (by decide)
    · obtain ⟨m, _⟩ := body
      rw [mode] at m
      rcases m with m | m <;> exact absurd m (by decide)
  · obtain ⟨m, _⟩ := stageFacts
    rw [mode] at m
    rcases m with m | m <;> exact absurd m (by decide)
  · have m : s.mode = DONE := stageFacts
    rw [mode] at m
    exact absurd m (by decide)

/-- A pending match was reached by a complete match token. -/
theorem parsed_copy_inv {dict : List UInt8} {bits : List Bool} {out : List UInt8} {final : Bool}
    {L D : List Nat} {remaining dist : Nat}
    (parsed : DeflateParsed dict bits ⟨out, final, .codes L D (.copy remaining dist)⟩) :
    ∃ c0 tb out0 out' written, bits = c0 ++ tb ∧
      DeflateParsed dict c0 ⟨out0, final, .codes L D .none⟩ ∧
      Token.Step L D dict out0 tb [] out' false ∧
      out' = copyBack dict dist (out'.length - out0.length) out0 ∧
      written < out'.length - out0.length ∧ 0 < dist ∧ dist ≤ (dict ++ out0).length ∧
      dist ≤ 32768 ∧ out = out'.take (out0.length + written) ∧
      remaining = out'.length - out0.length - written := by
  cases parsed with
  | partialCopy prev step eq lt d0 d1 d2 =>
    exact ⟨_, _, _, _, _, rfl, prev, step, eq, lt, d0, d1, d2, rfl, rfl⟩
  | partialToken _ _ pp => exact absurd pp (by simp [PendingParsed])

/-- The body dictionary is a suffix of the installed dictionary. -/
theorem wrapHeader_suffix {wrap : Api.Wrap} {configured : Nat} {dict header bodyDict : List UInt8}
    (wh : WrapHeader wrap configured dict header bodyDict) : ∃ p, dict = p ++ bodyDict := by
  have drop : ∀ w, ∃ p, dict = p ++ bodyDictionary w dict :=
    fun w => ⟨dict.take (dict.length - w), (List.take_append_drop _ _).symm⟩
  have zl : ∀ (window : Nat),
      bodyDict = (if header.length = 2 then [] else bodyDictionary window dict) →
      ∃ p, dict = p ++ bodyDict := by
    intro window eq
    rw [eq]
    split
    · exact ⟨dict, by simp⟩
    · exact drop window
  cases wrap with
  | raw => rw [wh.2]; exact drop _
  | zlib => obtain ⟨window, _, eq⟩ := wh; exact zl window eq
  | gzip => rw [wh.2]; exact ⟨dict, by simp⟩
  | auto =>
    rcases wh with ⟨window, _, eq⟩ | ⟨_, eq⟩
    · exact zl window eq
    · rw [eq]; exact ⟨dict, by simp⟩

/-- With a full window, the header and the configuration fix the width 15. -/
theorem full_width {wrap : Api.Wrap} {configured : Nat} {dict header bodyDict source : List UInt8}
    {s : InflateState} (config : ConfigMatches s wrap configured)
    (width : HeaderWidth s configured header) (wh : WrapHeader wrap configured dict header bodyDict)
    (full : Api.FullWindow wrap configured source) (pre : header <+: source) :
    s.wbits.toNat = 15 := by
  obtain ⟨_, _, _, _, cfg, _⟩ := config
  obtain ⟨_, _, zero⟩ := width
  have byZlib : ∀ window, ZlibHeader configured dict header window → configured = 0 →
      (source.head? = some 31 ∨ ∀ c, source.head? = some c → c.toNat / 16 + 8 = 15) →
      s.wbits.toNat = 15 := by
    intro window zh c0 cinfo
    have notGz := zlibHeader_not_gzip zh
    have e := (zero c0).2 notGz
    obtain ⟨cmf, flg, ok, _, _, shape⟩ := zh
    have hd : header.headD 0 = cmf := by rcases shape with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
    have sh : source.head? = some cmf := by
      obtain ⟨t, rfl⟩ := pre
      rcases shape with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
    rcases cinfo with h31 | ci
    · have c31 : cmf = 31 := Option.some.inj (sh.symm.trans h31)
      subst c31
      exact absurd ok.1 (by decide)
    · rw [hd, Zlib.windowSize, ci cmf sh] at e
      exact (Nat.pow_right_inj (by decide : 1 < 2)).mp e
  have byGzip : GzipHeader header → configured = 0 → s.wbits.toNat = 15 :=
    fun g c0 => (zero c0).1 (gzipHeader_is_gzip g)
  cases wrap with
  | raw =>
    have c15 : configured = 15 := full
    rw [cfg (by omega), c15]
  | gzip =>
    rcases full with c0 | c15
    · exact byGzip wh.1 c0
    · rw [cfg (by omega), c15]
  | zlib =>
    rcases full with c15 | ⟨c0, ci⟩
    · rw [cfg (by omega), c15]
    · obtain ⟨window, zh, _⟩ := wh
      exact byZlib window zh c0 (Or.inr ci)
  | auto =>
    rcases full with c15 | ⟨c0, ci⟩
    · rw [cfg (by omega), c15]
    · rcases wh with ⟨window, zh, _⟩ | ⟨g, _⟩
      · exact byZlib window zh c0 ci
      · exact byGzip g c0

/-- `if a > b then b else a` is the minimum. -/
theorem cap_toNat (a b : UInt32) : (if a > b then b else a).toNat = min a.toNat b.toNat := by
  split
  · rename_i lt
    have := UInt32.lt_iff_toNat_lt.mp lt
    omega
  · rename_i nlt
    have : ¬ b.toNat < a.toNat := fun lt => nlt (UInt32.lt_iff_toNat_lt.mpr lt)
    omega


/-- The call's output read back from its array. -/
theorem bytes_ref {h : Heap} {dest : BRef} {output : Array UInt8} {o0 : Nat} {xs : List UInt8}
    (view : Bytes h (.ref dest o0) xs.length xs) (get : Space.get h dest = some output) :
    (output.toList.drop o0).take xs.length = xs ∧ o0 + xs.length ≤ output.size := by
  rcases view with ⟨null, _, _⟩ | ⟨r, i, a, ptr, get', fits, eq⟩
  · cases null
  · obtain ⟨hr, hi⟩ := Ptr.ref.inj ptr
    subst hr hi
    have arrays : a = output := Option.some.inj (get'.symm.trans get)
    subst arrays
    exact ⟨eq.symm, fits⟩

/-! ## Rebuilding the loop meaning after a copy -/

/-- The registers after one copied segment of `n` bytes at `o`. -/
def regsAfter (l : IL) (n : UInt32) (dest : BRef) (o : Nat) (fr : BPtr) : IL :=
  { l with left := l.left - n, copy := 0, put := .ref dest (o + n.toNat), from_ := fr }

open ZlibF.Math.InflateMatchCopy in
/-- Copying `n` bytes after the call's output, with the state's length and
mode updated, keeps the loop meaning for a parse position `pos` whose output
is the old one followed by the copied bytes. -/
theorem rebuild {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {callOut : List UInt8} {consumed held : List Bool} {header bodyDict : List UInt8}
    {bitsP : List Bool} {pos : DeflatePos} {m : UInt32} {dest : BRef} {o0 : Nat}
    {output : Array UInt8} {n : UInt32}
    (st : c.st = some (.tab zs)) (retOk : l.ret = Z_OK)
    (config : ConfigMatches (loopState s l) f.wrap f.configured) (msync : m ≠ SYNC)
    (haveLe : l.have_.toNat ≤ l.in_.toNat) (inLen : l.in_.toNat = f.inp.length)
    (binv : BitInv h l (f.inp.drop (loopRead l)))
    (leftLe : l.left.toNat ≤ l.out_.toNat) (pendBase : loopPending l = callOut.length)
    (startEq : f.start = .ref dest o0)
    (outBytes : Bytes h (.ref dest o0) callOut.length callOut)
    (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (room : o0 + callOut.length + l.left.toNat ≤ output.size)
    (sepIn : Separate (.ref dest (o0 + callOut.length)) l.left.toNat l.next l.have_.toNat)
    (sepWin : Separate (.ref dest (o0 + callOut.length)) l.left.toNat s.window s.wsize.toNat)
    (sepOutIn : Separate (.ref dest o0) callOut.length l.next l.have_.toNat)
    (bitsEq : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = consumed ++ held)
    (heldBits : HeldBits (loopState s l) held)
    (wrapHeader : WrapHeader f.wrap f.configured f.dict header bodyDict)
    (consumedEq : consumed = bytesToBits header ++ bitsP)
    (parsed : DeflateParsed bodyDict bitsP pos)
    (window : WindowMeaning h (loopState s l) f.dict f.logOut)
    (check : CheckMeaning (loopState s l) f.wrap header
      ((f.logOut ++ callOut).take ((f.logOut ++ callOut).length - loopPending l)))
    (wrapM : FlagsMatch (loopState s l) f.wrap header ∧
      HeaderWidth (loopState s l) f.configured header)
    (priv : ∀ w o, s.window = .ref w o → w ≠ dest)
    (positive : 0 < n.toNat) (nLeft : n.toNat ≤ l.left.toNat)
    (same : Bool) (saved : Array UInt8) (so : Nat) (fr : BPtr)
    (body : BodyMatches
      (setI (Space.put h dest (copy same saved n.toNat so (o0 + callOut.length) output)) zs
        { s with length := s.length - n, mode := m })
      (loopState { s with length := s.length - n, mode := m }
        (regsAfter l n dest (o0 + callOut.length) fr)) pos)
    (outEq : pos.out = f.logOut ++ (callOut ++
      ((copy same saved n.toNat so (o0 + callOut.length) output).toList.drop
        (o0 + callOut.length)).take n.toNat)) :
    LoopMatches c f
      (setI (Space.put h dest (copy same saved n.toNat so (o0 + callOut.length) output)) zs
        { s with length := s.length - n, mode := m })
      (regsAfter l n dest (o0 + callOut.length) fr) := by
  have keep := copy_slice same saved n.toNat so (o0 + callOut.length) output o0 callOut.length
    (by omega) (Or.inl (Nat.le_refl _))
  have size := copy_size same saved n.toNat so (o0 + callOut.length) output
  have sepCond : f.inp.drop (loopRead l) = [] ∨ ∀ i, l.next = .ref dest i →
      i + (f.inp.drop (loopRead l)).length ≤ o0 + callOut.length ∨
        o0 + callOut.length + n.toNat ≤ i := by
    rcases sepIn with zero | zero | sep
    · omega
    · left
      apply List.eq_nil_of_length_eq_zero
      rw [← binv.have_eq]
      exact zero
    · right
      intro i ptr
      rw [ptr] at sep
      simp only at sep
      rw [← binv.have_eq]
      rcases sep with ne | before | after
      · exact absurd rfl ne
      · right; omega
      · left; exact after
  have binv' := bitInv_setI (zs := zs) (s := { s with length := s.length - n, mode := m })
    (binv.match_copy_ranges get write same saved n.toNat so (o0 + callOut.length) sepCond)
  generalize copy same saved n.toNat so (o0 + callOut.length) output = arr at keep size binv' body outEq ⊢
  generalize yDef : (arr.toList.drop (o0 + callOut.length)).take n.toNat = Y at outEq
  have yLen : Y.length = n.toNat := by
    rw [← yDef]
    simp only [List.length_take, List.length_drop, Array.length_toList, size]
    omega
  have leftSub : (l.left - n).toNat = l.left.toNat - n.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr nLeft)
  have pendEq : loopPending (regsAfter l n dest (o0 + callOut.length) fr) =
      loopPending l + n.toNat := by
    simp only [loopPending, regsAfter, leftSub]
    simp only [loopPending] at pendBase
    omega
  have view := (bytes_ref outBytes get).1
  refine ⟨zs, { s with length := s.length - n, mode := m }, callOut ++ Y, consumed, held,
    .body header pos, st, setI_istates_same _ _ _, retOk,
    ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, msync⟩, haveLe, inLen,
    ⟨binv'.have_eq, binv'.next, binv'.hold_lt⟩, ?_, ⟨?_, fun _ _ _ => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    bitsEq, ⟨heldBits.1, heldBits.2⟩, ⟨bodyDict, bitsP, wrapHeader, consumedEq, parsed⟩,
    ⟨body, ?_, ?_⟩, ⟨wrapM.1, wrapM.2⟩, ?_⟩
  · show (l.left - n).toNat ≤ l.out_.toNat
    rw [leftSub]
    omega
  · rw [pendEq, List.length_append, yLen, pendBase]
    exact Nat.le_refl _
  · rw [pendEq, List.length_append, yLen, pendBase]
  · show Ptr.ref dest (o0 + callOut.length + n.toNat) = inputAdvance f.start (callOut ++ Y).length
    rw [startEq, List.length_append, yLen]
    simp only [inputAdvance, Nat.add_assoc]
  · rw [startEq, List.length_append, yLen]
    apply bytes_setI
    refine Or.inr ⟨dest, o0, arr, rfl, byte_view_get_put get write arr, by rw [size]; omega, ?_⟩
    rw [slice_split, keep, view, yDef]
  · refine Or.inr ⟨dest, o0 + callOut.length + n.toNat, arr, rfl, ?_, ?_, ?_⟩
    · rw [byte_view_get_setI]; exact byte_view_get_put get write _
    · rw [byte_view_ro_setI, byte_view_ro_put]; exact write
    · show o0 + callOut.length + n.toNat + (l.left - n).toNat ≤ arr.size
      rw [size, leftSub]
      omega
  · show Separate (.ref dest (o0 + callOut.length + n.toNat)) (l.left - n).toNat l.next l.have_.toNat
    rw [leftSub]
    exact separate_shrink_n sepIn nLeft
  · show Separate (.ref dest (o0 + callOut.length + n.toNat)) (l.left - n).toNat s.window
      s.wsize.toNat
    rw [leftSub]
    exact separate_shrink_n sepWin nLeft
  · rw [startEq, List.length_append, yLen]
    exact separate_grow_n sepOutIn sepIn nLeft
  · exact window_put_ne rfl rfl rfl rfl priv window
  · rw [pendEq, show loopPending l + n.toNat = loopPending l + Y.length by rw [yLen],
      take_after_append _ _ _ _ (by omega)]
    exact check
  · exact outEq

set_option maxHeartbeats 1000000 in
open ZlibF.Math.InflateMatchCopy in
/-- One copied segment of a pending match keeps the loop meaning: the parse
moves over the copied bytes, to the end of the token when the match is done. -/
theorem emit {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    {callOut : List UInt8} {consumed held : List Bool} {header bodyDict : List UInt8}
    {c0 tb : List Bool} {out0 out' : List UInt8} {written : Nat} {final : Bool} {L D : List Nat}
    {dist : Nat} {dest : BRef} {o0 : Nat} {output : Array UInt8} {n : UInt32}
    (st : c.st = some (.tab zs)) (hs : h.istates zs = some s) (retOk : l.ret = Z_OK)
    (config : ConfigMatches (loopState s l) f.wrap f.configured)
    (haveLe : l.have_.toNat ≤ l.in_.toNat) (inLen : l.in_.toNat = f.inp.length)
    (binv : BitInv h l (f.inp.drop (loopRead l)))
    (leftLe : l.left.toNat ≤ l.out_.toNat) (pendBase : loopPending l = callOut.length)
    (startEq : f.start = .ref dest o0)
    (outBytes : Bytes h (.ref dest o0) callOut.length callOut)
    (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (room : o0 + callOut.length + l.left.toNat ≤ output.size)
    (sepIn : Separate (.ref dest (o0 + callOut.length)) l.left.toNat l.next l.have_.toNat)
    (sepWin : Separate (.ref dest (o0 + callOut.length)) l.left.toNat s.window s.wsize.toNat)
    (sepOutIn : Separate (.ref dest o0) callOut.length l.next l.have_.toNat)
    (bitsEq : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = consumed ++ held)
    (heldBits : HeldBits (loopState s l) held)
    (wrapHeader : WrapHeader f.wrap f.configured f.dict header bodyDict)
    (consumedEq : consumed = bytesToBits header ++ (c0 ++ tb))
    (prev : DeflateParsed bodyDict c0 ⟨out0, final, .codes L D .none⟩)
    (step : Token.Step L D bodyDict out0 tb [] out' false)
    (eqOut : out' = copyBack bodyDict dist (out'.length - out0.length) out0)
    (lt : written < out'.length - out0.length) (d0 : 0 < dist)
    (d1 : dist ≤ (bodyDict ++ out0).length) (d2 : dist ≤ 32768)
    (outputEq : out'.take (out0.length + written) = f.logOut ++ callOut)
    (window : WindowMeaning h (loopState s l) f.dict f.logOut)
    (check : CheckMeaning (loopState s l) f.wrap header
      ((f.logOut ++ callOut).take ((f.logOut ++ callOut).length - loopPending l)))
    (wrapM : FlagsMatch (loopState s l) f.wrap header ∧
      HeaderWidth (loopState s l) f.configured header)
    (priv : ∀ w o, s.window = .ref w o → w ≠ dest)
    (mode : s.mode = MATCH) (last : s.last = (if final then 1 else 0))
    (lenTable : TableMeaning h s.lencode s.lenbits LENS L)
    (distTable : TableMeaning h s.distcode s.distbits DISTS D)
    (lengthEq : s.length.toNat = out'.length - out0.length - written)
    (offsetEq : s.offset.toNat = dist) (bitsLt : l.bits.toNat < 8)
    (positive : 0 < n.toNat) (nLeft : n.toNat ≤ l.left.toNat) (nLen : n.toNat ≤ s.length.toNat)
    (same : Bool) (saved : Array UInt8) (so : Nat) (fr : BPtr)
    (format : f.logOut ++ (callOut ++
      ((copy same saved n.toNat so (o0 + callOut.length) output).toList.drop
        (o0 + callOut.length)).take n.toNat) =
      copyBack f.dict dist n.toNat (f.logOut ++ callOut)) :
    LoopMatches c f
      (setI (Space.put h dest (copy same saved n.toNat so (o0 + callOut.length) output)) zs
        (matchEmitState s n))
      (regsAfter l n dest (o0 + callOut.length) fr) := by
  have lenOut : out'.length = out0.length + (out'.length - out0.length) := by
    have := (ZlibF.Math.LZ77History.copy_back_extends_history bodyDict out0 dist
      (out'.length - out0.length)).2
    rw [← eqOut] at this
    exact this
  have first : out'.take (out0.length + written) = copyBack bodyDict dist written out0 := by
    have t := copyBack_take bodyDict out0 dist (out'.length - out0.length) written (by omega)
    rw [← eqOut] at t
    exact t
  have outLen : out0.length ≤ (f.logOut ++ callOut).length := by
    rw [← outputEq, List.length_take]
    omega
  have next : out'.take (out0.length + (written + n.toNat)) =
      copyBack f.dict dist n.toNat (f.logOut ++ callOut) := by
    have t := copyBack_take bodyDict out0 dist (out'.length - out0.length) (written + n.toNat)
      (by omega)
    rw [← eqOut] at t
    rw [t, ZlibF.Math.LZ77History.copy_back_compose, ← first, outputEq]
    obtain ⟨p, pe⟩ := wrapHeader_suffix wrapHeader
    exact (copyBack_dict_suffix pe dist n.toNat _
      (by simp only [List.length_append] at d1 outLen ⊢; omega)).symm
  have lengthSub : (s.length - n).toNat = s.length.toNat - n.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr nLen)
  by_cases fin : s.length - n = 0
  · have stateEq : matchEmitState s n = { s with length := s.length - n, mode := LEN } := by
      simp [matchEmitState, fin]
    rw [stateEq]
    have whole : out0.length + (written + n.toNat) = out'.length := by
      have : (s.length - n).toNat = 0 := by rw [fin]; rfl
      omega
    rw [whole, List.take_length] at next
    exact rebuild (m := LEN) (pos := ⟨out', final, .codes L D .none⟩) st retOk config (by decide) haveLe inLen
      binv leftLe pendBase startEq outBytes get write room sepIn sepWin sepOutIn bitsEq heldBits
      wrapHeader consumedEq (DeflateParsed.token prev step) window check wrapM priv positive nLeft
      same saved so fr
      ⟨last, table_after (s' := { s with length := s.length - n, mode := LEN }) hs rfl dest _ lenTable,
        table_after (s' := { s with length := s.length - n, mode := LEN }) hs rfl dest _ distTable,
        Or.inr rfl,
        Or.inl bitsLt⟩
      (next.trans format.symm)
  · have notZero : (s.length - n == 0) = false := by simpa using fin
    have stateEq : matchEmitState s n = { s with length := s.length - n, mode := MATCH } := by
      simp only [matchEmitState, notZero, Bool.false_eq_true, ↓reduceIte]
      rw [← mode]
    rw [stateEq]
    have more : written + n.toNat < out'.length - out0.length := by
      have : (s.length - n).toNat ≠ 0 := fun zero => fin (UInt32.toNat_inj.mp (by simpa using zero))
      omega
    exact rebuild (m := MATCH)
      (pos := ⟨out'.take (out0.length + (written + n.toNat)), final,
        .codes L D (.copy (out'.length - out0.length - (written + n.toNat)) dist)⟩)
      st retOk config (by decide) haveLe inLen binv leftLe pendBase startEq outBytes get write room
      sepIn sepWin sepOutIn bitsEq heldBits wrapHeader consumedEq
      (DeflateParsed.partialCopy prev step eqOut more d0 d1 d2) window check wrapM priv positive
      nLeft same saved so fr
      ⟨last, table_after (s' := { s with length := s.length - n, mode := MATCH }) hs rfl dest _ lenTable,
        table_after (s' := { s with length := s.length - n, mode := MATCH }) hs rfl dest _ distTable,
        rfl,
        by show (s.length - n).toNat = _; rw [lengthSub]; omega, offsetEq, bitsLt⟩
      (next.trans format.symm)


/-! ## The step -/

set_option maxHeartbeats 4000000 in
/-- `case MATCH` keeps the format meaning. With no output room it leaves with
nothing changed (`left = 0`). A distance beyond this call's output and the
window goes to `BAD`, and the input read so far has no valid completion with
a full window. Otherwise it copies a positive segment of the match from the
call's output or from the window ring: the output and the parse grow by the
same bytes, and no input is read.

The safety invariant of the decoder state supplies the facts beyond
`LoopMatches`: the stream record (for `Env`), the window bounds
`wnext ≤ whave ≤ wsize`, the enabled distance check `sane ≠ 0`, the window
size `2 ^ wbits` once allocated, a ring that is full once it has wrapped
(`whave < wsize → wnext = whave`), and a window block distinct from the
caller's output buffer. -/
theorem match_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (matching : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = MATCH)
    (bounds : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize)
    (sane : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.sane ≠ 0)
    (wsizeBits : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wsize ≠ 0 → s.wsize.toNat = 2 ^ s.wbits.toNat)
    (ring : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.whave < s.wsize → s.wnext = s.whave)
    (privateWindow : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      ∀ w o d i, s.window = .ref w o → l.put = .ref d i → w ≠ d) :
    ∃ result l' h', runX (inflate_MATCH c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ l.left = 0 ∧ l' = l ∧ h' = h) ∨
       (result = .ok () ∧ loopRead l' = loopRead l ∧
         (LoopMatches c f h' l' ∨
          ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
            LoopDoomed f l')))) := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    ⟨pendLe, pendBody⟩, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed,
    stageM, wrapM, outputEq⟩ := loop
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have mode : s.mode = MATCH := matching zs s st hs
  by_cases empty : l.left = 0
  · exact ⟨_, _, _, inflate_MATCH_wait c h l empty, Or.inl ⟨rfl, empty, rfl, rfl⟩⟩
  have leftPos : 0 < l.left.toNat := by
    have nz : l.left.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp (by simpa using zero))
    omega
  obtain ⟨header, out, final, L, D, remaining, dist, rfl⟩ := stage_of_match stageM mode
  have pendBase := pendBody _ _ rfl
  obtain ⟨⟨last, lenTable, distTable, _, lengthEq, offsetEq, bitsLt⟩, window, check⟩ := stageM
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  obtain ⟨c0, tb, out0, out', written, rfl, prev, step, eqOut, lt, d0, d1, d2, rfl, rfl⟩ :=
    parsed_copy_inv deflate
  have outputEq' : out'.take (out0.length + written) = f.logOut ++ callOut := outputEq
  have lengthEq' : s.length.toNat = out'.length - out0.length - written := lengthEq
  have offsetEq' : s.offset.toNat = dist := offsetEq
  have bitsLt' : l.bits.toNat < 8 := bitsLt
  have last' : s.last = (if final then 1 else 0) := last
  rcases writable with ⟨_, zero⟩ | ⟨dest, oo, output, put, get, write, room⟩
  · exact absurd (UInt32.toNat_inj.mp (by simpa using zero)) empty
  obtain ⟨o0, startEq, offEq⟩ : ∃ o0, f.start = .ref dest o0 ∧ oo = o0 + callOut.length := by
    rw [put] at putEq
    cases hst : f.start with
    | null => rw [hst] at putEq; simp [inputAdvance] at putEq
    | ref d o =>
        rw [hst] at putEq
        simp only [inputAdvance, Ptr.ref.injEq] at putEq
        obtain ⟨rfl, rfl⟩ := putEq
        exact ⟨o, rfl, rfl⟩
  subst offEq
  rw [startEq] at outBytes sepOutIn
  rw [put] at sepIn sepWin
  have priv : ∀ w o, s.window = .ref w o → w ≠ dest :=
    fun w o hw => privateWindow zs s st hs w o dest _ hw put
  have lenOut : out'.length = out0.length + (out'.length - out0.length) := by
    have := (ZlibF.Math.LZ77History.copy_back_extends_history bodyDict out0 dist
      (out'.length - out0.length)).2
    rw [← eqOut] at this
    exact this
  have outLen : (f.logOut ++ callOut).length = out0.length + written := by
    rw [← outputEq', List.length_take]
    omega
  have lengthPos : 0 < s.length.toNat := by omega
  have pendNat : (l.out_ - l.left).toNat = callOut.length := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr leftLe)]
    exact pendBase
  have viewFit := bytes_ref outBytes get
  by_cases inWindow : s.offset > l.out_ - l.left
  · have inNat : callOut.length < dist := by
      have := UInt32.lt_iff_toNat_lt.mp inWindow
      omega
    have dNat : (s.offset - (l.out_ - l.left)).toNat = dist - callOut.length := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr
        (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp inWindow))), pendNat, offsetEq']
    obtain ⟨p, pe⟩ := wrapHeader_suffix wrapHeader
    have dictLen : f.dict.length = p.length + bodyDict.length := by rw [pe, List.length_append]
    have d1' := d1
    simp only [List.length_append] at d1' outLen
    have bnds := bounds zs s st hs
    have nextLe : s.wnext.toNat ≤ s.whave.toNat := UInt32.le_iff_toNat_le.mp bnds.1
    have haveLe' : s.whave.toNat ≤ s.wsize.toNat := UInt32.le_iff_toNat_le.mp bnds.2
    by_cases far : s.offset - (l.out_ - l.left) > s.whave
    · -- too far back
      obtain ⟨i, _, run⟩ := matchSelect_bad_run E l empty inWindow far (sane zs s st hs)
      refine ⟨_, _, _, (by rw [inflate_MATCH_select_cut]; exact run),
        Or.inr ⟨rfl, rfl, Or.inr ⟨?_, ?_⟩⟩⟩
      · intro zs' s' st' hs'
        rw [st] at st'
        cases st'
        simp only [badHeap, setI_istates_same, Option.some.injEq] at hs'
        rw [← hs']
      · intro source decoded valid full started
        have farNat : s.whave.toNat < dist - callOut.length := by
          rw [← dNat]
          exact UInt32.lt_iff_toNat_lt.mp far
        have pre : header <+: source := by
          have bp : bytesToBits header <+: bytesToBits (f.logIn ++ f.inp.take (loopRead l)) := by
            rw [bitsEq, consumedEq]
            exact ⟨c0 ++ tb ++ held, by simp⟩
          exact (bytesToBits_prefix_iff.mp bp).trans started
        have w15 : s.wbits.toNat = 15 := full_width config wrapM.2 wrapHeader full pre
        rcases window with ⟨nz, dictn⟩ | ⟨_, _, hEmpty⟩
        · have wl : s.whave.toNat =
              ((f.dict ++ f.logOut).drop ((f.dict ++ f.logOut).length - s.wsize.toNat)).length :=
            dictionary_length (s := loopState s l) bnds dictn
          have ws : s.wsize.toNat = 32768 := by rw [wsizeBits zs s st hs nz, w15]
          simp only [List.length_drop, List.length_append] at wl
          omega
        · have e : (f.dict ++ f.logOut).length = 0 := by rw [hEmpty]; rfl
          simp only [List.length_append] at e
          omega
    · have reachNat : dist - callOut.length ≤ s.whave.toNat := by
        have : ¬ s.whave.toNat < (s.offset - (l.out_ - l.left)).toNat :=
          fun lt => far (UInt32.lt_iff_toNat_lt.mpr lt)
        omega
      obtain ⟨_, dictn⟩ : s.wsize ≠ 0 ∧ InflateDictionary h (loopState s l)
          ((f.dict ++ f.logOut).drop ((f.dict ++ f.logOut).length - s.wsize.toNat)) := by
        rcases window with w | ⟨_, h0, _⟩
        · exact w
        · exfalso
          have : s.whave.toNat = 0 := by rw [show s.whave = 0 from h0]; rfl
          omega
      have wl : s.whave.toNat =
          ((f.dict ++ f.logOut).drop ((f.dict ++ f.logOut).length - s.wsize.toNat)).length :=
        dictionary_length (s := loopState s l) bnds dictn
      rcases dictn with ⟨h0, _⟩ | ⟨wr, off, a, winPtr, getW, fitW, content⟩
      · exfalso
        have : s.whave.toNat = 0 := by rw [show s.whave = 0 from h0]; rfl
        omega
      have winPtr' : s.window = .ref wr off := winPtr
      have fitW' : off + s.wsize.toNat ≤ a.size := fitW
      have content' : (f.dict ++ f.logOut).drop ((f.dict ++ f.logOut).length - s.wsize.toNat) =
          (a.toList.drop (off + s.wnext.toNat)).take (s.whave - s.wnext).toNat ++
            (a.toList.drop off).take s.wnext.toNat := content
      rw [UInt32.toNat_sub_of_le _ _ bnds.1] at content'
      have privW := priv wr off winPtr'
      have dfalse : decide (wr = dest) = false := decide_eq_false privW
      have sourceGet : Space.get h wr = some (if wr = dest then output else a) := by
        rw [if_neg privW]
        exact getW
      by_cases wrap : s.offset - (l.out_ - l.left) > s.wnext
      · -- the segment before the ring's end
        have wrapNat : s.wnext.toNat < dist - callOut.length := by
          rw [← dNat]
          exact UInt32.lt_iff_toNat_lt.mp wrap
        have fullRing : s.whave.toNat = s.wsize.toNat := by
          apply Classical.byContradiction
          intro ne
          have lt : s.whave < s.wsize := UInt32.lt_iff_toNat_lt.mpr (by omega)
          have same := ring zs s st hs lt
          rw [same] at wrapNat
          omega
        have spanNat : (s.offset - (l.out_ - l.left) - s.wnext).toNat =
            dist - callOut.length - s.wnext.toNat := by
          rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [dNat]; omega)), dNat]
        have startNat : (s.wsize - (s.offset - (l.out_ - l.left) - s.wnext)).toNat =
            s.wsize.toNat - (dist - callOut.length - s.wnext.toNat) := by
          rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [spanNat]; omega)),
            spanNat]
        obtain ⟨n, nDef⟩ : ∃ n, (if (if s.offset - (l.out_ - l.left) - s.wnext > s.length then s.length
            else s.offset - (l.out_ - l.left) - s.wnext) > l.left then l.left
            else (if s.offset - (l.out_ - l.left) - s.wnext > s.length then s.length
              else s.offset - (l.out_ - l.left) - s.wnext)) = n := ⟨_, rfl⟩
        have nNat : n.toNat =
            min (min (dist - callOut.length - s.wnext.toNat) s.length.toNat) l.left.toNat := by
          rw [← nDef, cap_toNat, cap_toNat, spanNat]
        have address : s.window.add ((s.wsize - (s.offset - (l.out_ - l.left) - s.wnext)).toNat : Int) h =
            .ok (.ref wr (off + (s.wsize - (s.offset - (l.out_ - l.left) - s.wnext)).toNat), h) := by
          rw [winPtr']
          exact Ptr.add_nat_ok getW (by rw [startNat]; omega)
        have sel := matchSelect_wrap_cut E l empty inWindow far wrap address
        dsimp only at sel
        rw [nDef] at sel
        have run := matchEmit_run (c := c) E (l := l) (source := wr) (saved := a) (copy := n)
          (sourceOffset := off + (s.wsize - (s.offset - (l.out_ - l.left) - s.wnext)).toNat)
          put get write sourceGet (by omega) (by rw [if_neg privW, startNat]; omega) (by omega)
        refine ⟨_, _, _, (sel.trans run),
          Or.inr ⟨rfl, rfl, Or.inl ?_⟩⟩
        refine emit st hs retOk config haveLe inLen binv leftLe pendBase startEq outBytes get write room
          sepIn sepWin sepOutIn bitsEq heldBits wrapHeader consumedEq prev step eqOut lt d0 d1 d2
          outputEq' window check wrapM priv mode last' lenTable distTable lengthEq' offsetEq' bitsLt'
          (by omega) (by omega) (by omega)
          (decide (wr = dest)) a (off + (s.wsize - (s.offset - (l.out_ - l.left) - s.wnext)).toNat) _ ?_
        rw [dfalse, copy_saved_slice a output n.toNat _ _ (by omega) (by rw [startNat]; omega),
          window_history f.dict f.logOut callOut s.wsize.toNat dist n.toNat inNat
            (by rw [← wl]; exact reachNat) (by omega),
          content', fullRing,
          ring_far a.toList off s.wnext.toNat s.wsize.toNat (dist - callOut.length) n.toNat (by omega)
            (by simp only [Array.length_toList]; omega) wrapNat (by omega) (by omega),
          startNat, List.append_assoc]
      · -- the segment before the write cursor
        have nearNat : dist - callOut.length ≤ s.wnext.toNat := by
          have : ¬ s.wnext.toNat < (s.offset - (l.out_ - l.left)).toNat :=
            fun lt => wrap (UInt32.lt_iff_toNat_lt.mpr lt)
          omega
        have startNat : (s.wnext - (s.offset - (l.out_ - l.left))).toNat =
            s.wnext.toNat - (dist - callOut.length) := by
          rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [dNat]; exact nearNat)),
            dNat]
        obtain ⟨n, nDef⟩ : ∃ n, (if (if s.offset - (l.out_ - l.left) > s.length then s.length
            else s.offset - (l.out_ - l.left)) > l.left then l.left
            else (if s.offset - (l.out_ - l.left) > s.length then s.length
              else s.offset - (l.out_ - l.left))) = n := ⟨_, rfl⟩
        have nNat : n.toNat = min (min (dist - callOut.length) s.length.toNat) l.left.toNat := by
          rw [← nDef, cap_toNat, cap_toNat, dNat]
        have address : s.window.add ((s.wnext - (s.offset - (l.out_ - l.left))).toNat : Int) h =
            .ok (.ref wr (off + (s.wnext - (s.offset - (l.out_ - l.left))).toNat), h) := by
          rw [winPtr']
          exact Ptr.add_nat_ok getW (by rw [startNat]; omega)
        have sel := matchSelect_window_cut E l empty inWindow far wrap address
        dsimp only at sel
        rw [nDef] at sel
        have run := matchEmit_run (c := c) E (l := l) (source := wr) (saved := a) (copy := n)
          (sourceOffset := off + (s.wnext - (s.offset - (l.out_ - l.left))).toNat)
          put get write sourceGet (by omega) (by rw [if_neg privW, startNat]; omega) (by omega)
        refine ⟨_, _, _, (sel.trans run),
          Or.inr ⟨rfl, rfl, Or.inl ?_⟩⟩
        refine emit st hs retOk config haveLe inLen binv leftLe pendBase startEq outBytes get write room
          sepIn sepWin sepOutIn bitsEq heldBits wrapHeader consumedEq prev step eqOut lt d0 d1 d2
          outputEq' window check wrapM priv mode last' lenTable distTable lengthEq' offsetEq' bitsLt'
          (by omega) (by omega) (by omega)
          (decide (wr = dest)) a (off + (s.wnext - (s.offset - (l.out_ - l.left))).toNat) _ ?_
        rw [dfalse, copy_saved_slice a output n.toNat _ _ (by omega) (by rw [startNat]; omega),
          window_history f.dict f.logOut callOut s.wsize.toNat dist n.toNat inNat
            (by rw [← wl]; exact reachNat) (by omega),
          content',
          ring_near a.toList off s.wnext.toNat s.whave.toNat (dist - callOut.length) n.toNat nextLe
            (by simp only [Array.length_toList]; omega) nearNat (by omega),
          startNat, List.append_assoc]
  · -- a distance within this call's output
    have outNat : dist ≤ callOut.length := by
      have : ¬ (l.out_ - l.left).toNat < s.offset.toNat :=
        fun lt => inWindow (UInt32.lt_iff_toNat_lt.mpr lt)
      omega
    obtain ⟨n, nDef⟩ : ∃ n, (if s.length > l.left then l.left else s.length) = n := ⟨_, rfl⟩
    have nNat : n.toNat = min s.length.toNat l.left.toNat := by
      rw [← nDef, cap_toNat]
    have address : l.put.add (-(s.offset.toNat : Int)) h =
        .ok (.ref dest (o0 + callOut.length - s.offset.toNat), h) := by
      rw [put]
      exact Ptr.sub_nat_ok get (by omega) (by omega)
    have sel := matchSelect_output_cut E l empty inWindow address
    rw [nDef] at sel
    have run := matchEmit_run (c := c) E (l := l) (source := dest) (saved := output) (copy := n)
      (sourceOffset := o0 + callOut.length - s.offset.toNat)
      put get write (by rw [if_pos rfl]; exact get) (by omega) (by rw [if_pos rfl]; omega) (by omega)
    refine ⟨_, _, _, (sel.trans run),
      Or.inr ⟨rfl, rfl, Or.inl ?_⟩⟩
    refine emit st hs retOk config haveLe inLen binv leftLe pendBase startEq outBytes get write room
          sepIn sepWin sepOutIn bitsEq heldBits wrapHeader consumedEq prev step eqOut lt d0 d1 d2
          outputEq' window check wrapM priv mode last' lenTable distTable lengthEq' offsetEq' bitsLt'
          (by omega) (by omega) (by omega)
      (decide (dest = dest)) output (o0 + callOut.length - s.offset.toNat) _ ?_
    have co := copy_output output n.toNat output callOut o0 dist viewFit.1 (by omega) d0 outNat
    rw [slice_split, ZlibF.Math.InflateMatchCopy.copy_slice true output n.toNat
      (o0 + callOut.length - dist) (o0 + callOut.length) output o0 callOut.length (by omega)
      (Or.inl (Nat.le_refl _)), viewFit.1] at co
    rw [decide_eq_true (rfl : dest = dest), offsetEq',
      ZlibF.Math.LZ77History.retained_history_agrees f.dict f.logOut callOut [] dist n.toNat
        List.nil_suffix d0 (by simpa using outNat), ← co]

#print axioms match_step

end Zlib.Inflate.Proofs.MeaningMatch
