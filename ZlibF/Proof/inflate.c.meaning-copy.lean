import ZlibF.Proof.«inflate.c.meaning-lit»
import ZlibF.Proof.«inflate.c.stored-views»
import ZlibF.Proof.«inflate.c.meaning-leave-short»

/-!
# inflate.c: `COPY_` and `COPY` keep the format meaning

`case COPY` copies the next bytes of a stored block from the input to the
output, as many as the block, the input and the output room allow. With
nothing left in the block it goes to `TYPE`; the parse position moves to the
block boundary, or to the end of the data after the final block. With bytes
left but no input or no room it leaves; only the `copy` register changes.
Otherwise the parse moves over the copied bytes (`DeflateParsed.storedByte`
once per byte). `case COPY_` sets the mode `COPY` and runs `case COPY`.
-/

namespace Zlib.Inflate.Proofs.MeaningCopy
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningWrite Zlib.Inflate.Proofs.MeaningLit
set_option autoImplicit false

/-! ## The stage of a stored block -/

/-- The only stage a `COPY_` or `COPY` state can stand for. -/
theorem stage_of_copy {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage)
    (copy : s.mode = COPY ∨ s.mode = COPY_) :
    ∃ header out final remaining,
      stage = .body header ⟨out, final, .stored remaining⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rcases copy with m | m <;> rw [m] at lo hi <;> exact absurd hi (by decide)
  · have this := stageFacts
    simp only [LoopStageMatches] at this
    rcases copy with m | m <;> rw [m] at this <;> exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨m', _⟩ := body
      rcases copy with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · obtain ⟨m', _⟩ := body
      rcases copy with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · exact ⟨header, out, final, remaining, rfl⟩
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m' | m' | m' <;> rcases copy with m | m <;>
        (rw [m] at m'; exact absurd m' (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · rcases copy with m | m <;> rw [m] at rest <;> rcases rest.1 with m' | m' <;>
          exact absurd m' (by decide)
      · rcases copy with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases copy with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases copy with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases copy with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
      · rcases copy with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide)
    · obtain ⟨m', _⟩ := body
      rcases copy with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
  · obtain ⟨m', _⟩ := stageFacts
    rcases copy with m | m <;> rw [m] at m' <;> rcases m' with m' | m' <;>
      exact absurd m' (by decide)
  · have m' : s.mode = DONE := stageFacts
    rcases copy with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)

/-- Reading the bytes of a stored block one by one. -/
theorem parsed_stored_bytes {dict : List UInt8} : ∀ (bs : List UInt8) {consumed : List Bool}
    {out : List UInt8} {final : Bool} {remaining : Nat},
    DeflateParsed dict consumed ⟨out, final, .stored remaining⟩ → bs.length ≤ remaining →
    DeflateParsed dict (consumed ++ bytesToBits bs)
      ⟨out ++ bs, final, .stored (remaining - bs.length)⟩
  | [], consumed, out, final, remaining, parsed, _ => by
    simpa [bytesToBits] using parsed
  | b :: t, consumed, out, final, remaining, parsed, le => by
    obtain ⟨r, rfl⟩ : ∃ r, remaining = r + 1 :=
      ⟨remaining - 1, by simp only [List.length_cons] at le; omega⟩
    have step := DeflateParsed.storedByte b parsed
    have rest := parsed_stored_bytes t step (by simp only [List.length_cons] at le; omega)
    have e1 : consumed ++ bytesToBits (b :: t) = consumed ++ byteBits b ++ bytesToBits t := by
      simp [bytesToBits]
    have e2 : out ++ b :: t = out ++ [b] ++ t := by simp
    have e3 : r + 1 - (b :: t).length = r - t.length := by simp
    rw [e1, e2, e3]
    exact rest

theorem bytesToBits_app (a b : List UInt8) :
    bytesToBits (a ++ b) = bytesToBits a ++ bytesToBits b := by
  simp [bytesToBits]

/-! ## Heap facts of a copied byte range -/

/-- A list slice outside the copied range is unchanged. -/
theorem slice_copy_outside {output input : Array UInt8} {oo io n i m : Nat}
    (outputFit : oo + n ≤ output.size) (inputFit : io + n ≤ input.size)
    (outside : n = 0 ∨ m = 0 ∨ i + m ≤ oo ∨ oo + n ≤ i) :
    ((copyRange output input oo io n).toList.drop i).take m = (output.toList.drop i).take m := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_take, List.getElem?_drop, Array.getElem?_toList]
  split
  · rw [copyRange_getElem? output input oo io n outputFit inputFit]
    split
    · omega
    · rfl
  · rfl

/-- A readable range separate from the copied range is unchanged. -/
theorem bytes_after_copy {h : Heap} {dest : BRef} {output input : Array UInt8} {oo io n : Nat}
    (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (outputFit : oo + n ≤ output.size) (inputFit : io + n ≤ input.size)
    {p : BPtr} {m : Nat} {xs : List UInt8}
    (sep : Separate (.ref dest oo) n p m) (view : Bytes h p m xs) :
    Bytes (Space.put h dest (copyRange output input oo io n)) p m xs := by
  rcases view with ⟨rfl, rfl, rfl⟩ | ⟨r, i, a', rfl, get', fits, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · right
    by_cases same : r = dest
    · subst same
      have arrays : a' = output := Option.some.inj (get'.symm.trans get)
      subst arrays
      refine ⟨r, i, copyRange a' input oo io n, rfl, byte_view_get_put get' write _,
        by rw [size_copyRange]; exact fits, ?_⟩
      have outside : n = 0 ∨ m = 0 ∨ i + m ≤ oo ∨ oo + n ≤ i := by
        rcases sep with zero | zero | sep
        · exact Or.inl zero
        · exact Or.inr (Or.inl zero)
        · simp only at sep
          rcases sep with ne | lt | lt
          · exact absurd rfl ne
          · exact Or.inr (Or.inr (Or.inr lt))
          · exact Or.inr (Or.inr (Or.inl lt))
      exact (slice_copy_outside outputFit inputFit outside).symm
    · exact ⟨r, i, a', rfl, by rw [byte_view_get_put_ne h same]; exact get', fits, rfl⟩

/-- The window, separate from the copied range, is unchanged. -/
theorem dictionary_after_copy {h : Heap} {dest : BRef} {output input : Array UInt8}
    {oo io n : Nat} (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (outputFit : oo + n ≤ output.size) (inputFit : io + n ≤ input.size)
    {s : InflateState} {xs : List UInt8}
    (bounds : s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize)
    (sep : Separate (.ref dest oo) n s.window s.wsize.toNat) (dictionary : InflateDictionary h s xs) :
    InflateDictionary (Space.put h dest (copyRange output input oo io n)) s xs := by
  rcases dictionary with empty | ⟨r, off, w, window, getW, fits, content⟩
  · exact Or.inl empty
  · right
    by_cases same : r = dest
    · subst same
      have arrays : w = output := Option.some.inj (getW.symm.trans get)
      subst arrays
      refine ⟨r, off, copyRange w input oo io n, window, byte_view_get_put getW write _,
        by rw [size_copyRange]; exact fits, ?_⟩
      have nextLe : s.wnext.toNat ≤ s.whave.toNat := UInt32.le_iff_toNat_le.mp bounds.1
      have haveLe : s.whave.toNat ≤ s.wsize.toNat := UInt32.le_iff_toNat_le.mp bounds.2
      have diff : (s.whave - s.wnext).toNat = s.whave.toNat - s.wnext.toNat :=
        UInt32.toNat_sub_of_le _ _ bounds.1
      rw [window] at sep
      have cond : n = 0 ∨ s.wsize.toNat = 0 ∨ oo + n ≤ off ∨ off + s.wsize.toNat ≤ oo := by
        rcases sep with zero | zero | sep
        · exact Or.inl zero
        · exact Or.inr (Or.inl zero)
        · simp only at sep
          rcases sep with ne | lt | lt
          · exact absurd rfl ne
          · exact Or.inr (Or.inr (Or.inl lt))
          · exact Or.inr (Or.inr (Or.inr lt))
      rw [content, diff, slice_copy_outside outputFit inputFit (by omega),
        slice_copy_outside outputFit inputFit (by omega)]
    · exact ⟨r, off, w, window, by rw [byte_view_get_put_ne h same]; exact getW, fits, content⟩

/-- Copying right after a written range extends the range by the copied bytes. -/
theorem bytes_extend_copy {h : Heap} {dest : BRef} {output input : Array UInt8} {o0 k io n : Nat}
    {xs : List UInt8} (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (outputFit : o0 + k + n ≤ output.size) (inputFit : io + n ≤ input.size)
    (view : Bytes h (.ref dest o0) k xs) :
    Bytes (Space.put h dest (copyRange output input (o0 + k) io n)) (.ref dest o0) (k + n)
      (xs ++ (input.toList.drop io).take n) := by
  rcases view with ⟨null, _, _⟩ | ⟨r, i, a', ptr, get', fits, rfl⟩
  · cases null
  · obtain ⟨hr, hi⟩ := Ptr.ref.inj ptr
    subst hr hi
    have arrays : a' = output := Option.some.inj (get'.symm.trans get)
    subst arrays
    refine Or.inr ⟨dest, o0, copyRange a' input (o0 + k) io n, rfl, byte_view_get_put get write _,
      by rw [size_copyRange]; omega, ?_⟩
    have m : min k (a'.size - o0) = k := by omega
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_append, Array.getElem?_toList,
      List.length_take, List.length_drop, Array.length_toList, m]
    rw [copyRange_getElem? a' input (o0 + k) io n outputFit inputFit]
    by_cases jk : j < k
    · have c1 : j < k + n := by omega
      have c2 : ¬ (o0 + k ≤ o0 + j ∧ o0 + j < o0 + k + n) := by omega
      simp only [c1, c2, jk, ↓reduceIte]
    · by_cases jn : j < k + n
      · have c2 : o0 + k ≤ o0 + j ∧ o0 + j < o0 + k + n := by omega
        have c3 : j - k < n := by omega
        have e : io + (o0 + j - (o0 + k)) = io + (j - k) := by omega
        simp only [jn, c2, jk, c3, ↓reduceIte, e, and_self]
      · have c3 : ¬ j - k < n := by omega
        simp only [jn, jk, c3, ↓reduceIte]

/-! ## Ranges after `n` bytes of output -/

theorem separate_take {dest : BRef} {off n k : Nat} {q : BPtr} {m : Nat}
    (sep : Separate (.ref dest off) n q m) (le : k ≤ n) : Separate (.ref dest off) k q m := by
  rcases sep with zero | zero | sep
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl zero)
  · right; right
    cases q with
    | null => trivial
    | ref r j =>
        simp only at sep ⊢
        rcases sep with ne | lt | lt
        · exact Or.inl ne
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr lt)

theorem separate_shrink_n {dest : BRef} {off n k : Nat} {q : BPtr} {m : Nat}
    (sep : Separate (.ref dest off) n q m) (le : k ≤ n) :
    Separate (.ref dest (off + k)) (n - k) q m := by
  rcases sep with zero | zero | sep
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl zero)
  · right; right
    cases q with
    | null => trivial
    | ref r j =>
        simp only at sep ⊢
        rcases sep with ne | lt | lt
        · exact Or.inl ne
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))

theorem separate_advance_n {p : BPtr} {n : Nat} {source : BRef} {io m j : Nat}
    (sep : Separate p n (.ref source io) m) (le : j ≤ m) :
    Separate p n (.ref source (io + j)) (m - j) := by
  rcases sep with zero | zero | sep
  · exact Or.inl zero
  · exact Or.inr (Or.inl (by omega))
  · right; right
    cases p with
    | null => trivial
    | ref r i =>
        simp only at sep ⊢
        rcases sep with ne | before | after
        · exact Or.inl ne
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (by omega))

theorem separate_grow_n {dest : BRef} {o0 k left N : Nat} {q : BPtr} {m : Nat}
    (first : Separate (.ref dest o0) k q m) (second : Separate (.ref dest (o0 + k)) left q m)
    (le : N ≤ left) : Separate (.ref dest o0) (k + N) q m := by
  cases q with
  | null => exact Or.inr (Or.inr trivial)
  | ref r j =>
      unfold Separate at first second ⊢
      simp only at first second ⊢
      by_cases same : dest = r
      · subst same
        simp only [ne_eq, not_true_eq_false, false_or] at first second ⊢
        omega
      · exact Or.inr (Or.inr (Or.inl same))

theorem take_after_append (A c d : List UInt8) (p : Nat) (hp : p ≤ c.length) :
    (A ++ (c ++ d)).take ((A ++ (c ++ d)).length - (p + d.length)) =
      (A ++ c).take ((A ++ c).length - p) := by
  rw [← List.append_assoc]
  rw [List.take_append_of_le_length (by simp; omega)]
  congr 1
  simp
  omega

/-! ## Rebuilding the loop meaning -/

/-- The window meaning moves to a heap with the same byte views and a state
with the same window fields. -/
theorem window_transfer {h h' : Heap} {s s' : InflateState} {dict out : List UInt8}
    (wnd : s'.window = s.window) (wsize : s'.wsize = s.wsize) (wnext : s'.wnext = s.wnext)
    (whave : s'.whave = s.whave)
    (gets : ∀ q : BRef, (Space.get h' q : Option (Array UInt8)) = Space.get h q)
    (window : WindowMeaning h s dict out) : WindowMeaning h' s' dict out := by
  rcases window with ⟨nonzero, dictionary⟩ | ⟨z1, z2, z3⟩
  · refine Or.inl ⟨by rw [wsize]; exact nonzero, ?_⟩
    rw [wsize]
    exact dictionary_transfer wnd wsize wnext whave gets dictionary
  · exact Or.inr ⟨by rw [wsize]; exact z1, by rw [whave]; exact z2, z3⟩

/-- The `copy` register is not part of the meaning. -/
theorem loop_copy_reg {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} (x : UInt32)
    (loop : LoopMatches c f h l) : LoopMatches c f h { l with copy := x } := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  exact ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen,
    ⟨binv.have_eq, binv.next, binv.hold_lt⟩, leftLe, pendLe, putEq, outBytes, writable, sepIn,
    sepWin, sepOutIn, bitsEq, ⟨heldBits.1, heldBits.2⟩, parsed, stageM, wrapM, outputEq⟩

/-- A stalled copy of a nonempty stored block has no input or no output room. -/
theorem copyAmt_zero {len have_ left : UInt32} (hnz : len ≠ 0) (hz : copyAmt len have_ left = 0) :
    have_ = 0 ∨ left = 0 := by
  have hl : len.toNat ≠ 0 := fun e => hnz (UInt32.toNat_inj.mp (by simpa using e))
  have e : (copyAmt len have_ left).toNat = 0 := by rw [hz]; rfl
  unfold copyAmt at e
  simp only [gt_iff_lt, UInt32.lt_iff_toNat_lt] at e
  by_cases a : have_.toNat = 0
  · exact Or.inl (UInt32.toNat_inj.mp (by simpa using a))
  · right
    apply UInt32.toNat_inj.mp
    show left.toNat = 0
    split at e <;> split at e <;> omega

/-- The loop meaning after a state update that keeps the byte views and the
registers. -/
theorem loop_update {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s' : InflateState}
    {callOut : List UInt8} {consumed held : List Bool} {stage : WrapStage}
    (st : c.st = some (.tab zs)) (retOk : l.ret = Z_OK)
    (config : ConfigMatches (loopState s' l) f.wrap f.configured)
    (haveLe : l.have_.toNat ≤ l.in_.toNat) (inLen : l.in_.toNat = f.inp.length)
    (binv : BitInv h l (f.inp.drop (loopRead l)))
    (leftLe : l.left.toNat ≤ l.out_.toNat) (pendLe : loopPending l ≤ callOut.length ∧
      ∀ header pos, stage = .body header pos → loopPending l = callOut.length)
    (putEq : l.put = inputAdvance f.start callOut.length)
    (outBytes : Bytes h f.start callOut.length callOut)
    (writable : Writable h l.put l.left.toNat)
    (sepIn : Separate l.put l.left.toNat l.next l.have_.toNat)
    (sepWin : Separate l.put l.left.toNat s'.window s'.wsize.toNat)
    (sepOutIn : Separate f.start callOut.length l.next l.have_.toNat)
    (bitsEq : bytesToBits (f.logIn ++ f.inp.take (loopRead l)) = consumed ++ held)
    (heldBits : HeldBits (loopState s' l) held)
    (parsed : WrapParsed f.wrap f.configured f.dict consumed stage)
    (stageM : LoopStageMatches (setI h zs s') (loopState s' l) f
      ((f.logOut ++ callOut).take ((f.logOut ++ callOut).length - loopPending l)) stage)
    (wrapM : WrapMatches (setI h zs s') (loopState s' l) f.wrap f.configured f.dict stage)
    (outputEq : stage.output = f.logOut ++ callOut) :
    LoopMatches c f (setI h zs s') l := by
  refine ⟨zs, s', callOut, consumed, held, stage, st, setI_istates_same _ _ _, retOk, config, haveLe,
    inLen, bitInv_setI binv, leftLe, pendLe, putEq, bytes_setI outBytes, ?_, sepIn, sepWin, sepOutIn,
    bitsEq, heldBits, parsed, stageM, wrapM, outputEq⟩
  rcases writable with null | ⟨r, i, a, ptr, get, ro, fits⟩
  · exact Or.inl null
  · exact Or.inr ⟨r, i, a, ptr, by rw [byte_view_get_setI]; exact get,
      by rw [byte_view_ro_setI]; exact ro, fits⟩

/-- `case COPY_` sets the mode `COPY`; the meaning is kept. -/
theorem loop_set_copy {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {zs : Nat} {s : InflateState}
    (loop : LoopMatches c f h l) (st : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (mode : s.mode = COPY_) : LoopMatches c f (setI h zs { s with mode := COPY }) l := by
  obtain ⟨zs', s', callOut, consumed, held, stage, st', hs', retOk, config, haveLe, inLen, binv,
    leftLe, pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed,
    stageM, wrapM, outputEq⟩ := loop
  rw [st] at st'
  cases st'
  rw [hs] at hs'
  cases hs'
  obtain ⟨header, out, final, remaining, rfl⟩ := stage_of_copy stageM (Or.inr mode)
  obtain ⟨⟨_, lengthEq, last, bitsZero⟩, window, check⟩ := stageM
  exact loop_update st retOk
    ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show COPY ≠ SYNC by decide⟩
    haveLe inLen binv leftLe pendLe putEq outBytes writable sepIn sepWin sepOutIn bitsEq
    ⟨heldBits.1, heldBits.2⟩ parsed
    ⟨⟨Or.inr rfl, lengthEq, last, bitsZero⟩,
      window_transfer rfl rfl rfl rfl (fun q => byte_view_get_setI h zs _ q) window, check⟩
    wrapM outputEq

/-! ## The step -/

/-- `inflate_COPY_views_run` with the amount named. -/
theorem copy_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (nonempty : s.length ≠ 0) {n : UInt32} (nDef : copyAmt s.length l.have_ l.left = n)
    (positive : n ≠ 0)
    {source dest : BRef} {io oo : Nat} {input output : Array UInt8}
    (next : l.next = .ref source io) (put : l.put = .ref dest oo)
    (inputGet : Space.get h source = some input) (outputGet : Space.get h dest = some output)
    (write : Space.ro h dest = false)
    (inputFit : io + n.toNat ≤ input.size) (outputFit : oo + n.toNat ≤ output.size)
    (separate : dest ≠ source ∨ oo + n.toNat ≤ io ∨ io + n.toNat ≤ oo) :
    runX (inflate_COPY c) l h = .ok ((.ok (),
      copyRegs l n (.ref source (io + n.toNat)) (.ref dest (oo + n.toNat))),
      setI (Space.put h dest (copyRange output input oo io n.toNat)) zs { s with length := s.length - n }) := by
  subst nDef
  exact inflate_COPY_views_run E l nonempty positive next put inputGet outputGet write inputFit
    outputFit separate

set_option maxHeartbeats 2000000 in
/-- `case COPY` keeps the format meaning. With nothing left in the stored
block it goes to `TYPE` and the parse reaches the block boundary (or the end
of the data after the final block). With bytes left but no input or no output
room it leaves, and only the `copy` register changes. Otherwise it copies
`n > 0` bytes: the parse, the input read and the output grow by them. The
safety facts are the stream record (for `Env`) and the window bounds. -/
theorem copy_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (copy : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = COPY)
    (bounds : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) :
    ∃ result l' h', runX (inflate_COPY c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ ((l'.have_ = 0 ∧ LeaveShort c h' l') ∨ l.left = 0) ∧
          LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧ LoopMatches c f h' l')) := by
  have loop0 := loop
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have mode : s.mode = COPY := copy zs s st hs
  obtain ⟨header, out, final, remaining, rfl⟩ := stage_of_copy stageM (Or.inl mode)
  obtain ⟨body, window, check⟩ := stageM
  obtain ⟨modes, lengthEq, last, bitsZero⟩ := body
  have bitsZero' : l.bits = 0 := bitsZero
  have lengthEq' : s.length.toNat = remaining := lengthEq
  have heldNil : held = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [heldBits.1]
    show l.bits.toNat = 0
    rw [bitsZero']
    rfl
  subst heldNil
  obtain ⟨bodyDict, bits, wrapHeader, consumedEq, deflate⟩ := parsed
  by_cases done : s.length = 0
  · -- the end of the stored block
    have rem0 : remaining = 0 := by rw [← lengthEq', done]; rfl
    subst rem0
    refine ⟨_, _, _, inflate_COPY_done E l done, Or.inr ⟨rfl, Nat.le_refl _, ?_⟩⟩
    apply loop_copy_reg
    have gets : ∀ q : BRef, (Space.get (setI h zs { s with mode := TYPE }) q :
        Option (Array UInt8)) = Space.get h q := fun q => byte_view_get_setI h zs _ q
    have bitsLt : (loopState { s with mode := TYPE } l).bits.toNat < 8 := by
      show l.bits.toNat < 8
      rw [bitsZero']
      decide
    have config' : ConfigMatches (loopState { s with mode := TYPE } l) f.wrap f.configured :=
      ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show TYPE ≠ SYNC by decide⟩
    have window' := window_transfer (s' := loopState { s with mode := TYPE } l) rfl rfl rfl rfl gets window
    cases final with
    | false =>
      have last' : (loopState { s with mode := TYPE } l).last = 0 := by
        simpa [loopState] using last
      exact loop_update (stage := .body header ⟨out, false, .boundary⟩) st retOk config' haveLe
        inLen binv leftLe ⟨pendLe.1, fun _ _ _ => pendLe.2 _ _ rfl⟩ putEq outBytes writable sepIn
        sepWin sepOutIn bitsEq
        ⟨heldBits.1, heldBits.2⟩
        ⟨bodyDict, bits, wrapHeader, consumedEq, DeflateParsed.storedEnd deflate⟩
        ⟨⟨Or.inl rfl, rfl, last', bitsLt⟩, window', check⟩ wrapM outputEq
    | true =>
      have last' : (loopState { s with mode := TYPE } l).last = 1 := by
        simpa [loopState] using last
      exact loop_update (stage := .body header ⟨out, true, .finished⟩) st retOk config' haveLe
        inLen binv leftLe ⟨pendLe.1, fun _ _ _ => pendLe.2 _ _ rfl⟩ putEq outBytes writable sepIn
        sepWin sepOutIn bitsEq
        ⟨heldBits.1, heldBits.2⟩
        ⟨bodyDict, bits, wrapHeader, consumedEq, DeflateParsed.storedFinal deflate⟩
        ⟨⟨Or.inl rfl, rfl, last', bitsLt⟩, window', check⟩ wrapM outputEq
  obtain ⟨n, nDef⟩ : ∃ n, copyAmt s.length l.have_ l.left = n := ⟨_, rfl⟩
  obtain ⟨lengthBound, inputBound, outputBound⟩ := copyAmt_le s.length l.have_ l.left
  rw [nDef] at lengthBound inputBound outputBound
  by_cases stall : n = 0
  · exact ⟨_, _, _, inflate_COPY_leave E l done (nDef.trans stall),
      Or.inl ⟨rfl, (copyAmt_zero done (nDef.trans stall)).imp_left
        (fun e => ⟨e, LeaveShort.of_state st hs (Or.inr (Or.inr (Or.inl ⟨mode, done⟩)))⟩),
        loop_copy_reg 0 loop0⟩⟩
  have positive : 0 < n.toNat := by
    have nz : n.toNat ≠ 0 := fun zero => stall (UInt32.toNat_inj.mp (by simpa using zero))
    omega
  rcases writable with ⟨_, zero⟩ | ⟨dest, oo, output, put, outputGet, write, room⟩
  · omega
  have haveEq := binv.have_eq
  obtain ⟨source, input, io, next, inputGet, inputRoom, content⟩ := binv.next.resolve_left (by
    intro empty
    have e : (f.inp.drop (loopRead l)).length = 0 := by rw [empty]; rfl
    omega)
  have inputFit : io + n.toNat ≤ input.size := by omega
  have outputFit : oo + n.toNat ≤ output.size := by omega
  have sepIn0 := sepIn
  rw [put, next] at sepIn0
  have sepFull : dest ≠ source ∨ oo + l.left.toNat ≤ io ∨ io + l.have_.toNat ≤ oo := by
    rcases sepIn0 with zero | zero | sep
    · omega
    · omega
    · exact sep
  have separate : dest ≠ source ∨ oo + n.toNat ≤ io ∨ io + n.toNat ≤ oo := by
    rcases sepFull with ne | before | after
    · exact Or.inl ne
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))
  have run := copy_run E l done nDef stall next put inputGet outputGet write inputFit outputFit separate
  have haveSub : (l.have_ - n).toNat = l.have_.toNat - n.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr inputBound)
  have leftSub : (l.left - n).toNat = l.left.toNat - n.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr outputBound)
  have lengthSub : (s.length - n).toNat = s.length.toNat - n.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr lengthBound)
  have readEq : loopRead (copyRegs l n (.ref source (io + n.toNat)) (.ref dest (oo + n.toNat))) =
      loopRead l + n.toNat := by
    simp only [loopRead, copyRegs, haveSub]
    omega
  have pendEq : loopPending (copyRegs l n (.ref source (io + n.toNat)) (.ref dest (oo + n.toNat))) =
      loopPending l + n.toNat := by
    simp only [loopPending, copyRegs, leftSub]
    omega
  refine ⟨_, _, _, run, Or.inr ⟨rfl, by rw [readEq]; omega, ?_⟩⟩
  have copiedLen : ((f.inp.drop (loopRead l)).take n.toNat).length = n.toNat := by
    rw [List.length_take]
    omega
  have copiedEq : (input.toList.drop io).take n.toNat = (f.inp.drop (loopRead l)).take n.toNat := by
    conv => rhs; rw [content]
    rw [List.take_take]
    congr 1
    omega
  -- the output start is in the written array
  obtain ⟨o0, startEq, offEq⟩ : ∃ o0, f.start = .ref dest o0 ∧ oo = o0 + callOut.length := by
    rw [put] at putEq
    cases hst : f.start with
    | null => rw [hst] at putEq; simp [inputAdvance] at putEq
    | ref d o =>
        rw [hst] at putEq
        simp only [inputAdvance, Ptr.ref.injEq] at putEq
        obtain ⟨rfl, rfl⟩ := putEq
        exact ⟨o, rfl, rfl⟩
  have sepWin0 := sepWin
  rw [put] at sepWin0
  have sepOutIn0 := sepOutIn
  rw [startEq, next] at sepOutIn0
  let s' : InflateState := { s with length := s.length - n }
  let h1 := Space.put h dest (copyRange output input oo io n.toNat)
  have gets : ∀ q : BRef, (Space.get (setI h1 zs s') q : Option (Array UInt8)) = Space.get h1 q :=
    fun q => byte_view_get_setI h1 zs s' q
  refine ⟨zs, s', callOut ++ (f.inp.drop (loopRead l)).take n.toNat,
    consumed ++ bytesToBits ((f.inp.drop (loopRead l)).take n.toNat), [],
    .body header ⟨out ++ (f.inp.drop (loopRead l)).take n.toNat, final, .stored (remaining - n.toNat)⟩,
    st, setI_istates_same _ _ _, retOk,
    ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, config.2.2.2.2.2⟩,
    ?_, inLen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨heldBits.1, heldBits.2⟩, ?_, ?_, wrapM, ?_⟩
  · -- have ≤ in
    show (l.have_ - n).toNat ≤ l.in_.toNat
    rw [haveSub]
    omega
  · -- the unread input
    have positions : f.inp.drop (loopRead l) = [] ∨ ∀ i, l.next = .ref dest i →
        i + (f.inp.drop (loopRead l)).length ≤ oo ∨ oo + n.toNat ≤ i := by
      right
      intro i ptr
      rw [next] at ptr
      obtain ⟨same, rfl⟩ := Ptr.ref.inj ptr
      rcases sepFull with ne | before | after
      · exact absurd same.symm ne
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have copied := binv.stored_copy (input := input) (io := io) (oo := oo) (n := n.toNat)
      outputGet write inputFit outputFit positions
    have advanced := copied.advance_bytes (used := n.toNat)
      (regs := copyRegs l n (.ref source (io + n.toNat)) (.ref dest (oo + n.toNat)))
      (by omega) (by rw [next]; rfl)
      (by show (l.have_ - n).toNat + n.toNat = l.have_.toNat; rw [haveSub]; omega) rfl rfl
    rw [readEq, ← List.drop_drop]
    exact bitInv_setI advanced
  · -- left ≤ out
    show (l.left - n).toNat ≤ l.out_.toNat
    rw [leftSub]
    omega
  · -- the pending count
    have pendBase := pendLe.2 _ _ rfl
    refine ⟨?_, fun _ _ _ => ?_⟩
    · rw [pendEq, List.length_append, copiedLen]
      omega
    · rw [pendEq, List.length_append, copiedLen, pendBase]
  · -- the output cursor
    show Ptr.ref dest (oo + n.toNat) = _
    rw [List.length_append, copiedLen, startEq, offEq]
    simp only [inputAdvance, Nat.add_assoc]
  · -- the call's output
    rw [List.length_append, copiedLen, ← copiedEq, startEq]
    apply bytes_setI
    rw [startEq] at outBytes
    have ext := bytes_extend_copy (o0 := o0) (k := callOut.length) (io := io) (n := n.toNat)
      (input := input) outputGet write (by omega) inputFit outBytes
    rw [← offEq] at ext
    exact ext
  · -- the output room
    refine Or.inr ⟨dest, oo + n.toNat, copyRange output input oo io n.toNat, rfl, ?_, ?_, ?_⟩
    · rw [gets]; exact byte_view_get_put outputGet write _
    · rw [byte_view_ro_setI, byte_view_ro_put]; exact write
    · show oo + n.toNat + (l.left - n).toNat ≤ (copyRange output input oo io n.toNat).size
      rw [size_copyRange, leftSub]
      omega
  · -- the room is separate from the unread input
    show Separate (.ref dest (oo + n.toNat)) (l.left - n).toNat (.ref source (io + n.toNat))
      (l.have_ - n).toNat
    rw [leftSub, haveSub]
    exact separate_advance_n (separate_shrink_n sepIn0 outputBound) inputBound
  · -- the room is separate from the window
    show Separate (.ref dest (oo + n.toNat)) (l.left - n).toNat s.window s.wsize.toNat
    rw [leftSub]
    exact separate_shrink_n sepWin0 outputBound
  · -- the call's output is separate from the unread input
    rw [List.length_append, copiedLen, startEq]
    show Separate (.ref dest o0) (callOut.length + n.toNat) (.ref source (io + n.toNat))
      (l.have_ - n).toNat
    rw [haveSub]
    have sepIn1 := sepIn0
    rw [offEq] at sepIn1
    exact separate_advance_n (separate_grow_n sepOutIn0 sepIn1 outputBound) inputBound
  · -- the consumed bits
    rw [readEq, List.take_add, ← List.append_assoc, bytesToBits_app, bitsEq]
    simp
  · -- the parse
    refine ⟨bodyDict, bits ++ bytesToBits ((f.inp.drop (loopRead l)).take n.toNat), wrapHeader,
      by rw [consumedEq, List.append_assoc], ?_⟩
    have p := parsed_stored_bytes ((f.inp.drop (loopRead l)).take n.toNat) deflate
      (by rw [copiedLen]; omega)
    rw [copiedLen] at p
    exact p
  · -- stage facts
    refine ⟨⟨modes, ?_, last, bitsZero⟩, ?_, ?_⟩
    · show (s.length - n).toNat = remaining - n.toNat
      rw [lengthSub, lengthEq']
    · rcases window with ⟨nonzero, dictionary⟩ | empty
      · have sepW : Separate (.ref dest oo) n.toNat s.window s.wsize.toNat :=
          separate_take sepWin0 outputBound
        have stored := dictionary_after_copy (s := loopState s l) outputGet write outputFit inputFit
          (bounds zs s st hs) sepW dictionary
        exact Or.inl ⟨nonzero, dictionary_transfer rfl rfl rfl rfl gets stored⟩
      · exact Or.inr empty
    · rw [pendEq, show loopPending l + n.toNat =
        loopPending l + ((f.inp.drop (loopRead l)).take n.toNat).length by rw [copiedLen],
        take_after_append _ _ _ _ pendLe.1]
      exact check
  · simp only [WrapStage.output] at outputEq ⊢
    rw [outputEq, List.append_assoc]

/-- `case COPY_` keeps the format meaning: it sets the mode `COPY` and runs
`case COPY` (`copy_step`). -/
theorem copy_start_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (copyStart : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = COPY_)
    (bounds : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize) :
    ∃ result l' h', runX (inflate_COPY_ c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ ((l'.have_ = 0 ∧ LeaveShort c h' l') ∨ l.left = 0) ∧
          LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧ LoopMatches c f h' l')) := by
  obtain ⟨zs, s, st, hs⟩ : ∃ zs s, c.st = some (.tab zs) ∧ h.istates zs = some s := by
    obtain ⟨zs, s, _, _, _, _, st, hs, _⟩ := loop
    exact ⟨zs, s, st, hs⟩
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have moved := loop_set_copy loop st hs (copyStart zs s st hs)
  have hz0 : r.get (setI h zs { s with mode := COPY }) = some z := by simpa using hz
  have same : ∀ zs' s', c.st = some (.tab zs') →
      (setI h zs { s with mode := COPY }).istates zs' = some s' → s' = { s with mode := COPY } := by
    intro zs' s' st' hs'
    rw [st] at st'
    cases st'
    rw [setI_istates_same] at hs'
    cases hs'
    rfl
  obtain ⟨result, l', h', run, rest⟩ := copy_step moved strm hz0
    (fun zs' s' st' hs' => by rw [same zs' s' st' hs'])
    (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact bounds zs s st hs)
  exact ⟨result, l', h', (inflate_COPY__eq E l).trans run, rest⟩

end Zlib.Inflate.Proofs.MeaningCopy
