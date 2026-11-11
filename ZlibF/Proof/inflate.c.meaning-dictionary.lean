import ZlibF.Proof.«inflate.c.meaning-rebuffer»
import ZlibF.Proof.«inflate.c.dictionary-invariant»
import ZlibF.Proof.«public-inflate-setdict»
import ZlibF.Proof.«inflate.c.caller-buffers»

/-!
# inflate.c: `inflateSetDictionary` keeps the format meaning

`setDictionary_cases` splits an actual call over the general invariant into
its three outcomes: a refusal or identifier mismatch that changes nothing, an
allocation failure that enters `MEM`, and a success that changes only the
window fields and `havedict`, with the window holding the last window of the
old window followed by the dictionary (the registered
`Goal.inflateSetDictionary`). No object-size premise is used (the copy of the
invariant argument of `inflateSetDictionary_preserves` without it, as agreed
with the inflate owner).
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The three outcomes of an actual `inflateSetDictionary` on a state with the
general invariant. -/
theorem setDictionary_cases {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {source : BPtr} {len : UInt32} {xs : List UInt8} {rc : Int32}
    (current : InflateInv h r zs z s)
    (range : StreamArguments h r (.inflateSetDictionary (some r) source len))
    (read : Bytes h source len.toNat xs)
    (run : C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after)) :
    (after = h ∧ rc ≠ Z_OK ∧ rc ≠ Z_MEM_ERROR) ∨
    (rc = Z_MEM_ERROR ∧ InflateInv after r zs z { s with mode := MEM }) ∨
    (rc = Z_OK ∧ (s.wrap = 0 ∨ s.mode = DICT) ∧
      (s.mode = DICT → (ZlibF.Spec.adler32 xs).toUInt64 = s.check) ∧
      ∃ state, WindowStateFrame s state ∧ InflateInv after r zs z { state with havedict := 1 } ∧
        (∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) ∧
        ∀ old, InflateDictionary h s old →
          InflateDictionary after { state with havedict := 1 }
            ((old ++ xs).drop ((old ++ xs).length - 2 ^ s.wbits.toNat))) := by
  by_cases refused : source = .null ∨ (s.wrap ≠ 0 ∧ s.mode ≠ DICT)
  · have actual := inflateSetDictionary_refused_any current.good.live source len refused
    rw [run] at actual
    cases actual
    exact Or.inl ⟨rfl, by decide, by decide⟩
  have nonnull : source ≠ .null := fun null => refused (Or.inl null)
  have allowed : s.wrap = 0 ∨ s.mode = DICT := by
    by_cases raw : s.wrap = 0
    · exact Or.inl raw
    · right
      apply Classical.byContradiction
      intro wrong
      exact refused (Or.inr ⟨raw, wrong⟩)
  have nonzero : s.wbits ≠ 0 := by
    rcases allowed with raw | dict
    · exact current.config.raw raw
    · intro zero
      rcases current.config.window with ⟨low, _⟩ | ⟨_, _, early⟩
      · rw [zero] at low
        exact absurd low (by decide)
      · rw [dict] at early
        rcases early with e | e | e <;> exact absurd e (by decide)
  obtain null | ⟨ref, off, array, pointer, get, room, values⟩ := read
  · exact False.elim (nonnull null.1)
  subst pointer
  by_cases mismatch : s.mode = DICT ∧
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 ≠ s.check
  · have actual := inflateSetDictionary_dataerr_any current.good.live get room mismatch.1 mismatch.2
    rw [run] at actual
    cases actual
    exact Or.inl ⟨rfl, by decide, by decide⟩
  have checked : s.mode = DICT →
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 = s.check := by
    intro dict
    apply Classical.byContradiction
    intro wrong
    exact mismatch ⟨dict, wrong⟩
  have unowned := callerRange_private_window current.good range rfl
  have separate : Separate (.ref ref off) len.toNat s.window (2 ^ s.wbits.toNat) := by
    rcases current.good.inv.win.block with null | ⟨w, bytes, window, _⟩
    · simp [Separate, null]
    · simp [Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, _sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary current.good current.alloc.1 get
      (by omega : len.toNat ≤ off + len.toNat) room unowned
  have static := updatewindow_static current.good current.alloc.1 get
    (by omega : len.toNat ≤ off + len.toNat) room
    (by simpa only [Nat.add_sub_cancel] using separate) windowRun
  have next := current.window_update good1 windowFrame codeViews static current.alloc nonzero
  have cut := inflateSetDictionary_window_cut current.good.live get room allowed checked windowRun
    good1.live.hs
  have xsEq : xs = Zlib.Adler32.Proofs.seg array off len.toNat := by
    rw [values]
    apply List.ext_getElem
    · simp [Zlib.Adler32.Proofs.seg]
      omega
    · intro i inside _
      simp only [List.length_take, List.length_drop, Array.length_toList] at inside
      simp [Zlib.Adler32.Proofs.seg, getElem!_pos array (off + i) (by omega)]
  rcases outcome with success | failure
  · subst wr
    simp only [ite_true] at cut
    rw [run] at cut
    cases cut
    right; right
    refine ⟨rfl, allowed, fun dict => by rw [xsEq]; exact checked dict, state1, windowFrame,
      next.set_havedict, ?_, ?_⟩
    · intro cref
      rw [← codeViews cref]
      cases cref with
      | istate_codes i =>
        by_cases same : i = zs
        · subst same
          simp [Space.get, setI, good1.live.hs]
        · simp [Space.get, setI, upd, Tbl.get_set, same]
      | st_lenfix => rfl
      | st_distfix => rfl
    · intro old oldView
      obtain ⟨rc', after', run', _, outcomes, _, _⟩ :=
        ZlibF.Spec.Public.Proofs.inflateSetDictionary_public h r zs z s (.ref ref off) len xs old
          current.good current.alloc.1 oldView
          (fun _ => Or.inr ⟨ref, off, array, rfl, get, room, values⟩) separate
          (fun _ => by
            rcases current.config.window with ⟨low, _⟩ | ⟨zero, _⟩
            · exact low
            · exact absurd zero nonzero)
      rw [run] at run'
      cases run'
      have chosen := outcomes (by simp) allowed
      have notMismatch : ¬ (s.mode = DICT ∧ s.check ≠ (ZlibF.Spec.adler32 xs).toUInt64) := by
        rintro ⟨dict, wrong⟩
        exact wrong (by rw [xsEq]; exact (checked dict).symm)
      simp only [notMismatch, ite_false] at chosen
      rcases chosen with ⟨bad, _⟩ | ⟨_, s', good', _, _, dictionary⟩
      · exact absurd bad (by decide)
      · have same : s' = { state1 with havedict := 1 } :=
          Option.some.inj (good'.live.hs.symm.trans (by simp [setI]))
        rw [← same]
        exact dictionary
  · obtain ⟨code, _window, sameState, _heap⟩ := failure
    subst wr
    subst state1
    simp only [show ¬ ((1 : Int32) = 0) from by decide, ite_false] at cut
    rw [run] at cut
    cases cut
    have good : Good (setI heap1 zs { s with mode := MEM }) r zs z { s with mode := MEM } :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    exact Or.inr (Or.inl ⟨rfl, next.mem_update good rfl current.alloc nonzero⟩)

#print axioms setDictionary_cases

/-! ## Facts for an epoch with no input yet -/

/-- An empty final stored block decodes to nothing with any dictionary. -/
theorem empty_stored_decodes (dict : List UInt8) :
    ZlibF.Spec.Deflate.Decodes dict [0x01, 0x00, 0x00, 0xFF, 0xFF] [] :=
  ⟨_, .last rfl rfl (.stored rfl rfl rfl rfl), by decide +kernel⟩

/-- No bits decode to no stream. -/
theorem not_decodes_nil (dict out : List UInt8) : ¬ ZlibF.Spec.Deflate.Decodes dict [] out := by
  rintro ⟨rest, blocks, _⟩
  cases blocks with
  | last one _ _ => simp [ZlibF.Spec.bytesToBits, ZlibF.Spec.readBits] at one
  | more one _ _ _ => simp [ZlibF.Spec.bytesToBits, ZlibF.Spec.readBits] at one

/-- On no bits the deflate grammar is at its start. -/
theorem deflateParsed_nil {dict : List UInt8} {bits : List Bool} {pos : DeflatePos}
    (parsed : DeflateParsed dict bits pos) : bits = [] → pos = ⟨[], false, .boundary⟩ := by
  induction parsed with
  | start => intro _; rfl
  | storedStart => intro empty; simp at empty
  | storedPad _ _ ih =>
    intro empty
    exact absurd (ih (List.append_eq_nil_iff.mp empty).1) (by simp)
  | storedLength _ _ _ ih =>
    intro empty
    simp [natToBitsLSB] at empty
  | storedByte _ _ ih =>
    intro empty
    exact absurd (ih (List.append_eq_nil_iff.mp empty).1) (by simp)
  | storedEnd _ ih => intro empty; exact absurd (ih empty) (by simp)
  | storedFinal _ ih => intro empty; exact absurd (ih empty) (by simp)
  | fixedHeader => intro empty; simp at empty
  | dynamicStart => intro empty; simp at empty
  | dynamicBits _ _ ih =>
    intro empty
    exact absurd (ih (List.append_eq_nil_iff.mp empty).1) (by simp)
  | dynamicDone _ _ ih => intro empty; exact absurd (ih empty) (by simp)
  | token _ _ ih =>
    intro empty
    exact absurd (ih (List.append_eq_nil_iff.mp empty).1) (by simp)
  | endOfBlock _ _ ih =>
    intro empty
    exact absurd (ih (List.append_eq_nil_iff.mp empty).1) (by simp)
  | endOfFinal _ _ ih =>
    intro empty
    exact absurd (ih (List.append_eq_nil_iff.mp empty).1) (by simp)
  | partialToken _ _ _ ih =>
    intro empty
    exact absurd (ih (List.append_eq_nil_iff.mp empty).1) (by simp)
  | partialCopy _ _ _ _ _ _ _ ih =>
    intro empty
    exact absurd (ih (List.append_eq_nil_iff.mp empty).1) (by simp)
  | partialLiteral _ _ ih =>
    intro empty
    exact absurd (ih (List.append_eq_nil_iff.mp empty).1) (by simp)

/-- Keeping the last `W` bytes, then appending and keeping the last `W` again,
is keeping the last `W` of the whole. -/
theorem drop_window_append (d xs : List UInt8) (W : Nat) :
    (d.drop (d.length - W) ++ xs).drop ((d.drop (d.length - W) ++ xs).length - W) =
      (d ++ xs).drop ((d ++ xs).length - W) := by
  by_cases small : d.length ≤ W
  · rw [show d.length - W = 0 by omega, List.drop_zero]
  · have split : d ++ xs = d.take (d.length - W) ++ (d.drop (d.length - W) ++ xs) := by
      rw [← List.append_assoc, List.take_append_drop]
    have idx : (d ++ xs).length - W = (d.take (d.length - W)).length +
        ((d.drop (d.length - W) ++ xs).length - W) := by
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    symm
    calc (d ++ xs).drop ((d ++ xs).length - W)
        = (d.take (d.length - W) ++ (d.drop (d.length - W) ++ xs)).drop
            ((d.take (d.length - W)).length + ((d.drop (d.length - W) ++ xs).length - W)) := by
          rw [← idx, ← split]
      _ = _ := List.drop_length_add_append _

#print axioms empty_stored_decodes
#print axioms deflateParsed_nil
#print axioms drop_window_append

end Zlib.Inflate.Proofs
