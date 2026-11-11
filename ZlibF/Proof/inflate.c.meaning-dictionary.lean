import ZlibF.Proof.«inflate.c.meaning-rebuffer»
import ZlibF.Proof.«inflate.c.meaning-format»
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
    (rc = Z_MEM_ERROR ∧ (s.wrap = 0 ∨ s.mode = DICT) ∧ InflateInv after r zs z { s with mode := MEM }) ∨
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
    exact Or.inr (Or.inl ⟨rfl, allowed, next.mem_update good rfl current.alloc nonzero⟩)

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

/-- The window after a dictionary installation holds the last window of the
old dictionary followed by the new bytes. -/
theorem window_after_dictionary {h after : Heap} {s t : InflateState} {dict bytes : List UInt8}
    (old : WindowMeaning h s dict []) (oldWin : WinInv h s) (newWin : WinInv after t)
    (wbitsEq : t.wbits = s.wbits)
    (install : ∀ o, InflateDictionary h s o →
      InflateDictionary after t ((o ++ bytes).drop ((o ++ bytes).length - 2 ^ s.wbits.toNat))) :
    WindowMeaning after t (dict ++ bytes) [] := by
  have pos : 0 < 2 ^ s.wbits.toNat := Nat.two_pow_pos _
  have viewed : InflateDictionary after t
      ((dict ++ bytes).drop ((dict ++ bytes).length - 2 ^ s.wbits.toNat)) := by
    rcases old with ⟨nonzero, dictionary⟩ | ⟨_, whave, empty⟩
    · have size : s.wsize.toNat = 2 ^ s.wbits.toNat := by
        rcases oldWin.ws with zero | full
        · exact absurd (UInt32.toNat_inj.mp (by simpa using zero)) nonzero
        · exact full
      have := install _ dictionary
      simp only [List.append_nil, size] at this
      rwa [drop_window_append] at this
    · simp only [List.append_nil] at empty
      subst empty
      have := install [] (Or.inl ⟨whave, rfl⟩)
      simpa using this
  rcases newWin.ws with zero | full
  · right
    have wsizeZero : t.wsize = 0 := UInt32.toNat_inj.mp (by simpa using zero)
    have whaveZero : t.whave.toNat = 0 := by have := newWin.hv; omega
    have wnextZero : t.wnext.toNat = 0 := by
      rcases newWin.wn with lt | ⟨_, z⟩
      · omega
      · exact z
    refine ⟨wsizeZero, UInt32.toNat_inj.mp (by simpa using whaveZero), ?_⟩
    have emptyView : (dict ++ bytes).drop ((dict ++ bytes).length - 2 ^ s.wbits.toNat) = [] := by
      rcases viewed with ⟨_, e⟩ | ⟨_, _, _, _, _, _, e⟩
      · exact e
      · have hw : t.whave = 0 := UInt32.toNat_inj.mp (by simpa using whaveZero)
        have hn : t.wnext = 0 := UInt32.toNat_inj.mp (by simpa using wnextZero)
        rw [e, hw, hn]
        simp
    have := congrArg List.length emptyView
    simp only [List.length_drop, List.length_nil] at this
    simp only [List.append_nil]
    exact List.eq_nil_of_length_eq_zero (by omega)
  · left
    refine ⟨fun zero => by
      have := Nat.two_pow_pos t.wbits.toNat
      rw [zero] at full
      simp at full
      omega, ?_⟩
    rw [full, wbitsEq]
    simpa using viewed

/-- A raw configuration is exactly a negative windowBits. -/
theorem inflWbits_raw_iff {w : Int} {wrap : ZlibF.Spec.Api.Wrap} {bits : Nat}
    (selected : ZlibF.Spec.Api.inflWbits w = some (wrap, bits)) : w < 0 ↔ wrap = .raw := by
  unfold ZlibF.Spec.Api.inflWbits at selected
  by_cases negative : w < 0
  · simp only [negative, ite_true] at selected
    split at selected
    · cases selected
    · split at selected
      · cases selected
      · cases selected
        exact ⟨fun _ => rfl, fun _ => negative⟩
  · simp only [negative, ite_false] at selected
    refine ⟨fun n => absurd n negative, fun raw => ?_⟩
    subst raw
    exfalso
    generalize hsel : (if w / 16 = 0 then some ZlibF.Spec.Api.Wrap.zlib
      else if w / 16 = 1 then some ZlibF.Spec.Api.Wrap.gzip
      else if w / 16 = 2 then some ZlibF.Spec.Api.Wrap.auto else none) = chosen at selected
    have notRaw : chosen ≠ some ZlibF.Spec.Api.Wrap.raw := by
      rw [← hsel]
      split
      · simp
      · split
        · simp
        · split <;> simp
    cases chosen with
    | none => simp at selected
    | some wr =>
      simp only at selected
      split at selected <;> simp_all

#print axioms window_after_dictionary

/-- The DICTID that `check` holds is the big-endian Adler-32 the dictionary
must have. -/
theorem dictId_be32 {a b c d e f : UInt8} {v : UInt32}
    (eq : dictId [a, b, c, d, e, f] = v.toUInt64) : ZlibF.Spec.be32 v.toNat = [c, d, e, f] := by
  have nat := congrArg UInt64.toNat eq
  simp only [dictId, List.getD_cons_succ, List.getD_cons_zero, UInt32.toNat_toUInt64,
    UInt64.toNat_ofNat] at nat
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have he := e.toNat_lt
  have hf := f.toNat_lt
  have hv : v.toNat = c.toNat * 2 ^ 24 + d.toNat * 2 ^ 16 + e.toNat * 2 ^ 8 + f.toNat := by
    rw [← nat]
    simp only [UInt64.toNat_ofNat']
    omega
  simp only [ZlibF.Spec.be32, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> simp [hv] <;> omega

theorem wrapCode_zero {wrap : ZlibF.Spec.Api.Wrap} (zero : wrapCode wrap = 0) : wrap = .raw := by
  cases wrap <;> first | rfl | exact absurd zero (by decide)

/-- `int inflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`
keeps the format meaning (statement as on `skeleton/inflate`). -/
theorem meaning_dictionary {h after : Heap} {r : ZStreamRef} {wb : Int32} {log : ZlibF.Spec.Public.DataLog}
    {pending : Bool} {p : BPtr} {n : UInt32} {bytes : List UInt8} {rc : Int32}
    (current : ParseMeaning wb r h log pending)
    (arguments : StreamArguments h r (.inflateSetDictionary (some r) p n))
    (read : Bytes h p n.toNat bytes)
    (run : C.run (inflateSetDictionary (some r) p n) h = .ok (rc, after))
    (admitted : wb.toInt < 0 ∨ rc ≠ Z_OK ∨ pending = true) :
    ParseMeaning wb r after
      { log with
        dictionary := if rc = Z_OK then
          if wb.toInt < 0 then log.dictionary ++ bytes else bytes else log.dictionary
        singleDictionary := log.singleDictionary &&
          !(rc = Z_OK && wb.toInt < 0 && (log.input != [] || log.output != [])) }
      (if wb.toInt < 0 then pending else if rc = Z_OK then false else pending) := by
  have saved := current
  obtain ⟨wrap, configured, i, z, s, params, inv, config, dataError, ended, bad, memory,
    stageClause⟩ := current
  rcases setDictionary_cases inv arguments read run with ⟨rfl, notOk, _⟩ |
    ⟨rfl, allowed, invMem⟩ | ⟨rfl, allowed, checked, state, frame, inv', codes, window⟩
  · cases log
    simpa [notOk] using saved
  · have notOk : (Z_MEM_ERROR : Int32) ≠ Z_OK := by decide
    have kept : ParseMeaning wb r after log pending := by
      refine ⟨wrap, configured, i, z, { s with mode := MEM }, params, invMem, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · obtain ⟨a, b, c, d, e, _⟩ := config
        exact ⟨a, b, c, d, e, show MEM ≠ SYNC by decide⟩
      · intro error
        right
        refine ⟨rfl, ?_⟩
        rcases dataError error with isBad | ⟨_, raw⟩
        · rcases allowed with zero | dict
          · exact wrapCode_zero (config.1.symm.trans zero)
          · rw [isBad] at dict
            exact absurd dict (by decide)
        · exact raw
      · intro _
        exact Or.inr rfl
      · intro _ isBad
        exact absurd isBad (show MEM ≠ BAD by decide)
      · intro single _
        exact ⟨fun finished => meaning_accepted params saved single finished,
          fun source decoded valid full started => meaning_prefix params saved valid single full started⟩
      · intro _ _ notMem
        exact absurd rfl notMem
    cases log
    simpa [notOk] using kept
  · -- success: only the window fields and `havedict` change
    let t : InflateState :=
      { s with window := state.window, wsize := state.wsize, whave := state.whave,
               wnext := state.wnext, havedict := 1 }
    have tEq : { state with havedict := 1 } = t := by
      show { state with havedict := 1 } =
        { s with window := state.window, wsize := state.wsize, whave := state.whave,
                 wnext := state.wnext, havedict := 1 }
      rw [frame]
    rw [tEq] at inv'
    have install : ∀ o, InflateDictionary h s o →
        InflateDictionary after t ((o ++ bytes).drop ((o ++ bytes).length - 2 ^ s.wbits.toNat)) := by
      intro o view
      have := window o view
      rwa [tEq] at this
    by_cases neg : wb.toInt < 0
    · have raw : wrap = .raw := (inflWbits_raw_iff params).mp neg
      subst raw
      simp only [ite_true, neg, decide_true, Bool.true_and]
      refine ⟨.raw, configured, i, z, t, params, inv', config, dataError, ended, ?_, ?_, ?_⟩
      · intro single' isBad source decoded _ full _
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, bne_eq_false_iff_eq]
          at single'
        obtain ⟨single, inEmpty, _⟩ := single'
        exact bad single isBad [0x01, 0x00, 0x00, 0xFF, 0xFF] [] (empty_stored_decodes _) full
          (by rw [inEmpty]; exact List.nil_prefix)
      · intro single' isMem
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, bne_eq_false_iff_eq]
          at single'
        obtain ⟨single, inEmpty, outEmpty⟩ := single'
        have old := memory single isMem
        have notEnded : log.result ≠ Z_STREAM_END := by
          intro finished
          have accepted := old.1 finished
          rw [inEmpty] at accepted
          exact not_decodes_nil _ _ accepted
        refine ⟨fun finished => absurd finished notEnded, fun source decoded _ full _ => ?_⟩
        refine ⟨by rw [outEmpty]; exact List.nil_prefix, fun error => ?_,
          fun finished => absurd finished notEnded⟩
        exact (old.2 [0x01, 0x00, 0x00, 0xFF, 0xFF] [] (empty_stored_decodes _) full
          (by rw [inEmpty]; exact List.nil_prefix)).2.1 error
      · intro single' notBad notMem notSync
        simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff, bne_eq_false_iff_eq]
          at single'
        obtain ⟨single, inEmpty, outEmpty⟩ := single'
        obtain ⟨consumed, held, stage, inputBits, heldBits, parsed, stageM, wrapM, outputEq,
          request⟩ := stageClause single notBad notMem notSync
        rw [inEmpty] at inputBits
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp (by simpa [ZlibF.Spec.bytesToBits] using inputBits.symm)
        have notNeed : ¬ pending = true := by
          intro yes
          obtain ⟨_, eq, _⟩ := request.mp yes
          subst eq
          exact absurd parsed.2.1 (by simp)
        have request' : pending = true ↔ ∃ header, stage = .needDict header ∧ t.havedict = 0 :=
          ⟨fun yes => absurd yes notNeed, fun ⟨_, _, one⟩ => absurd one (show ¬ (1 : Int32) = 0 by decide)⟩
        cases stage with
        | header bytes0 =>
          obtain ⟨consumedEq, _⟩ := parsed
          have empty0 : bytes0 = [] := by
            have := congrArg List.length consumedEq
            rw [bytesToBits_length'] at this
            exact List.eq_nil_of_length_eq_zero (by simp at this; omega)
          subst empty0
          obtain ⟨⟨h1, h2, h3, h4, h5, _, h7⟩, windowM, _⟩ := wrapM
          have headerM : HeaderMatches t .raw configured [] := ⟨h1, h2, h3, h4, h5, fun ne => absurd rfl ne, h7⟩
          exact ⟨[], [], .header [], by simp [inEmpty, ZlibF.Spec.bytesToBits], heldBits,
            ⟨rfl, [], _, ⟨rfl, rfl⟩, Or.inr rfl⟩, stageM,
            ⟨headerM, window_after_dictionary windowM inv.good.inv.win inv'.good.inv.win rfl install,
              Or.inr rfl⟩,
            outputEq, request'⟩
        | needDict header => exact absurd parsed.2.1 (by simp)
        | body header pos =>
          obtain ⟨bodyDict, bits, ⟨rfl, _⟩, consumedEq, dparsed⟩ := parsed
          have bitsNil : bits = [] := by simpa [ZlibF.Spec.bytesToBits] using consumedEq.symm
          subst bitsNil
          have posEq := deflateParsed_nil dparsed rfl
          subst posEq
          obtain ⟨body, windowM, check⟩ := stageM
          exact ⟨[], [], .body [] ⟨[], false, .boundary⟩, by simp [inEmpty, ZlibF.Spec.bytesToBits],
            heldBits,
            ⟨_, [], ⟨rfl, rfl⟩, by simp [ZlibF.Spec.bytesToBits], .start⟩,
            ⟨body, window_after_dictionary windowM inv.good.inv.win inv'.good.inv.win rfl install,
              check⟩, ⟨wrapM.1, wrapM.2.1, Or.inr (Or.inl rfl)⟩, outputEq, request'⟩
        | trailer header out bytes0 =>
          obtain ⟨_, _, _, _, _, wrapped, _⟩ := parsed
          exact absurd rfl wrapped
        | done out =>
          obtain ⟨header, bodyDict, bits, pad, _, dparsed, _, consumedEq⟩ := parsed
          have bitsNil : bits = [] := by
            have := congrArg List.length consumedEq
            simp only [List.length_append, List.length_nil] at this
            exact List.eq_nil_of_length_eq_zero (by omega)
          subst bitsNil
          exact absurd (deflateParsed_nil dparsed rfl) (by simp)
    · have wrapped : wrap ≠ .raw := fun raw => neg ((inflWbits_raw_iff params).mpr raw)
      have dict : s.mode = DICT := by
        rcases allowed with zero | dict
        · exact absurd (wrapCode_zero (config.1.symm.trans zero)) wrapped
        · exact dict
      have pendingTrue : pending = true := by
        rcases admitted with n | notOk | yes
        · exact absurd n neg
        · exact absurd rfl notOk
        · exact yes
      simp only [ite_true, neg, ite_false, decide_true, decide_false, Bool.false_and,
        Bool.and_false, Bool.not_false, Bool.and_true]
      refine ⟨wrap, configured, i, z, t, params, inv', config, ?_, ?_, ?_, ?_, ?_⟩
      · intro error
        exfalso
        rcases dataError error with isBad | ⟨isMem, _⟩
        · rw [dict] at isBad; exact absurd isBad (by decide)
        · rw [dict] at isMem; exact absurd isMem (by decide)
      · intro finished
        exfalso
        rcases ended finished with isDone | isMem
        · rw [dict] at isDone; exact absurd isDone (by decide)
        · rw [dict] at isMem; exact absurd isMem (by decide)
      · intro _ isBad
        exact absurd (dict.symm.trans isBad) (by decide)
      · intro _ isMem
        exact absurd (dict.symm.trans isMem) (by decide)
      · intro single _ _ _
        obtain ⟨consumed, held, stage, inputBits, heldBits, parsed, stageM, wrapM, outputEq,
          request⟩ := stageClause single (by rw [dict]; decide) (by rw [dict]; decide)
            (by rw [dict]; decide)
        obtain ⟨header, rfl, noDict⟩ := request.mp pendingTrue
        obtain ⟨check, flags, bits0, width, empty, _⟩ := wrapM
        obtain ⟨wsizeZero, whaveZero⟩ := empty noDict
        have parsed' := parsed
        obtain ⟨_, _, cmf, flg, dictid, rfl, idLength, _, _, _⟩ := parsed'
        match dictid, idLength with
        | [c, d, e, f], _ =>
          have idEq : ZlibF.Spec.be32 (ZlibF.Spec.adler32 bytes).toNat = [c, d, e, f] :=
            dictId_be32 (check.symm.trans (checked dict).symm)
          have windowM := window_after_dictionary (dict := []) (bytes := bytes)
            (Or.inr ⟨wsizeZero, whaveZero, rfl⟩) inv.good.inv.win inv'.good.inv.win rfl install
          simp only [List.nil_append] at windowM
          exact ⟨consumed, held, .needDict ([cmf, flg] ++ [c, d, e, f]), inputBits, heldBits, parsed,
            stageM, ⟨check, flags, bits0, width, fun zero => absurd zero (show ¬ (1 : Int32) = 0 by decide),
              fun _ => ⟨by simpa using idEq, windowM⟩⟩, outputEq,
            ⟨fun no => absurd no (by simp), fun ⟨_, _, one⟩ => absurd one (show ¬ (1 : Int32) = 0 by decide)⟩⟩

#print axioms meaning_dictionary

end Zlib.Inflate.Proofs
