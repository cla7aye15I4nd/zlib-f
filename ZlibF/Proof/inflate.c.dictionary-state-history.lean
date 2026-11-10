import ZlibF.Proof.«inflate.c.leave-default-state»
import ZlibF.Proof.«inflate.c.public-setdict-success»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Successful window updates retain all decoder-code views under the
public interval separation premise. Empty sources may alias the window. -/
theorem updatewindow_code_views_public {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s state : InflateState} {off : Nat} {source : BRef} {bytes : Array UInt8} {copy : UInt32}
    (good : Good h r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (get : Space.get h source = some bytes) (fit : off + copy.toNat ≤ bytes.size)
    (separate : Separate (.ref source off) copy.toNat s.window (2 ^ s.wbits.toNat))
    (run : C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (0, after))
    (stored : after.istates zs = some state) :
    ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref := by
  have frame := updatewindow_state_frame_public good allocator get fit separate run stored
  have sep : Separate (.ref source ((off + copy.toNat) - copy.toNat)) copy.toNat
      s.window (2 ^ s.wbits.toNat) := by simpa using separate
  rcases good.inv.win.block with window | ⟨w, a, window, array, ro, size⟩
  · by_cases alloc : h.allocOk h.nalloc = true
    · obtain ⟨result, state', execution, nextGood, _, _, views⟩ :=
        uw_null_state_frame_public (copy := copy) (eo := off + copy.toNat)
          good allocator window alloc get (by omega) fit
      have heaps : after = result := congrArg Prod.snd (Except.ok.inj (run.symm.trans execution))
      rwa [heaps]
    · have fail := uw_alloc_fail good.live allocator good.inv.win.wbits window alloc
        (.ref source (off + copy.toNat)) copy
      change updatewindow (some r) (.ref source (off + copy.toNat)) copy h = .ok (0, after) at run
      rw [run] at fail
      cases fail
  · obtain ⟨result, state', execution, heapEq, value, nextGood, rest⟩ :=
      uw_post_public (copy := copy) (eo := off + copy.toNat)
        good window array ro size get (by omega) fit sep
    have heaps : after = result := congrArg Prod.snd (Except.ok.inj (run.symm.trans execution))
    intro ref
    cases ref with
    | istate_codes i =>
      by_cases same : i = zs
      · subst i
        simp only [Space.get, stored, good.live.hs, Option.map_some]
        rw [frame]
      · rw [heaps, heapEq]
        simp [Space.get, setI, upd_ne _ _ _ _ same]
    | st_lenfix => rw [heaps, heapEq]; rfl
    | st_distfix => rw [heaps, heapEq]; rfl

/-- The actual dictionary window operation preserves the full initialized
relation on every allocation outcome and every separated readable source. -/
theorem updatewindow_default_state {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {off : Nat} {source : BRef} {bytes : Array UInt8} {copy : UInt32}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (get : Space.get h source = some bytes) (fit : off + copy.toNat ≤ bytes.size)
    (separate : Separate (.ref source off) copy.toNat s.window (2 ^ s.wbits.toNat)) :
    ∃ rc after state, C.run (updatewindow (some r) (.ref source (off + copy.toNat)) copy) h = .ok (rc, after) ∧
      DefaultStateJ after r zs z state ∧ (rc = 0 ∨ rc = 1) := by
  have sep : Separate (.ref source ((off + copy.toNat) - copy.toNat)) copy.toNat
      s.window (2 ^ s.wbits.toNat) := by simpa using separate
  obtain ⟨rc, after, state, run, good, cases⟩ :=
    updatewindow_safe_public invariant.good allocator.1 get (by omega) fit sep
  obtain ⟨platform, static⟩ := updatewindow_platform_public invariant.good invariant.platform
    allocator.1 get (by omega) fit sep run
  have frame : WindowStateFrame s state := by
    rcases cases with ⟨zero, rest⟩ | ⟨one, window, failed, heapEq, stateEq⟩
    · exact updatewindow_state_frame_public invariant.good allocator.1 get fit separate (by simpa only [zero] using run) good.live.hs
    · rw [stateEq]
      rfl
  have views : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref := by
    rcases cases with ⟨zero, rest⟩ | ⟨one, window, failed, heapEq, stateEq⟩
    · exact updatewindow_code_views_public invariant.good allocator.1 get fit separate (by simpa only [zero] using run) good.live.hs
    · intro ref
      rw [heapEq]
      have same : setI { h with nalloc := h.nalloc + 1 } zs s = { h with nalloc := h.nalloc + 1 } :=
        tcSetI_same invariant.good.live.hs
      rw [same]
      cases ref <;> rfl
  exact ⟨rc, after, state, run, invariant.window_update good frame views platform static,
    cases.elim (fun success => Or.inl success.1) (fun failure => Or.inr failure.1)⟩

/-- Setting the dictionary-present flag changes none of J's guarded
scalar/table/configuration clauses. -/
theorem DefaultStateJ.set_havedict {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) :
    DefaultStateJ (setI h zs { s with havedict := 1 }) r zs z { s with havedict := 1 } := by
  have good := good_state (st' := { s with havedict := 1 }) invariant.good rfl invariant.good.live.mode
    (invariant.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl invariant.good.inv.bits rfl rfl rfl)
  have views : ∀ ref : CodeRef, (Space.get (setI h zs { s with havedict := 1 }) ref : Option (Array Code)) = Space.get h ref := by
    intro ref
    cases ref with
    | istate_codes i =>
      by_cases same : i = zs
      · subst i
        simp [Space.get, invariant.good.live.hs]
      · simp [Space.get, setI, upd_ne _ _ _ _ same]
    | st_lenfix => rfl
    | st_distfix => rfl
  have tables : DataTableInvariant (setI h zs { s with havedict := 1 }) { s with havedict := 1 } := by
    intro active
    obtain ⟨length, distance⟩ := invariant.tables active
    constructor
    · obtain ⟨ref, off, array, pointer, get, safe⟩ := length
      exact ⟨ref, off, array, pointer, by rw [views]; exact get, safe⟩
    · obtain ⟨ref, off, array, pointer, get, safe⟩ := distance
      exact ⟨ref, off, array, pointer, by rw [views]; exact get, safe⟩
  exact ⟨⟨good, tables, ⟨invariant.pending.sane, invariant.pending.lenext,
    invariant.pending.dist, invariant.pending.distext, invariant.pending.matching⟩,
    invariant.lengths, invariant.headerLengths, invariant.held, invariant.window, invariant.wrapper,
    invariant.header, invariant.modes, invariant.trailer, invariant.globals, invariant.platform.with_istates _⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

/-- The real accepted dictionary path preserves full J after window
allocation/copy and after either the havedict or MEM write. No abstract
dictionary contents or successor invariant is assumed as a callee contract. -/
theorem inflateSetDictionary_accepted_default_state {H : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {st : InflateState} {off : Nat} {source : BRef} {D : Array UInt8} {L : UInt32}
    (invariant : DefaultStateJ H r zs z st) (allocator : DefAlloc z)
    (hD : Space.get H source = some D) (hfit : off + L.toNat ≤ D.size)
    (hsep : Separate (.ref source off) L.toNat st.window (2 ^ st.wbits.toNat))
    (hwrap : st.wrap = 0 ∨ st.mode = DICT)
    (hadler : st.mode = DICT → (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg D off L.toNat)).toUInt64 = st.check) :
    ∃ rc after state, C.run (inflateSetDictionary (some r) (.ref source off) L) H = .ok (rc, after) ∧
      DefaultStateJ after r zs z state ∧ DefAlloc z ∧
      ((rc = Z_OK ∧ state.havedict = 1 ∧ state.mode = st.mode) ∨ (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  have hG := invariant.good
  have hL := hG.live
  obtain ⟨v0, H1, st1, hr1, current, codes⟩ := updatewindow_default_state invariant allocator hD hfit hsep
  have hG1 := current.good
  have hadd' : Ptr.add (Ptr.ref source off) (L.toNat : Int) H =
      .ok (Ptr.ref source (off + L.toNat), H) := Ptr.add_nat_ok hD hfit
  have hnn : (Ptr.ref source off == (Ptr.null : BPtr)) = false := by simp
  have hr1' : updatewindow (some r) (Ptr.ref source (off + L.toNat)) L H = .ok (v0, H1) := hr1
  have hrun : inflateSetDictionary (some r) (.ref source off) L H =
      (if v0 = 0 then .ok (Z_OK, setI H1 zs { st1 with havedict := 1 })
       else .ok (Z_MEM_ERROR, setI H1 zs { st1 with mode := MEM })) := by
    have hs1 : H1.istates zs = some st1 := hG1.live.hs
    unfold inflateSetDictionary
    simp only [bind_app, stateCheck_live hL, ldZ_eq, ldI_eq, hL.hz, hL.zst, castI, hL.hs, hnn, bne_self_eq_false,
      Bool.or_self, Bool.false_eq_true, ite_false]
    by_cases hm : st.mode = DICT
    · have hra := adler32_dict_any hD L hfit
      have hck := hadler hm
      have hmb : (st.mode == DICT) = true := by simpa using hm
      simp only [hmb, adler32_init, hra, hck, bne_self_eq_false, hadd', hr1', ite_true, Bool.false_eq_true, ite_false, Bool.and_false, hmb, hm, beq_self_eq_true]
      simp only [bind_app, adler32_init, hra, hck, bne_self_eq_false, hadd', hr1', Bool.false_eq_true, ite_false, setMode, wrI_eq, hs1]
      by_cases hv0 : v0 = 0
      · simp only [hv0, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, bind_app, wrI_eq, hs1, pure_app, setI]
      · have hb : (v0 != 0) = true := by simpa using hv0
        simp only [hb, ite_true, hv0, ite_false, setMode, bind_app, wrI_eq, hs1, pure_app, setI]
    · have hw0 : st.wrap = 0 := by rcases hwrap with h | h; exact h; exact absurd h hm
      have hmb : (st.mode == DICT) = false := by simpa using hm
      simp only [hmb, hw0, hadd', hr1', bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false, Bool.and_false]
      simp only [bind_app, hadd', hr1', Bool.false_eq_true, ite_false, setMode, wrI_eq, hs1]
      by_cases hv0 : v0 = 0
      · simp only [hv0, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, bind_app, wrI_eq, hs1, pure_app, setI]
      · have hb : (v0 != 0) = true := by simpa using hv0
        simp only [hb, ite_true, hv0, ite_false, setMode, bind_app, wrI_eq, hs1, pure_app, setI]
  by_cases zero : v0 = 0
  · have frame := updatewindow_state_frame_public invariant.good allocator.1 hD hfit hsep
      (by simpa only [zero] using hr1) current.good.live.hs
    have mode : st1.mode = st.mode := by rw [frame]
    refine ⟨Z_OK, setI H1 zs { st1 with havedict := 1 }, { st1 with havedict := 1 }, ?_,
      current.set_havedict, allocator, Or.inl ⟨rfl, rfl, mode⟩⟩
    rw [C.run, hrun, if_pos zero]
  · have good := good_state (st' := { st1 with mode := MEM }) current.good rfl mode_mem
      (current.good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl current.good.inv.bits rfl rfl rfl)
    refine ⟨Z_MEM_ERROR, setI H1 zs { st1 with mode := MEM }, { st1 with mode := MEM }, ?_,
      current.mem_update good (current.platform.with_istates _) rfl, allocator, Or.inr ⟨rfl, rfl⟩⟩
    rw [C.run, hrun, if_neg zero]

/-- `int inflateSetDictionary(z_streamp strm, const Bytef *dictionary, uInt dictLength)`.
All actual default-history dictionary outcomes preserve full J and allocator:
argument refusal, checksum refusal, accepted copy, and genuine memory failure.
The readable-source and separation premises are the existing public ones. -/
theorem inflateSetDictionary_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (source : BPtr) (n : UInt32) (xs : List UInt8)
    (readable : source ≠ .null → Bytes h source n.toNat xs)
    (separate : Separate source n.toNat s.window (2 ^ s.wbits.toNat)) :
    ∃ rc after state, C.run (inflateSetDictionary (some r) source n) h = .ok (rc, after) ∧
      DefaultStateJ after r zs z state ∧ DefAlloc z ∧
      (rc = Z_OK ∨ rc = Z_STREAM_ERROR ∨ rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR) := by
  by_cases null : source = .null
  · exact ⟨Z_STREAM_ERROR, h, s,
      inflateSetDictionary_refused_any invariant.good.live source n (Or.inl null),
      invariant, allocator, Or.inr (Or.inl rfl)⟩
  by_cases permitted : s.wrap = 0 ∨ s.mode = DICT
  · rcases readable null with impossible | ⟨ref, off, array, pointer, get, fit, value⟩
    · exact False.elim (null impossible.1)
    subst source
    by_cases wrong : s.mode = DICT ∧ (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off n.toNat)).toUInt64 ≠ s.check
    · exact ⟨Z_DATA_ERROR, h, s,
        inflateSetDictionary_dataerr_any invariant.good.live get fit wrong.1 wrong.2,
        invariant, allocator, Or.inr (Or.inr (Or.inl rfl))⟩
    · have accepted : s.mode = DICT → (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off n.toNat)).toUInt64 = s.check := by
        intro mode
        by_cases equal : (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off n.toNat)).toUInt64 = s.check
        · exact equal
        · exact False.elim (wrong ⟨mode, equal⟩)
      obtain ⟨rc, after, state, run, final, finalAllocator, outcome⟩ :=
        inflateSetDictionary_accepted_default_state invariant allocator get fit separate permitted accepted
      refine ⟨rc, after, state, run, final, finalAllocator, ?_⟩
      rcases outcome with success | failure
      · exact Or.inl success.1
      · exact Or.inr (Or.inr (Or.inr failure.1))
  · have refused : s.wrap ≠ 0 ∧ s.mode ≠ DICT := by
      constructor
      · exact fun equal => permitted (Or.inl equal)
      · exact fun equal => permitted (Or.inr equal)
    exact ⟨Z_STREAM_ERROR, h, s,
      inflateSetDictionary_refused_any invariant.good.live source n (Or.inr refused),
      invariant, allocator, Or.inr (Or.inl rfl)⟩

end Zlib.Inflate.Proofs
