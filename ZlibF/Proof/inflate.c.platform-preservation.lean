import ZlibF.Proof.«inflate.c.call-safety»

/-!
# inflate.c: stream operations keep the object-size limit

The history relation assumes `ZlibF.PlatformMemory.ByteObjectsFit` on every
heap of a call history. These lemmas show the library itself never breaks
it, so a history that starts with it needs it again only where the caller
supplies new storage.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- One stream operation keeps the object-size limit. -/
def PlatformPreserves (r : ZStreamRef) (call : Call) : Prop :=
  ∀ (h after : Heap) (i : Nat) (z : ZStream) (s : InflateState) (value : call.Result),
    InflateInv h r i z s → ZlibF.PlatformMemory.ByteObjectsFit h → StreamArguments h r call →
    call.execute default h = .ok ((value, default), after) →
    ZlibF.PlatformMemory.ByteObjectsFit after

theorem platform_resetHeap {h : Heap} (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (s : InflateState) : ZlibF.PlatformMemory.ByteObjectsFit (resetHeap h s) := by
  unfold resetHeap
  split
  · exact platform_freeWin platform s.window
  · exact platform

/-- A record write: stream record and decoder state. -/
theorem platform_records {h : Heap} (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (r : ZStreamRef) (stream : ZStream) (zs : Nat) (state : InflateState) :
    ZlibF.PlatformMemory.ByteObjectsFit (setI (r.put h stream) zs state) :=
  (platform.put_stream r stream).with_istates _

theorem inflateSyncPoint_platform (r : ZStreamRef) :
    PlatformPreserves r (.inflateSyncPoint (some r)) := by
  intro h after i z s value current platform _ actual
  have run := inflateSyncPoint_spec current.good.live
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact platform

theorem inflateMark_platform (r : ZStreamRef) : PlatformPreserves r (.inflateMark (some r)) := by
  intro h after i z s value current platform _ actual
  obtain ⟨mark, run, _⟩ := inflateMark_spec current.good.live
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact platform

theorem inflateCodesUsed_platform (r : ZStreamRef) :
    PlatformPreserves r (.inflateCodesUsed (some r)) := by
  intro h after i z s value current platform _ actual
  obtain ⟨offset, _, _, run⟩ := inflateCodesUsed_spec current.good
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact platform

theorem inflateUndermine_platform (r : ZStreamRef) (subvert : Int32) :
    PlatformPreserves r (.inflateUndermine (some r) subvert) := by
  intro h after i z s value current platform _ actual
  obtain ⟨written, run, heap, _⟩ := inflateUndermine_safe current.good subvert
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  rw [heap]
  exact platform.with_istates _

theorem inflateValidate_platform (r : ZStreamRef) (check : Int32) :
    PlatformPreserves r (.inflateValidate (some r) check) := by
  intro h after i z s value current platform _ actual
  obtain ⟨written, run, heap, _, _⟩ := inflateValidate_safe current.good check
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  rw [heap]
  exact platform.with_istates _

theorem inflatePrime_platform (r : ZStreamRef) (bits word : Int32) :
    PlatformPreserves r (.inflatePrime (some r) bits word) := by
  intro h after i z s value current platform _ actual
  change heapCall (inflatePrime (some r) bits word) default h = _ at actual
  have run := run_of_heapCall actual
  rcases inflatePrime_default_record_image current.good bits word run with same | ⟨state, heap, _⟩
  · rw [same]
    exact platform
  · rw [heap]
    exact platform.with_istates _

theorem inflateResetKeep_platform (r : ZStreamRef) :
    PlatformPreserves r (.inflateResetKeep (some r)) := by
  intro h after i z s value current platform _ actual
  obtain ⟨written, run, heap, _, _⟩ := inflateResetKeep_safe current.good
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  rw [heap]
  exact platform_records platform _ _ _ _

theorem inflateReset_platform (r : ZStreamRef) : PlatformPreserves r (.inflateReset (some r)) := by
  intro h after i z s value current platform _ actual
  obtain ⟨written, run, heap, _, _⟩ := inflateReset_safe current.good current.alloc.2
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  rw [heap]
  exact platform_records (platform_resetHeap platform s) _ _ _ _

theorem inflateReset2_platform (r : ZStreamRef) (wb : Int32) :
    PlatformPreserves r (.inflateReset2 (some r) wb) := by
  intro h after i z s value current platform _ actual
  obtain ⟨code, written, run, result⟩ := inflateReset2_safe current.good current.alloc.2 wb
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  cases params : reset2Params wb with
  | none =>
    rw [params] at result
    rw [result.2]
    exact platform
  | some selected =>
    obtain ⟨wrap, width⟩ := selected
    rw [params] at result
    rw [result.2.1]
    exact platform_records (platform_reset2Heap platform width s) _ _ _ _

theorem inflateGetHeader_platform (r : ZStreamRef) (head : GzHeaderPtr) :
    PlatformPreserves r (.inflateGetHeader (some r) head) := by
  intro h after i z s value current platform arguments actual
  change heapCall (inflateGetHeader (some r) head) default h = _ at actual
  have run := run_of_heapCall actual
  obtain ⟨memory, present⟩ := arguments
  by_cases nogzip : s.wrap &&& 2 = 0
  · have expected := inflateGetHeader_nogzip current.good.live head nogzip
    have same := Except.ok.inj (run.symm.trans expected)
    cases same
    exact platform
  rcases memory with none | ⟨b, gh, pointer, get, _⟩
  · exact absurd none present
  subst pointer
  obtain ⟨written, expected, heap, _, _, _⟩ :=
    inflateGetHeader_ok current.good (g := .tab b) get nogzip
  have same := Except.ok.inj (run.symm.trans expected)
  cases same
  rw [heap]
  apply platform.of_storage_eq
  all_goals simp only [GzHeaderRef.put, setI]
  all_goals split <;> rfl

#print axioms inflateReset2_platform
#print axioms inflateGetHeader_platform

theorem inflateGetDictionary_platform (r : ZStreamRef) (dest : BPtr) (dl : Option UInt32) :
    PlatformPreserves r (.inflateGetDictionary (some r) dest dl) := by
  intro h after zs z s value current platform arguments actual
  change heapCall (inflateGetDictionary (some r) dest dl) default h = _ at actual
  have run := run_of_heapCall actual
  obtain ⟨stream, index, state, streamGet, pointer, stateGet, range⟩ := arguments
  have sameStream : stream = z := Option.some.inj (streamGet.symm.trans current.good.live.hz)
  subst stream
  have sameIndex : index = zs := by
    rw [current.good.live.zst] at pointer
    cases pointer
    rfl
  subst index
  have sameState : state = s := Option.some.inj (stateGet.symm.trans current.good.live.hs)
  subst state
  have good := current.good
  by_cases empty : dest = .null ∨ s.whave = 0
  · have expected : C.run (inflateGetDictionary (some r) dest dl) h =
        .ok ((Z_OK, dl.map (fun _ => s.whave)), h) := by
      unfold C.run inflateGetDictionary
      rcases empty with null | zero
      · cases dl <;> simp [stateCheck_live good.live, ldZ_eq, ldI_eq,
          good.live.hz, good.live.zst, castI, good.live.hs, null]
      · cases dl <;> simp [stateCheck_live good.live, ldZ_eq, ldI_eq,
          good.live.hz, good.live.zst, castI, good.live.hs, zero]
    have same := Except.ok.inj (run.symm.trans expected)
    cases same
    exact platform
  have nonnull : dest ≠ .null := fun null => empty (Or.inl null)
  have positive : s.whave ≠ 0 := fun zero => empty (Or.inr zero)
  have positiveNat : 0 < s.whave.toNat := by
    have : s.whave.toNat ≠ 0 := fun zero => positive (UInt32.toNat_inj.mp (by simpa using zero))
    omega
  obtain ⟨w, a, window, bytes, _write, size⟩ :
      ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧
        h.ro w = false ∧ a.size = 2 ^ s.wbits.toNat := by
    rcases good.inv.win.block with null | block
    · have := good.inv.win.nullws null
      have := good.inv.win.hv
      simp_all
    · exact block
  have windowSize : s.wsize.toNat = a.size := by
    rcases good.inv.win.ws with zero | full
    · have := good.inv.win.hv
      omega
    · omega
  have bounded : s.whave.toNat ≤ a.size := by
    have := good.inv.win.hv
    omega
  have chronological : s.wnext.toNat ≤ s.whave.toNat := by
    rcases Nat.lt_or_ge s.whave.toNat s.wsize.toNat with growing | full
    · have := good.inv.win.eq growing
      omega
    · have := good.inv.win.wn
      have := good.inv.win.hv
      omega
  have writable : Writable h dest s.whave.toNat := by
    rcases range with null | ⟨_read, write⟩
    · exact False.elim (nonnull null)
    · exact write.1 rfl
  rcases writable with ⟨null, _⟩ | ⟨ref, off, old, pointer, get, write, room⟩
  · exact False.elim (nonnull null)
  have separate := callerRange_private_window good range pointer
  have copied := inflateGetDictionary_copy_general (dl := dl) good.live window bytes get write
    (separate w window) positive chronological bounded room
  have expected : C.run (inflateGetDictionary (some r) dest dl) h =
      .ok ((Z_OK, dl.map (fun _ => s.whave)),
        Space.put h ref (getDictBytes old a off s.wnext.toNat s.whave.toNat)) := by
    simpa only [C.run, pointer] using copied
  have same := Except.ok.inj (run.symm.trans expected)
  cases same
  have sizeEq : (getDictBytes old a off s.wnext.toNat s.whave.toNat).size = old.size := by
    simp [getDictBytes, size_copyRange]
  exact (byte_view_sizes_put get write _ sizeEq).platform platform

theorem inflateSetDictionary_platform (r : ZStreamRef) (source : BPtr) (len : UInt32) :
    PlatformPreserves r (.inflateSetDictionary (some r) source len) := by
  intro h after zs z s value current platform range actual
  change heapCall (inflateSetDictionary (some r) source len) default h = _ at actual
  have run := run_of_heapCall actual
  have unchanged : ∀ {rc : Int32},
      C.run (inflateSetDictionary (some r) source len) h = .ok (rc, h) →
      ZlibF.PlatformMemory.ByteObjectsFit after := by
    intro rc expected
    have same := Except.ok.inj (run.symm.trans expected)
    cases same
    exact platform
  by_cases refused : source = .null ∨ (s.wrap ≠ 0 ∧ s.mode ≠ DICT)
  · exact unchanged (inflateSetDictionary_refused_any current.good.live source len refused)
  have nonnull : source ≠ .null := fun null => refused (Or.inl null)
  have allowed : s.wrap = 0 ∨ s.mode = DICT := by
    by_cases raw : s.wrap = 0
    · exact Or.inl raw
    · right
      apply Classical.byContradiction
      intro wrong
      exact refused (Or.inr ⟨raw, wrong⟩)
  have readable : ∃ xs, Bytes h source len.toNat xs := by
    rcases range with null | ⟨readable, _⟩
    · exact False.elim (nonnull null)
    · exact readable
  obtain ⟨xs, null | ⟨ref, off, array, pointer, get, room, _values⟩⟩ := readable
  · exact False.elim (nonnull null.1)
  subst pointer
  by_cases mismatch : s.mode = DICT ∧
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 ≠ s.check
  · exact unchanged (inflateSetDictionary_dataerr_any current.good.live get room mismatch.1 mismatch.2)
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
  obtain ⟨wr, heap1, state1, windowRun, good1, _, _, _, outcome⟩ :=
    updatewindow_decoder_boundary current.good current.alloc.1 get
      (by omega : len.toNat ≤ off + len.toNat) room unowned
  have fit1 := (updatewindow_platform_public current.good platform current.alloc.1 get
    (by omega : len.toNat ≤ off + len.toNat) room
    (by simpa only [Nat.add_sub_cancel] using separate) windowRun).1
  have cut := inflateSetDictionary_window_cut current.good.live get room allowed checked windowRun
    good1.live.hs
  rcases outcome with success | failure
  · subst wr
    have expected := (by simpa only [ite_true] using cut :
      C.run (inflateSetDictionary (some r) (.ref ref off) len) h =
        .ok (Z_OK, setI heap1 zs { state1 with havedict := 1 }))
    have same := Except.ok.inj (run.symm.trans expected)
    cases same
    exact fit1.with_istates _
  · obtain ⟨code, _window, sameState, _heap⟩ := failure
    subst wr
    have expected := (by simpa only [show ¬ ((1 : Int32) = 0) from by decide, ite_false] using cut :
      C.run (inflateSetDictionary (some r) (.ref ref off) len) h =
        .ok (Z_MEM_ERROR, setI heap1 zs { state1 with mode := MEM }))
    have same := Except.ok.inj (run.symm.trans expected)
    cases same
    exact fit1.with_istates _

#print axioms inflateGetDictionary_platform
#print axioms inflateSetDictionary_platform

end Zlib.Inflate.Proofs
