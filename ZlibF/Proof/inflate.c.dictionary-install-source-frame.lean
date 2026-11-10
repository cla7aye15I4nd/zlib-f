import ZlibF.Proof.«inflate.c.dictionary-install-origin»
import ZlibF.Proof.«adler32.c.public-block»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An actual dictionary request exposes its complete source state frame.
Success changes only window fields and havedict; DICT checksum validation
is about the supplied bytes. Refusals and checksum errors change nothing.
The real allocation-failure path changes only mode to MEM. -/
theorem inflateSetDictionary_source_frame
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {source : BPtr} {len : UInt32} {bytes : List UInt8}
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (range : CallerRange h r source len.toNat false)
    (input : Bytes h source len.toNat bytes) :
    ∃ rc after state,
      C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after) ∧
      DefaultOriginState after r zs z state ∧
      (((rc = Z_STREAM_ERROR ∨ rc = Z_DATA_ERROR) ∧ after = h ∧ state = s) ∨
       (rc = Z_MEM_ERROR ∧ state = { s with mode := MEM }) ∨
       (rc = Z_OK ∧ source ≠ .null ∧ (s.wrap = 0 ∨ s.mode = DICT) ∧
         state = { s with
           window := state.window, wsize := state.wsize, whave := state.whave,
           wnext := state.wnext, havedict := 1 } ∧
         (s.mode = DICT → (ZlibF.Spec.adler32 bytes).toUInt64 = s.check))) := by
  by_cases refused : source = .null ∨ (s.wrap ≠ 0 ∧ s.mode ≠ DICT)
  · exact ⟨Z_STREAM_ERROR, h, s,
      inflateSetDictionary_refused_any invariant.good.live source len refused,
      invariant, Or.inl ⟨Or.inl rfl, rfl, rfl⟩⟩
  have nonnull : source ≠ .null := fun null => refused (Or.inl null)
  have allowed : s.wrap = 0 ∨ s.mode = DICT := by
    by_cases raw : s.wrap = 0
    · exact Or.inl raw
    · right
      apply Classical.byContradiction
      intro wrong
      exact refused (Or.inr ⟨raw, wrong⟩)
  rcases input with null | ⟨ref, off, array, pointer, get, room, values⟩
  · exact False.elim (nonnull null.1)
  have semantic : Zlib.Adler32.Proofs.seg array off len.toNat = bytes :=
    (Zlib.Adler32.Proofs.seg_eq_slice array off len.toNat room).trans values.symm
  rw [pointer]
  by_cases mismatch : s.mode = DICT ∧
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 ≠ s.check
  · exact ⟨Z_DATA_ERROR, h, s,
      inflateSetDictionary_dataerr_any invariant.good.live get room mismatch.1 mismatch.2,
      invariant, Or.inl ⟨Or.inr rfl, rfl, rfl⟩⟩
  have checked : s.mode = DICT →
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 = s.check := by
    intro dict
    apply Classical.byContradiction
    intro wrong
    exact mismatch ⟨dict, wrong⟩
  have unowned := callerRange_private_window invariant.good range pointer
  have separate : Separate (.ref ref off) len.toNat s.window (2 ^ s.wbits.toNat) := by
    rcases invariant.good.inv.win.block with missing | ⟨w, data, window, _⟩
    · simp [Separate, missing]
    · simp [Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, _sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary invariant.good allocator.1 get
      (by omega : len.toNat ≤ off + len.toNat) room unowned
  obtain ⟨platform, static⟩ := updatewindow_platform_public invariant.good invariant.platform
    allocator.1 get (by omega : len.toNat ≤ off + len.toNat) room
    (by simpa only [Nat.add_sub_cancel] using separate) windowRun
  have currentJ := invariant.toDefaultStateJ.window_update good1 windowFrame codeViews platform static
  have current := invariant.window_update currentJ windowFrame
  have actual := inflateSetDictionary_window_cut invariant.good.live get room allowed checked
    windowRun good1.live.hs
  rcases outcome with success | failure
  · subst wr
    refine ⟨Z_OK, setI heap1 zs { state1 with havedict := 1 }, { state1 with havedict := 1 },
      ?_, current.set_havedict, Or.inr (Or.inr ⟨rfl, ?_, allowed, ?_, ?_⟩)⟩
    · simpa only [ite_true] using actual
    · intro null
      cases null
    · rw [windowFrame]
    · intro dict
      simpa only [semantic] using checked dict
  · obtain ⟨_code, _window, sameState, _heap⟩ := failure
    subst wr
    subst state1
    have good : Good (setI heap1 zs { s with mode := MEM }) r zs z { s with mode := MEM } :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have nextJ := current.toDefaultStateJ.mem_update good (platform.with_istates _) rfl
    have next := current.of_fields nextJ rfl rfl rfl
    refine ⟨Z_MEM_ERROR, setI heap1 zs { s with mode := MEM }, { s with mode := MEM },
      ?_, next, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    simpa only [show ¬ ((1 : Int32) = 0) from by decide, ite_false] using actual

/-- On a wrapped stream, successful actual installation validates the
identifier and retains every scalar except the explicit window/flag writes. -/
theorem inflateSetDictionary_wrapped_source_observed
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s state : InflateState}
    {source : BPtr} {len : UInt32} {bytes : List UInt8} {rc : Int32}
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (wrapped : s.wrap ≠ 0) (range : CallerRange h r source len.toNat false)
    (input : Bytes h source len.toNat bytes)
    (actual : C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after))
    (stored : after.istates zs = some state) :
    (((rc = Z_STREAM_ERROR ∨ rc = Z_DATA_ERROR) ∧ after = h ∧ state = s) ∨
     (rc = Z_MEM_ERROR ∧ state = { s with mode := MEM }) ∨
     (rc = Z_OK ∧ s.mode = DICT ∧ (ZlibF.Spec.adler32 bytes).toUInt64 = s.check ∧
       state = { s with
         window := state.window, wsize := state.wsize, whave := state.whave,
         wnext := state.wnext, havedict := 1 })) := by
  obtain ⟨code, heap, returned, run, current, outcome⟩ :=
    inflateSetDictionary_source_frame invariant allocator range input
  have pair := Except.ok.inj (run.symm.trans actual)
  cases pair
  have sameState : returned = state := Option.some.inj (current.good.live.hs.symm.trans stored)
  subst returned
  rcases outcome with refused | failed | success
  · exact Or.inl refused
  · exact Or.inr (Or.inl failed)
  · obtain ⟨ok, _nonnull, allowed, frame, checked⟩ := success
    have dict := allowed.resolve_left wrapped
    exact Or.inr (Or.inr ⟨ok, dict, checked dict, frame⟩)

#print axioms inflateSetDictionary_source_frame
#print axioms inflateSetDictionary_wrapped_source_observed
end Zlib.Inflate.Proofs
