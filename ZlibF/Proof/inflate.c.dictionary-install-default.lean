import ZlibF.Proof.«inflate.c.dictionary-install-cut»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual dictionary request preserves the full initialized default
state. CallerRange derives the readable general byte view and window
exclusion. Null/wrong-state/checksum refusals and genuine allocation failure
remain in scope; no dictionary contents or window-success contract is assumed. -/
theorem inflateSetDictionary_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (source : BPtr) (len : UInt32) (range : CallerRange h r source len.toNat false) :
    ∃ rc after state, C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after) ∧
      DefaultStateJ after r zs z state ∧
      (rc = Z_OK ∨ rc = Z_STREAM_ERROR ∨ rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR) := by
  by_cases refused : source = .null ∨ (s.wrap ≠ 0 ∧ s.mode ≠ DICT)
  · exact ⟨Z_STREAM_ERROR, h, s, inflateSetDictionary_refused_any invariant.good.live source len refused,
      invariant, Or.inr (Or.inl rfl)⟩
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
  rw [pointer]
  by_cases mismatch : s.mode = DICT ∧
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 ≠ s.check
  · exact ⟨Z_DATA_ERROR, h, s,
      inflateSetDictionary_dataerr_any invariant.good.live get room mismatch.1 mismatch.2,
      invariant, Or.inr (Or.inr (Or.inl rfl))⟩
  have checked : s.mode = DICT →
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 = s.check := by
    intro dict
    apply Classical.byContradiction
    intro wrong
    exact mismatch ⟨dict, wrong⟩
  have unowned := callerRange_private_window invariant.good range pointer
  have separate : Separate (.ref ref off) len.toNat s.window (2 ^ s.wbits.toNat) := by
    rcases invariant.good.inv.win.block with null | ⟨w, bytes, window, _⟩
    · simp [Separate, null]
    · simp [Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, _sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary invariant.good allocator.1 get (by omega : len.toNat ≤ off + len.toNat) room unowned
  obtain ⟨platform, static⟩ := updatewindow_platform_public invariant.good invariant.platform
    allocator.1 get (by omega : len.toNat ≤ off + len.toNat) room
    (by simpa only [Nat.add_sub_cancel] using separate) windowRun
  have current := invariant.window_update good1 windowFrame codeViews platform static
  have actual := inflateSetDictionary_window_cut invariant.good.live get room allowed checked windowRun good1.live.hs
  rcases outcome with success | failure
  · subst wr
    refine ⟨Z_OK, setI heap1 zs { state1 with havedict := 1 }, { state1 with havedict := 1 },
      ?_, current.set_havedict, Or.inl rfl⟩
    simpa only [ite_true] using actual
  · obtain ⟨code, _window, sameState, _heap⟩ := failure
    subst wr
    subst state1
    have good : Good (setI heap1 zs { s with mode := MEM }) r zs z { s with mode := MEM } :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have next := current.mem_update good (platform.with_istates _) rfl
    refine ⟨Z_MEM_ERROR, setI heap1 zs { s with mode := MEM }, { s with mode := MEM },
      ?_, next, Or.inr (Or.inr (Or.inr rfl))⟩
    simpa only [show ¬ ((1 : Int32) = 0) from by decide, ite_false] using actual

#print axioms inflateSetDictionary_default_state
end Zlib.Inflate.Proofs
