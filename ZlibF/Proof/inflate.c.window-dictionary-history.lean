import ZlibF.Proof.«inflate.c.window-physical-history»
import ZlibF.Proof.«inflate.c.dictionary-install-default»

namespace Zlib.Inflate.Proofs.WindowHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Every actual successful setter appends its bytes to the physical
saved-window history. A repeated DICT installation may therefore retain
an older prefix, even though the public DataLog dictionary is replaced. -/
theorem inflateSetDictionary_window_history
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {source : BPtr} {len : UInt32} {history incoming : List UInt8}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (range : CallerRange h r source len.toNat false)
    (input : Bytes h source len.toNat incoming)
    (stored : InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) :
    ∃ rc after state, C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after) ∧
      DefaultStateJ after r zs z state ∧
      ((rc = Z_OK ∧ state.mode = s.mode ∧ InflateDictionary after state
          ((history ++ incoming).drop ((history ++ incoming).length - 2 ^ state.wbits.toNat))) ∨
       ((rc = Z_STREAM_ERROR ∨ rc = Z_DATA_ERROR) ∧ after = h ∧ state = s) ∨
       (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  by_cases refused : source = .null ∨ (s.wrap ≠ 0 ∧ s.mode ≠ DICT)
  · exact ⟨Z_STREAM_ERROR, h, s, inflateSetDictionary_refused_any invariant.good.live source len refused,
      invariant, Or.inr (Or.inl ⟨Or.inl rfl, rfl, rfl⟩)⟩
  have nonnull : source ≠ .null := fun null => refused (Or.inl null)
  have allowed : s.wrap = 0 ∨ s.mode = DICT := by
    by_cases raw : s.wrap = 0
    · exact Or.inl raw
    · right
      exact Classical.byContradiction (fun wrong => refused (Or.inr ⟨raw, wrong⟩))
  rcases input with null | ⟨ref, off, array, pointer, get, room, values⟩
  · exact False.elim (nonnull null.1)
  rw [pointer]
  by_cases mismatch : s.mode = DICT ∧
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 ≠ s.check
  · exact ⟨Z_DATA_ERROR, h, s,
      inflateSetDictionary_dataerr_any invariant.good.live get room mismatch.1 mismatch.2,
      invariant, Or.inr (Or.inl ⟨Or.inr rfl, rfl, rfl⟩)⟩
  have checked : s.mode = DICT →
      (ZlibF.Spec.adler32 (Zlib.Adler32.Proofs.seg array off len.toNat)).toUInt64 = s.check := by
    intro dict
    exact Classical.byContradiction (fun wrong => mismatch ⟨dict, wrong⟩)
  have unowned := callerRange_private_window invariant.good range pointer
  have separate : Separate (.ref ref off) len.toNat s.window (2 ^ s.wbits.toNat) := by
    rcases invariant.good.inv.win.block with null | ⟨w, bytes, window, _⟩
    · simp [Separate, null]
    · simp [Separate, window, unowned w window]
  obtain ⟨wr, heap1, state1, windowRun, good1, windowFrame, _sourceView, codeViews, outcome⟩ :=
    updatewindow_decoder_boundary invariant.good allocator.1 get (by omega : len.toNat ≤ off + len.toNat) room unowned
  have input0 : Bytes h (.ref ref off) len.toNat incoming :=
    Or.inr ⟨ref, off, array, rfl, get, room, values⟩
  obtain ⟨historyRc, historyHeap, historyState, historyRun, historyGood, _historyFrame,
    historyBits, historyOutcome⟩ :=
    updatewindow_history_suffix_framed invariant.good allocator.1 input0 stored separate
  have historyRun0 : updatewindow (some r) (.ref ref (off + len.toNat)) len h =
      .ok (historyRc, historyHeap) := historyRun
  have same := Except.ok.inj (windowRun.symm.trans historyRun0)
  cases same
  have stateSame : historyState = state1 :=
    Option.some.inj (historyGood.live.hs.symm.trans good1.live.hs)
  subst historyState
  obtain ⟨platform, static⟩ := updatewindow_platform_public invariant.good invariant.platform
    allocator.1 get (by omega : len.toNat ≤ off + len.toNat) room
    (by simpa only [Nat.add_sub_cancel] using separate) windowRun
  have current := invariant.window_update good1 windowFrame codeViews platform static
  have actual := inflateSetDictionary_window_cut invariant.good.live get room allowed checked windowRun good1.live.hs
  rcases outcome with success | failure
  · subst wr
    have dictionary : InflateDictionary heap1 state1
        ((history ++ incoming).drop ((history ++ incoming).length - 2 ^ state1.wbits.toNat)) := by
      rcases historyOutcome with success | ⟨impossible, _⟩
      · exact success.2
      · exact False.elim ((by decide : (0 : Int32) ≠ 1) impossible)
    have nextDictionary := dictionary_transport dictionary (after := setI heap1 zs {state1 with havedict := 1})
      (state := {state1 with havedict := 1}) rfl rfl rfl rfl (byte_view_get_setI heap1 zs _)
    exact ⟨Z_OK, setI heap1 zs {state1 with havedict := 1}, {state1 with havedict := 1},
      by simpa only [ite_true] using actual, current.set_havedict,
      Or.inl ⟨rfl, by change state1.mode = s.mode; rw [windowFrame], nextDictionary⟩⟩
  · obtain ⟨code, _window, sameState, _heap⟩ := failure
    subst wr
    subst state1
    have good : Good (setI heap1 zs {s with mode := MEM}) r zs z {s with mode := MEM} :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have next := current.mem_update good (platform.with_istates _) rfl
    exact ⟨Z_MEM_ERROR, setI heap1 zs {s with mode := MEM}, {s with mode := MEM},
      by simpa only [show ¬ ((1 : Int32) = 0) from by decide, ite_false] using actual,
      next, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

#print axioms inflateSetDictionary_window_history
end Zlib.Inflate.Proofs.WindowHistory
