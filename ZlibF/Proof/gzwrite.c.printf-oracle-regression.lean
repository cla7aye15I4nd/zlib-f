import ZlibF.Proof.«gzwrite.c.borrowed-error-regression»

/-!
# gzwrite.c: a failing `vsnprintf` inside the proved domain

The `vsnprintf` of `gzvprintf` may fail on any call (the world oracle `printfOk`; glibc fails for large widths,
positional arguments, wide conversions, a length past `INT_MAX`). This regression shows that the failure branch is
reachable inside the domain the goals quantify over, so the oracle is not dead text: a real `gzopen("p", "wT")` in a
world whose oracle fails, `gzbuffer(8)`, then `gzprintf` with the represented format `"p"`. As the C does with
`len = -1` (`(unsigned)len >= state->size`), the call returns 0, and the history stays reachable.
-/

namespace Zlib.Gzwrite.PrintfOracleRegression
open C Zlib.GzFs Zlib.Gzguts Zlib.Gzlib Zlib.Gzwrite
open ZlibF.Spec.Public
open Zlib.Gzwrite.BorrowRegression

/-- The empty zero-limit world of the borrowed-error regression, with a `vsnprintf` that fails on every call. -/
def failFs : Fs := { initialFs with printfOk := fun _ => false }

/-- The world after the open: as in the borrowed-error regression, with the failing oracle. -/
def failOpenedFs : Fs := { openedFs with printfOk := fun _ => false }

theorem fail_world_valid : FileSystem failFs := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro path node hm; simp [failFs, initialFs] at hm
  · intro i file hg; simp [failFs, initialFs] at hg
  · intro i node hg; simp [failFs, initialFs] at hg

set_option maxRecDepth 20000 in
theorem fail_open (statics : Statics) :
    gzopen (.ref (.blk 0) 0) (.ref (.blk 1) 0) failFs (callerHeap statics) =
      .ok ((some (.in_gzstate_x 2), failOpenedFs), openedHeap statics) := by
  conv => lhs; cbv
  conv => rhs; cbv
  all_goals rfl

set_option maxRecDepth 20000 in
/-- `gzprintf(file, "p")` with the oracle failing returns 0. -/
theorem fail_printf (statics : Statics) :
    ∃ fs' after, gzprintf (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) [] failOpenedFs (smallHeap statics) =
      .ok ((0, fs'), after) := by
  have e : gzprintf (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) [] failOpenedFs (smallHeap statics) =
      gzprintf (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) [] failOpenedFs (smallHeap statics) := rfl
  conv at e => rhs; cbv
  exact ⟨_, _, e⟩

/-- The format `"p"` is represented: it formats to the one byte `p`. -/
theorem p_formatted (statics : Statics) :
    Formatted (smallHeap statics) (.ref (.blk 0) 0) [] [112] := by
  refine ⟨[112], ⟨Or.inr ⟨.blk 0, 0, #[112, 0], rfl, rfl, by decide, rfl⟩, by decide, by decide⟩, ?_⟩
  rfl

/-- **The failure branch is reachable**: a reachable writer, a represented format, the oracle failing on this call,
and `gzprintf` returning 0 with the history still reachable. -/
theorem printf_failure_reachable (statics : Statics) (hg : LibraryGlobals (callerHeap statics)) :
    failOpenedFs.printfOk failOpenedFs.nprintf = false ∧
    ∃ fs' after, gzprintf (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) [] failOpenedFs (smallHeap statics) =
      .ok ((0, fs'), after) ∧ GzReachable after fs' 2 := by
  refine ⟨rfl, ?_⟩
  have hc := caller_fresh_uniq statics
  have hp : CString (callerHeap statics) (.ref (.blk 0) 0) [112] :=
    ⟨Or.inr ⟨.blk 0, 0, #[112, 0], rfl, rfl, by decide, rfl⟩, by decide, by decide⟩
  have hm : CString (callerHeap statics) (.ref (.blk 1) 0) [119, 84] :=
    ⟨Or.inr ⟨.blk 1, 0, #[119, 84, 0], rfl, rfl, by decide, rfl⟩, by decide, by decide⟩
  have ho := GzReachable.open hc.1 hc.2 hg fail_world_valid hp hm (fail_open statics)
  have hbexec : (Call.gzbuffer (some (.in_gzstate_x 2)) 8).execute failOpenedFs (openedHeap statics) =
      .ok (((0 : Int32), failOpenedFs), smallHeap statics) := by
    simp only [Call.execute, heapCall, actual_buffer]
  have hb := GzReachable.step ho (show (openedHeap statics).gzstates 2 = some openedState from rfl)
    (show GzOperation 2 (.gzbuffer (some (.in_gzstate_x 2)) 8) from rfl)
    (show GzArguments (openedHeap statics) 2 openedState (.gzbuffer (some (.in_gzstate_x 2)) 8) from True.intro) hbexec
  obtain ⟨fs', after, run⟩ := fail_printf statics
  refine ⟨fs', after, run, ?_⟩
  exact GzReachable.step hb (show (smallHeap statics).gzstates 2 = some smallState from rfl)
    (show GzOperation 2 (.gzprintf (some (.in_gzstate_x 2)) (.ref (.blk 0) 0) []) from rfl)
    ⟨⟨[112], p_formatted statics⟩, fun b hb => by
      have e : b = 0 := hb
      subst e
      simp [GzOwned, smallState, openedState, GzState.zeroed, GzState.garbage]
      exact fun hz => absurd rfl hz, fun q hq => nomatch hq⟩ run

end Zlib.Gzwrite.PrintfOracleRegression
