import ZlibF.Spec.Public.GzSafety

/-!
# gz: the `gzgetc()` macro with `x.have = 0`

`GzHistory.getcMacro` and conjunct 3 of `Goal.gz_sequence_safety` ran the `gzgetc()` macro of `zlib.h`
(`Zlib.ZlibH.gzgetc`) only with buffered output (`x.have ≠ 0`). A call of the macro with `x.have = 0`, where the macro
calls the function `gzgetc`, was outside the goal. So the macro's `have = 0` branch was never run by the goal: the
proof mutant `macro-have-guard-dropped` (`tests/proof-mutants/gz-sequence.tsv`), which drops the `have` test so that
the inline path runs with nothing buffered (`have--` wraps and `*next` is read), survived.

The macro now steps a history in either branch, and the goal states it in either branch, with the termination split
of the function it calls. Below: a history continues through a macro call with `x.have = 0`, and the goal's no-fault
clause and post apply to that call.
-/

namespace GzMacroHaveZeroRegression
open C Zlib.GzFs ZlibF.Spec.Public

/-- **A macro call with nothing buffered steps the history.** -/
theorem history_through_empty {h after : Heap} {fs fs' : Fs} {i : Nat} {s : GzState} {value : Int32}
    (hist : GzHistory h fs i) (hs : h.gzstates i = some s) (_h0 : s.x.have = 0)
    (e : Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), after)) :
    GzHistory after fs' i :=
  .getcMacro hist hs e

/-- **The goal covers that call**: no fault but the out-of-fuel outcome, and the post of the function `gzgetc`. -/
theorem goal_covers_empty (G : Goal.gz_sequence_safety) {h : Heap} {fs : Fs} {i : Nat} {s : GzState}
    (hist : GzHistory h fs i) (hs : h.gzstates i = some s) (_h0 : s.x.have = 0) :
    (∀ e, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .error e → e = .outOfFuel) ∧
    (∀ value fs' after, Zlib.ZlibH.gzgetc (some (.in_gzstate_x i)) fs h = .ok ((value, fs'), after) →
      FdsKept fs fs' ∧ GzStepPost h i s (.gzgetc (some (.in_gzstate_x i))) fs' after) :=
  ⟨(G.2.2.1 h fs i s hist hs).1, (G.2.2.1 h fs i s hist hs).2.2⟩

end GzMacroHaveZeroRegression
