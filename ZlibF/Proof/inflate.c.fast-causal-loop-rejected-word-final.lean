import ZlibF.Proof.«inflate.c.fast-causal-loop-rejected-word-run»
namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
set_option autoImplicit false

/-- An actual BAD state selects the rejection packet: unchanged normal
state and actual EOB state are excluded by the same heap state cell. -/
theorem WordRejectedOutcome.rejected_of_bad
    {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap} {q : Zlib.Inffast.L}
    {z : ZStream} {s : InflateState}
    (outcome : WordRejectedOutcome p h q) (good : Good h ctx.r ctx.zs z s)
    (badMode : s.mode = BAD) :
    ∃ rejected : RejectedObservation p h q, WordSource rejected.toObservation := by
  rcases outcome with normal | eob | rejected
  · obtain ⟨_tracked, _source, unchanged⟩ := normal
    have same : ctx.s = s := Option.some.inj (unchanged.good.live.hs.symm.trans good.live.hs)
    exact False.elim (FastArbitraryBody.data_mode_ne_bad ctx.mode (by rw [same, badMode]))
  · obtain ⟨ended, _source⟩ := eob
    have same : {ctx.s with mode := TYPE} = s :=
      Option.some.inj (ended.state.good.live.hs.symm.trans good.live.hs)
    have impossible : TYPE = BAD := by simpa only [← same] using badMode
    cases impossible
  · exact rejected

/-- The full real loop, when its actual final state is BAD, excludes
all Symbols completions of the consumed word at the original fast entry.
Held remainder bits belong to the universally quantified continuation. -/
theorem WordRejectedExit.no_symbols_of_bad
    {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap} {q : Zlib.Inffast.L}
    {z : ZStream} {s : InflateState}
    (exit : WordRejectedExit p h q) (good : Good h ctx.r ctx.zs z s)
    (badMode : s.mode = BAD) :
    ∃ rejected : RejectedObservation p h q,
      WordSource rejected.toObservation ∧
      ∀ future rest output, ¬ Symbols p.L p.D p.dict p.start
        ((p.initialWords ++ rejected.word) ++ future) rest output := by
  obtain ⟨rejected, source⟩ := exit.2.rejected_of_bad good badMode
  exact ⟨rejected, source, rejected.no_symbols⟩

#print axioms WordRejectedOutcome.rejected_of_bad
#print axioms WordRejectedExit.no_symbols_of_bad
end Zlib.Inflate.Proofs.FastCommittedLoop
