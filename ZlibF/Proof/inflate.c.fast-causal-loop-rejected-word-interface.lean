import ZlibF.Proof.«inflate.c.fast-causal-loop-word-rollback»
import ZlibF.Proof.«inflate.c.fast-ready-bad-consumed-word»
namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec
open ZlibF.Math.InflateCommittedTokens
set_option autoImplicit false

/-- The last rejected token word follows a separately committed accepted
prefix. The concatenation is a source word, not a single rejected token. -/
structure RejectedObservation {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L)
    extends Observation p h q where
  priorWord : List Bool
  badWord : List Bool
  wordEq : word = priorWord ++ badWord
  priorCommitted : Committed p.L p.D p.dict p.start (p.initialWords ++ priorWord) (p.past ++ history)
  rejected : ∀ future : List Bool, Token.Rejected p.L p.D p.dict (p.past ++ history) (badWord ++ future)
  broke : q.broke = true
  state : ∃ i, DefaultStateJ h ctx.r ctx.zs {ctx.z with msg := .ref (.str i) 0} {ctx.s with mode := BAD}

def WordRejectedOutcome {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L) : Prop :=
  (∃ tracked : Tracked p h q, WordSource tracked.toObservation ∧ DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s) ∨
  (∃ ended : Ended p h q, WordSource ended.toObservation) ∨
  (∃ rejected : RejectedObservation p h q, WordSource rejected.toObservation)

def WordRejectedExit {ctx : FastLoopContext} (p : Parameters ctx) (h : Heap) (q : Zlib.Inffast.L) : Prop :=
  FastLoopExit ctx h q ∧ WordRejectedOutcome p h q

/-- The accepted-prefix context transports a valid original completion to
the last token, where its universally rejected word gives a contradiction. -/
theorem RejectedObservation.no_symbols
    {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap} {q : Zlib.Inffast.L}
    (rejected : RejectedObservation p h q) :
    ∀ future rest output, ¬ Symbols p.L p.D p.dict p.start
      ((p.initialWords ++ rejected.word) ++ future) rest output := by
  intro future rest output parsed
  have atLast : Symbols p.L p.D p.dict (p.past ++ rejected.history) (rejected.badWord ++ future) rest output := by
    apply (rejected.priorCommitted.future (rejected.badWord ++ future) rest output).mp
    simpa only [rejected.wordEq, List.append_assoc] using parsed
  exact Token.rejected_has_no_symbols p.L p.D p.dict (p.past ++ rejected.history)
    (rejected.badWord ++ future) (rejected.rejected future) rest output atLast

#print axioms RejectedObservation.no_symbols
end Zlib.Inflate.Proofs.FastCommittedLoop
