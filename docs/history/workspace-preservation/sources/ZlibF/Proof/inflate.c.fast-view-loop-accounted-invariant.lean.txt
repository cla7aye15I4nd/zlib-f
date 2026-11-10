import ZlibF.Proof.«inflate.c.fast-view-loop-bit-account-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual fast loop retains input bit accounting from entry to every
nonbreaking exit. The error-break cursor remains a separate obligation. -/
theorem FastLoopReady.run_account
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L} {startOff startBits : Nat}
    (ready : FastLoopReady ctx h q)
    (account : FastInputAccount ctx startOff startBits q) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ ctx.c.last then
            pure (← Ptr.lt q.out ctx.c.end_, q)
          else pure (false, q)) q) h =
          .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      (result.broke = false →
        FastInputAccount ctx startOff startBits result) := by
  let Inv : Zlib.Inffast.L → Heap → Prop :=
    fun current heap =>
      FastLoopReady ctx heap current ∧
      FastInputAccount ctx startOff startBits current
  let Final : Zlib.Inffast.L → Heap → Prop :=
    fun current heap =>
      FastLoopExit ctx heap current ∧
      (current.broke = false →
        FastInputAccount ctx startOff startBits current)
  have hstep : ∀ current heap, Inv current heap →
      ∃ result after,
        Zlib.Inffast.inflate_fast_body ctx.c current heap =
          .ok (result, after) ∧
        ((∃ q2 h2,
          fastLoopCond ctx result after =
            .ok ((false, q2), h2) ∧
          Final q2 h2) ∨
         (∃ q2 h2,
          fastLoopCond ctx result after =
            .ok ((true, q2), h2) ∧
          Inv q2 h2 ∧
          fastLoopMeasure ctx q2 <
            fastLoopMeasure ctx current)) := by
    intro current heap state
    obtain ⟨readyNow, accountNow⟩ := state
    obtain ⟨result, after, bodyRun, outcome⟩ :=
      readyNow.step_input_account accountNow
    obtain ⟨accountResult, accountAfter, accountRun,
      maintained⟩ :=
      readyNow.body_input_account accountNow
    have same : (result, after) =
        (accountResult, accountAfter) := by
      have eq := bodyRun.symm.trans accountRun
      exact Except.ok.inj eq
    cases same
    refine ⟨result, after, bodyRun, ?_⟩
    rcases outcome with stopped | ⟨condition, next,
      nextAccount, decrease⟩
    · exact Or.inl ⟨result, after, stopped.1,
        stopped.2, maintained⟩
    · exact Or.inr ⟨result, after, condition,
        ⟨next, nextAccount⟩, decrease⟩
  have hfuel : fastLoopMeasure ctx q < fuel := by
    rcases ready with ⟨slow, bs, output, off, k,
      packet, invariant, buffers, codesGet, distGet,
      bitsBound, leftEq, outEq, putPtr, nextPtr,
      lastPtr, inputMargin, outPtr, outputGet,
      outputWrite, outputSize, current, beginLe,
      span, guard⟩
    apply Zlib.Inffast.Proofs.lt_fuel_of
    simp only [fastLoopMeasure, outPtr]
    have width := UInt32.toNat_lt ctx.leftTotal
    omega
  obtain ⟨result, after, run, final⟩ :=
    Zlib.Inffast.Proofs.Wp.exists_eq
      (Zlib.Inffast.Proofs.Wp.cdoWhile
        Inv (fastLoopMeasure ctx) Final hstep
        ⟨ready, account⟩ hfuel)
  refine ⟨result, after, ?_, final.1, final.2⟩
  have condEq : fastLoopCond ctx =
      (fun q => do
        if q.broke then pure (false, q)
        else if ← Ptr.lt q.in_ ctx.c.last then
          pure (← Ptr.lt q.out ctx.c.end_, q)
        else pure (false, q)) := by
    funext q
    rfl
  rw [condEq] at run
  exact run

/-- The entry packet fixes the input object and its starting offset. -/
theorem FastLoopReady.input_cursor
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ off, q.in_ = .ref ctx.inputRef off := by
  rcases ready with ⟨slow, bs, output, off, k,
    packet, invariant, buffers, codesGet, distGet,
    bitsBound, leftEq, outEq, putPtr, nextPtr,
    lastPtr, inputMargin, outPtr, outputGet,
    outputWrite, outputSize, current, beginLe,
    span, guard⟩
  exact ⟨off, packet.cursor.trans nextPtr⟩

/-- The real loop starts with a nonvacuous accounting witness and retains
that account through every nonbreaking exit. -/
theorem FastLoopReady.run_account_from_entry
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ startOff result after,
      q.in_ = .ref ctx.inputRef startOff ∧
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fun q => do
          if q.broke then pure (false, q)
          else if ← Ptr.lt q.in_ ctx.c.last then
            pure (← Ptr.lt q.out ctx.c.end_, q)
          else pure (false, q)) q) h =
          .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      (result.broke = false →
        FastInputAccount ctx startOff q.bits.toNat result) := by
  obtain ⟨startOff, cursor⟩ := ready.input_cursor
  obtain ⟨result, after, run, final, account⟩ :=
    ready.run_account (FastInputAccount.initial cursor)
  exact ⟨startOff, result, after, cursor, run,
    final, account⟩

end Zlib.Inflate.Proofs
