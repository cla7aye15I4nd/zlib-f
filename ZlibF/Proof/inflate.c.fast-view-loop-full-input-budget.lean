import ZlibF.Proof.«inflate.c.fast-view-loop-ready-invariant»
import ZlibF.Proof.«inflate.c.fast-view-body-bit-budget»
import ZlibF.Proof.«inffast.c.rollback-input-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The input cursor and held-bit budget relative to the actual fast-call
entry. This relation is also retained by broken loop exits. -/
def FastLoopInputBudget (ctx : FastLoopContext)
    (startOff startBits : Nat) (q : Zlib.Inffast.L) : Prop :=
  ∃ off, q.in_ = .ref ctx.inputRef off ∧ startOff ≤ off ∧
    q.bits.toNat + 8 * startOff ≤ startBits + 8 * off

/-- Output geometry retained on every actual loop return. -/
def FastLoopOutputRange (ctx : FastLoopContext)
    (h : Heap) (q : Zlib.Inffast.L) : Prop :=
  ∃ off array, q.out = .ref ctx.dest off ∧
    ctx.oo ≤ off ∧ off ≤ ctx.oo + ctx.leftTotal.toNat ∧
    Space.get h ctx.dest = some array ∧
    ctx.oo + ctx.leftTotal.toNat ≤ array.size

/-- The last source body can read through at most the five bytes past
the loop's fixed `last` threshold. -/
def FastLoopInputLimit (ctx : FastLoopContext) (q : Zlib.Inffast.L) : Prop :=
  ∃ off lastOff, q.in_ = .ref ctx.inputRef off ∧
    ctx.c.last = .ref ctx.inputRef lastOff ∧ off ≤ lastOff + 5

/-- Actual loop-entry registers witness the initial input account. -/
theorem FastLoopInputBudget.initial
    {ctx : FastLoopContext} {q : Zlib.Inffast.L} {off : Nat}
    (cursor : q.in_ = .ref ctx.inputRef off) :
    FastLoopInputBudget ctx off q.bits.toNat q :=
  ⟨off, cursor, Nat.le_refl _, Nat.le_refl _⟩

/-- One actual body preserves the entry-relative input budget and output
bounds, including every source break. No callee contract is assumed. -/
theorem FastLoopReady.body_full_input_budget
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    {startOff startBits : Nat}
    (ready : FastLoopReady ctx h q)
    (account : FastLoopInputBudget ctx startOff startBits q) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      FastLoopInputBudget ctx startOff startBits result ∧
      FastLoopOutputRange ctx after result ∧ FastLoopInputLimit ctx result := by
  rcases ready with ⟨slow, bs, output, off, k, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  obtain ⟨first, second, third, fourth, fifth, sixth, rest, rfl⟩ :=
    packet.six_unread inputMargin
  have left : slow.left ≠ 0 := by rw [leftEq]; exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest
      (ctx.oo + slow.left.toNat - 257) := by rw [leftEq]; exact ctx.endPtr
  obtain ⟨used, consumed, slowFinal, result, after, zNext, sNext,
    array, next, _, _, run, _, _, _, _, _, _, _, _,
    outputOut, lower, upper, bytes, size, pulled, pulledBound, cursor, budget⟩ :=
    packet.fast_body_view_post_with_bit_budget invariant buffers
      ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe
      ctx.lenMask ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  have initialCursor : q.in_ = .ref ctx.inputRef off := packet.cursor.trans nextPtr
  obtain ⟨oldOff, oldCursor, oldLower, oldBudget⟩ := account
  have same : off = oldOff := (Ptr.ref.inj (initialCursor.symm.trans oldCursor)).2
  subst oldOff
  have resultCursor : result.in_ = .ref ctx.inputRef (off + pulled) := by
    rw [cursor, initialCursor]
    rfl
  refine ⟨result, after, run, ⟨off + pulled, resultCursor, by omega, by omega⟩, ?_, ?_⟩
  · refine ⟨next, array, outputOut, by omega, ?_, bytes, ?_⟩
    · rw [← leftEq]
      exact upper
    · rw [← leftEq]
      omega
  · exact ⟨off + pulled, off + slow.have_.toNat - 5,
      resultCursor, lastPtr, by omega⟩

/-- The actual complete fast loop returns within its fuel bound and
retains input accounting and output bounds on every exit, including breaks. -/
theorem FastLoopReady.run_full_input_budget
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    {startOff startBits : Nat}
    (ready : FastLoopReady ctx h q)
    (account : FastLoopInputBudget ctx startOff startBits q) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      FastLoopInputBudget ctx startOff startBits result ∧
      FastLoopOutputRange ctx after result ∧ FastLoopInputLimit ctx result := by
  let Inv : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopReady ctx heap current ∧ FastLoopInputBudget ctx startOff startBits current
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopExit ctx heap current ∧ FastLoopInputBudget ctx startOff startBits current ∧
      FastLoopOutputRange ctx heap current ∧ FastLoopInputLimit ctx current
  have step : ∀ current heap, Inv current heap →
      ∃ result after, Zlib.Inffast.inflate_fast_body ctx.c current heap = .ok (result, after) ∧
        ((∃ next heap2, fastLoopCond ctx result after = .ok ((false, next), heap2) ∧
          Final next heap2) ∨
         (∃ next heap2, fastLoopCond ctx result after = .ok ((true, next), heap2) ∧
          Inv next heap2 ∧ fastLoopMeasure ctx next < fastLoopMeasure ctx current)) := by
    intro current heap state
    obtain ⟨readyNow, accountNow⟩ := state
    obtain ⟨result, after, bodyRun, outcome⟩ := readyNow.step
    obtain ⟨budgetResult, budgetAfter, budgetRun, budget, output, limit⟩ :=
      readyNow.body_full_input_budget accountNow
    have same : (result, after) = (budgetResult, budgetAfter) :=
      Except.ok.inj (bodyRun.symm.trans budgetRun)
    cases same
    refine ⟨result, after, bodyRun, ?_⟩
    rcases outcome with stopped | continuing
    · exact Or.inl ⟨result, after, stopped.1, stopped.2, budget, output, limit⟩
    · exact Or.inr ⟨result, after, continuing.1,
        ⟨continuing.2.1, budget⟩, continuing.2.2⟩
  have fuelBound : fastLoopMeasure ctx q < fuel := by
    rcases ready with ⟨slow, bs, output, off, k, packet,
      invariant, buffers, codesGet, distGet, bitsBound,
      leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
      outPtr, outputGet, outputWrite, outputSize, current,
      beginLe, span, guard⟩
    apply Zlib.Inffast.Proofs.lt_fuel_of
    simp only [fastLoopMeasure, outPtr]
    have width := UInt32.toNat_lt ctx.leftTotal
    omega
  obtain ⟨result, after, run, final⟩ :=
    Zlib.Inffast.Proofs.Wp.exists_eq
      (Zlib.Inffast.Proofs.Wp.cdoWhile Inv (fastLoopMeasure ctx) Final
        step ⟨ready, account⟩ fuelBound)
  exact ⟨result, after, run, final⟩

/-- Every actual loop exit with the entry-relative bit budget admits its
whole-byte rollback, with a result no earlier than the fast-call entry. -/
theorem FastLoopExit.rollback_full_input_budget
    {ctx : FastLoopContext} {h : Heap} {result : Zlib.Inffast.L}
    {startOff startBits : Nat}
    (final : FastLoopExit ctx h result)
    (account : FastLoopInputBudget ctx startOff startBits result)
    (initialBits : startBits < 8) :
    ∃ off input used,
      result.in_ = .ref ctx.inputRef off ∧
      Space.get h ctx.inputRef = some input ∧
      used ≤ off - startOff ∧
      used + (result.bits >>> 3).toNat = off - startOff ∧
      C.run (Zlib.Inffast.subn result.in_ (result.bits >>> 3)) h =
        .ok (.ref ctx.inputRef (startOff + used), h) := by
  obtain ⟨slow, bs, z, s, packet, invariant, buffers⟩ := final
  obtain ⟨off, cursor, lower, budget⟩ := account
  have slowPtr : slow.next = .ref ctx.inputRef off := packet.cursor.symm.trans cursor
  obtain ⟨input, inputGet, inputBound⟩ :=
    caller_range_ref_view (by simpa only [slowPtr] using buffers.input)
  have exactOffset : startOff + (off - startOff) = off := by omega
  have cursorFromEntry : result.in_ = .ref ctx.inputRef (startOff + (off - startOff)) := by
    rw [exactOffset]
    exact cursor
  obtain ⟨used, usedBound, count, _, rollback⟩ :=
    Zlib.Inffast.Proofs.rollback_input_account inputGet cursorFromEntry
      (by rw [exactOffset]; omega) initialBits (by omega)
  exact ⟨off, input, used, cursor, inputGet, usedBound, count, rollback⟩

/-- The complete actual loop and its rollback compose from an entry
witness. The rollback conclusion has no nonbreaking-exit side condition. -/
theorem FastLoopReady.run_with_accounted_rollback
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q)
    (initialBits : q.bits.toNat < 8) :
    ∃ startOff result after off used input,
      q.in_ = .ref ctx.inputRef startOff ∧
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      FastLoopInputBudget ctx startOff q.bits.toNat result ∧
      FastLoopOutputRange ctx after result ∧ FastLoopInputLimit ctx result ∧
      result.in_ = .ref ctx.inputRef off ∧
      Space.get after ctx.inputRef = some input ∧
      used ≤ off - startOff ∧
      used + (result.bits >>> 3).toNat = off - startOff ∧
      C.run (Zlib.Inffast.subn result.in_ (result.bits >>> 3)) after =
        .ok (.ref ctx.inputRef (startOff + used), after) := by
  have inputCursor : ∃ startOff, q.in_ = .ref ctx.inputRef startOff := by
    rcases ready with ⟨slow, bs, output, off, k, packet,
      invariant, buffers, codesGet, distGet, bitsBound,
      leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
      outPtr, outputGet, outputWrite, outputSize, current,
      beginLe, span, guard⟩
    exact ⟨off, packet.cursor.trans nextPtr⟩
  obtain ⟨startOff, initialCursor⟩ := inputCursor
  obtain ⟨result, after, run, final, account, output, limit⟩ :=
    ready.run_full_input_budget (FastLoopInputBudget.initial initialCursor)
  obtain ⟨off, input, used, cursor, inputGet, usedBound, count, rollback⟩ :=
    final.rollback_full_input_budget account initialBits
  exact ⟨startOff, result, after, off, used, input, initialCursor, run,
    final, account, output, limit, cursor, inputGet, usedBound, count, rollback⟩

#print axioms FastLoopReady.run_with_accounted_rollback

#print axioms FastLoopReady.body_full_input_budget
#print axioms FastLoopReady.run_full_input_budget
#print axioms FastLoopExit.rollback_full_input_budget
end Zlib.Inflate.Proofs
