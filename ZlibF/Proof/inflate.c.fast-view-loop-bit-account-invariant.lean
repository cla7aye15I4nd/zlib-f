import ZlibF.Proof.«inflate.c.fast-view-writeback-bits-invariant»
import ZlibF.Proof.«inflate.c.fast-view-bit-accounting-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- One actual fast body charges every held bit to the incoming bit buffer
or to one of at most six newly read bytes. On a continuing branch, the
source cursor advances by exactly that read count. -/
theorem FastLoopReady.body_bit_account
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ (off used : Nat) (result : Zlib.Inffast.L)
        (after : Heap),
      q.in_ = .ref ctx.inputRef off ∧
      used ≤ 6 ∧
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h =
        .ok (result, after) ∧
      result.bits.toNat ≤ q.bits.toNat + 8 * used ∧
      (result.broke = false →
        result.in_ = .ref ctx.inputRef (off + used)) := by
  rcases ready with ⟨slow, bs, output, off, k,
    packet, invariant, buffers, codesGet, distGet,
    bitsBound, leftEq, outEq, putPtr, nextPtr,
    lastPtr, inputMargin, outPtr, outputGet,
    outputWrite, outputSize, current, beginLe,
    span, guard⟩
  obtain ⟨first, second, third, fourth, fifth, sixth,
    rest, rfl⟩ := packet.six_unread inputMargin
  have left : slow.left ≠ 0 := by
    rw [leftEq]
    exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by
    rw [leftEq]
    exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest
      (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]
    exact ctx.endPtr
  have count : slow.left.toNat ≤ slow.out_.toNat := by
    rw [leftEq, outEq]
    exact ctx.count
  have made : slow.out_.toNat - slow.left.toNat ≤
      ctx.oo := by
    rw [leftEq, outEq]
    exact ctx.made
  have beginEq : ctx.bg = ctx.oo -
      (slow.out_.toNat - slow.left.toNat) := by
    rw [leftEq, outEq]
    exact ctx.beginEq
  obtain ⟨used, consumed, slowFinal, result, after,
    zNext, sNext, usedBound, consumedBound, bodyRun,
    finalPacket, finalJ, finalBuffers, sizes, source,
    rank, finalFrame, heapFrame, keepGoing, condRun,
    continuing, finalBits⟩ :=
    packet.fast_body_condition_heap_bits_default_state
      invariant buffers ctx.streamPtr ctx.statePtr ctx.mode
      ctx.whaveEq ctx.wsizeEq ctx.wnextEq ctx.windowEq
      ctx.lcodePtr codesGet ctx.lenSafe ctx.lenMask
      ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr
      endPtr outputGet outputWrite outputSize current
      beginLe span guard nextPtr lastPtr
  have usedLe : used ≤
      (first :: second :: third :: fourth :: fifth ::
        sixth :: rest).length := by
    simp only [List.length_cons]
    omega
  have budget := fast_stream_drop_bit_upper usedLe source
  have initialCursor : q.in_ = .ref ctx.inputRef off :=
    packet.cursor.trans nextPtr
  have finalBudget : result.bits.toNat ≤
      q.bits.toNat + 8 * used := by
    rw [finalPacket.bits, packet.bits]
    exact budget
  refine ⟨off, used, result, after, initialCursor,
    usedBound, bodyRun, finalBudget, ?_⟩
  intro notBroken
  obtain ⟨_, _, _, nextFrame, _, _⟩ :=
    finalFrame notBroken
  calc
    result.in_ = slowFinal.next := finalPacket.cursor
    _ = inputAdvance slow.next used := nextFrame
    _ = .ref ctx.inputRef (off + used) := by
      rw [nextPtr]
      rfl

/-- Loop-wide input accounting relative to the fast-call entry. -/
def FastInputAccount (ctx : FastLoopContext)
    (startOff startBits : Nat)
    (q : Zlib.Inffast.L) : Prop :=
  ∃ off,
    q.in_ = .ref ctx.inputRef off ∧
    startOff ≤ off ∧
    q.bits.toNat + 8 * startOff ≤ startBits + 8 * off

/-- The source registers establish the accounting relation at entry. -/
theorem FastInputAccount.initial
    {ctx : FastLoopContext} {q : Zlib.Inffast.L}
    {off : Nat}
    (cursor : q.in_ = .ref ctx.inputRef off) :
    FastInputAccount ctx off q.bits.toNat q := by
  exact ⟨off, cursor, Nat.le_refl _, Nat.le_refl _⟩

/-- One nonbreaking actual body preserves loop-wide input accounting.
The broken branch still needs its cursor frame. -/
theorem FastLoopReady.body_input_account
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L} {startOff startBits : Nat}
    (ready : FastLoopReady ctx h q)
    (account : FastInputAccount ctx startOff startBits q) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h =
        .ok (result, after) ∧
      (result.broke = false →
        FastInputAccount ctx startOff startBits result) := by
  obtain ⟨off, used, result, after, cursor, usedBound,
    run, bitBudget, nextCursor⟩ :=
    ready.body_bit_account
  obtain ⟨oldOff, oldCursor, lower, oldBudget⟩ :=
    account
  have same : off = oldOff := by
    rw [oldCursor] at cursor
    cases cursor
    rfl
  subst oldOff
  refine ⟨result, after, run, ?_⟩
  intro notBroken
  refine ⟨off + used, nextCursor notBroken,
    by omega, ?_⟩
  omega

/-- A true continuation result cannot come from a source `break`. -/
theorem fastLoopCond_true_not_broken
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L}
    (condition : fastLoopCond ctx q h =
      .ok ((true, q), h)) :
    q.broke = false := by
  cases flag : q.broke
  · rfl
  · simp [fastLoopCond, flag] at condition

/-- The existing actual step proof and the bit-source accounting theorem
agree on the same body result. A continuing step retains both invariants. -/
theorem FastLoopReady.step_input_account
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L} {startOff startBits : Nat}
    (ready : FastLoopReady ctx h q)
    (account : FastInputAccount ctx startOff startBits q) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h =
        .ok (result, after) ∧
      ((fastLoopCond ctx result after =
          .ok ((false, result), after) ∧
          FastLoopExit ctx after result) ∨
       (fastLoopCond ctx result after =
          .ok ((true, result), after) ∧
          FastLoopReady ctx after result ∧
          FastInputAccount ctx startOff startBits result ∧
          fastLoopMeasure ctx result < fastLoopMeasure ctx q)) := by
  obtain ⟨result, after, bodyRun, outcome⟩ :=
    ready.step
  obtain ⟨accountResult, accountAfter,
    accountRun, maintained⟩ :=
    ready.body_input_account account
  have same : (result, after) =
      (accountResult, accountAfter) := by
    have eq := bodyRun.symm.trans accountRun
    exact Except.ok.inj eq
  cases same
  refine ⟨result, after, bodyRun, ?_⟩
  rcases outcome with stopped | ⟨condition, next,
    decrease⟩
  · exact Or.inl stopped
  · exact Or.inr ⟨condition, next,
      maintained (fastLoopCond_true_not_broken condition),
      decrease⟩

end Zlib.Inflate.Proofs
