import ZlibF.Proof.«inflate.c.fast-view-break-account-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- Proof-side expression for the registers after the fast body's two
translated input pulls. -/
def fastTwoPulls (slow : IL) (first second : UInt8)
    (l : Zlib.Inffast.L) : Zlib.Inffast.L :=
  let next1 := inputAdvance slow.next 1
  let next2 := inputAdvance next1 1
  Zlib.Inffast.Proofs.pullL
    (Zlib.Inffast.Proofs.pullL l first next1)
    second next2

/-- The two source pulls retain caller byte views and call-entry input
accounting. Their result is the explicit `fastTwoPulls` register value. -/
theorem FastInputPacket.two_pulls_account_default_state
    {h : Heap} {slow : IL}
    {first second : UInt8} {rest : List UInt8}
    {l : Zlib.Inffast.L}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {ctx : FastLoopContext}
    {startOff startBits off : Nat}
    (packet : FastInputPacket h slow
      (first :: second :: rest) l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow
      (first :: second :: rest))
    (account : FastInputAccount ctx startOff startBits l)
    (small : slow.bits.toNat < 15)
    (cursor : l.in_ = .ref ctx.inputRef off) :
    ∃ fast1 fast2 slow2,
      C.run (Zlib.Inffast.pull l) h = .ok (fast1, h) ∧
      C.run (Zlib.Inffast.pull fast1) h = .ok (fast2, h) ∧
      fast2 = fastTwoPulls slow first second l ∧
      FastInputPacket h slow2 rest fast2 ∧
      DispatchBuffers h r slow2 rest ∧
      FastInputAccount ctx startOff startBits fast2 ∧
      16 ≤ slow2.bits.toNat ∧
      slow2.bits.toNat ≤ 30 ∧
      stream slow2 rest =
        stream slow (first :: second :: rest) := by
  obtain ⟨next1, fast1, slow1, pull1, next1Eq,
    slow1Eq, fast1Eq, packet1, _, buffers1,
    stream1⟩ :=
    packet.pull_default_state invariant buffers (by omega)
  have cursor1 : fast1.in_ =
      .ref ctx.inputRef (off + 1) := by
    rw [packet1.cursor, slow1Eq, pulled, next1Eq]
    have old : slow.next = .ref ctx.inputRef off :=
      packet.cursor.symm.trans cursor
    rw [old]
    rfl
  have account1 : FastInputAccount ctx startOff
      startBits fast1 := by
    exact account.advance_from_stream (used := 1)
      (consumed := 0) packet packet1 cursor cursor1
      (by simp) (by simpa using stream1)
  have small1 : slow1.bits.toNat ≤ 22 := by
    rw [slow1Eq]
    change (slow.bits + 8).toNat ≤ 22
    rw [u32_add8 slow.bits (by omega)]
    omega
  obtain ⟨next2, fast2, slow2, pull2, next2Eq,
    slow2Eq, fast2Eq, packet2, _, buffers2,
    stream2⟩ :=
    packet1.pull_default_state invariant buffers1 small1
  have cursor2 : fast2.in_ =
      .ref ctx.inputRef (off + 2) := by
    rw [packet2.cursor, slow2Eq, pulled, next2Eq]
    rw [packet1.cursor] at cursor1
    rw [cursor1]
    rfl
  have account2 : FastInputAccount ctx startOff
      startBits fast2 := by
    exact account1.advance_from_stream (used := 1)
      (consumed := 0) packet1 packet2 cursor1 cursor2
      (by simp) (by simpa using stream2)
  have exactFast : fast2 = fastTwoPulls slow first second l := by
    rw [fast2Eq, fast1Eq, next2Eq, slow1Eq,
      next1Eq]
    rfl
  have bits1 : slow1.bits.toNat = slow.bits.toNat + 8 := by
    rw [slow1Eq]
    exact u32_add8 slow.bits (by omega)
  have bits2 : slow2.bits.toNat = slow1.bits.toNat + 8 := by
    rw [slow2Eq]
    exact u32_add8 slow1.bits (by omega)
  refine ⟨fast1, fast2, slow2, pull1, pull2,
    exactFast, packet2, buffers2, account2,
    by omega, by omega, ?_⟩
  rw [stream2, stream1]

end Zlib.Inflate.Proofs
