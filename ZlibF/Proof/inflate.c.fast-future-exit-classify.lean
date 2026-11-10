import ZlibF.Proof.«inflate.c.fast-future-loop-output-prefix-cursor»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- At the actual final cursor, a fast exit either retains a future-aware
independent block continuation or has written the exact block target on EOB. -/
theorem FastFutureExitCursor.classify
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L}
    (exit : FastFutureExitCursor ctx L D dict future tail target h q) :
    ∃ (slow : IL) (bs : List UInt8) (array : Array UInt8)
      (off : Nat) (next : List UInt8),
      FastInputPacket h slow bs q ∧
      q.out = .ref ctx.dest off ∧
      Space.get h ctx.dest = some array ∧
      ZlibF.Math.LZ77Copy.writtenBytes array off (off - ctx.bg) = next ∧
      (Symbols L D dict next (stream slow bs ++ future) tail target ∨
        (next = target ∧ stream slow bs ++ future = tail ∧
          q.broke = true)) := by
  rcases exit with ⟨_, before, beforeLocal, beforeReady, bodyRun,
    slow, bs, array, k, made, next, done, input, history,
    packet, get, token, bytes, beginLe, out, continuation,
    terminal⟩
  refine ⟨slow, bs, array, k + made, next, packet, out, get, ?_, ?_⟩
  · have count : k + made - ctx.bg = (k - ctx.bg) + made := by omega
    rw [count]
    exact bytes
  · cases done with
    | false => exact Or.inl (continuation rfl)
    | true =>
        have last := terminal rfl
        exact Or.inr ⟨last.2.1, last.1, last.2.2.1⟩

#print axioms FastFutureExitCursor.classify
end Zlib.Inflate.Proofs
