import ZlibF.Proof.«inflate.c.fast-view-break-account-invariant»
import ZlibF.Proof.«inflate.c.fast-view-writeback-rollback-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual distance-too-far error branch preserves the call-entry
input account and admits the translated whole-byte rollback. This is the
`copyMatch` leaf; its length and distance callers remain to be composed. -/
theorem FastInputPacket.copyMatch_invalid_rollback
    {ctx : FastLoopContext} {h : Heap} {slow : IL}
    {bs : List UInt8} {l : Zlib.Inffast.L}
    {startOff startBits : Nat}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h ctx.r ctx.zs ctx.z ctx.s)
    (buffers : DispatchBuffers h ctx.r slow bs)
    (account : FastInputAccount ctx startOff startBits l)
    (initialBits : startBits < 8)
    (windowBranch : l.dist > l.op)
    (invalidBack : l.dist - l.op > ctx.c.whave)
    {output : Array UInt8}
    (outputGet : Space.get h ctx.dest = some output)
    (outputWrite : Space.ro h ctx.dest = false) :
    let result := { l with op := l.dist - l.op, broke := true }
    ∃ after off input,
      C.run (Zlib.Inffast.copyMatch ctx.c l) h =
        .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      result.in_ = .ref ctx.inputRef off ∧
      Space.get after ctx.inputRef = some input ∧
      startOff ≤ off - (result.bits >>> 3).toNat ∧
      C.run (Zlib.Inffast.subn result.in_
        (result.bits >>> 3)) after =
        .ok (.ref ctx.inputRef
          (off - (result.bits >>> 3).toNat), after) := by
  dsimp only
  obtain ⟨i, after, run, heapEq, finalPacket, finalJ,
    finalBuffers, sizes, outputAfter, writableAfter⟩ :=
    packet.copyMatch_invalid_default_state invariant buffers
      ctx.streamPtr ctx.statePtr windowBranch invalidBack
      outputGet outputWrite
  let result : Zlib.Inffast.L :=
    { l with op := l.dist - l.op, broke := true }
  have final : FastLoopExit ctx after result :=
    ⟨slow, bs, { ctx.z with msg := .ref (.str i) 0 },
      { ctx.s with mode := BAD }, finalPacket, finalJ,
      finalBuffers⟩
  have finalAccount : FastInputAccount ctx startOff
      startBits result :=
    account.no_pull rfl (Nat.le_refl _)
  obtain ⟨off, input, cursor, inputGet, lower,
    rollback⟩ :=
    final.rollback_accounted finalAccount initialBits
  exact ⟨after, off, input, run, final, cursor,
    inputGet, lower, rollback⟩

end Zlib.Inflate.Proofs
