import ZlibF.Proof.«inflate.c.fast-future-loop-run-cursor»
import ZlibF.Proof.«inflate.c.payload-semantic-loop-prefix»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The final physical cursor, not an existential span from the last token,
indexes exactly the written output prefix. This includes EOB exits. -/
theorem FastFutureExitCursor.output_prefix_at_cursor
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L}
    (exit : FastFutureExitCursor ctx L D dict future tail target h q) :
    ∃ (array : Array UInt8) (off : Nat) (next : List UInt8),
      q.out = .ref ctx.dest off ∧
      Space.get h ctx.dest = some array ∧
      ZlibF.Math.LZ77Copy.writtenBytes array off (off - ctx.bg) = next ∧
      next <+: target := by
  rcases exit with ⟨_, before, beforeLocal, beforeReady, bodyRun,
    slow, bs, array, k, made, next, done, input, history,
    packet, get, token, bytes, beginLe, out, continuation,
    terminal⟩
  refine ⟨array, k + made, next, out, get, ?_, ?_⟩
  · have count : k + made - ctx.bg = (k - ctx.bg) + made := by omega
    rw [count]
    exact bytes
  · cases done with
    | false => exact symbols_output_prefix (continuation rfl)
    | true => rw [(terminal rfl).2.1]; exact List.prefix_refl _

/-- The whole translated fast loop returns an exact physical output prefix
of the independent block result, for an arbitrary fixed future suffix. -/
theorem FastFutureReady.run_output_prefix_at_cursor
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastFutureReady ctx L D dict future tail target h q) :
    ∃ result after array off next,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      result.out = .ref ctx.dest off ∧
      Space.get after ctx.dest = some array ∧
      ZlibF.Math.LZ77Copy.writtenBytes array off (off - ctx.bg) = next ∧
      next <+: target := by
  obtain ⟨result, after, run, exit⟩ := ready.run_with_output_cursor
  obtain ⟨array, off, next, cursor, get, bytes, outputPrefix⟩ :=
    exit.output_prefix_at_cursor
  exact ⟨result, after, array, off, next,
    run, cursor, get, bytes, outputPrefix⟩

#print axioms FastFutureExitCursor.output_prefix_at_cursor
#print axioms FastFutureReady.run_output_prefix_at_cursor
end Zlib.Inflate.Proofs
