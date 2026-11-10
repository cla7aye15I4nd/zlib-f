import ZlibF.Proof.«inflate.c.payload-future-loop-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public ZlibF.Spec
open Zlib.Inffast.Spec
set_option autoImplicit false

private theorem copyBack_prefix (dict : List UInt8) (dist n : Nat)
    (history : List UInt8) :
    history <+: copyBack dict dist n history := by
  induction n generalizing history with
  | zero => exact List.prefix_refl _
  | succ n ih => exact (List.prefix_append _ _).trans (ih _)

/-- Output represented by a valid remaining block is a prefix of its
completion, including a back-reference that overlaps itself. -/
theorem future_symbols_output_prefix
    {L D : List Nat} {dict history : List UInt8}
    {input tail : List Bool} {target : List UInt8}
    (parsed : Symbols L D dict history input tail target) :
    history <+: target := by
  induction parsed with
  | eob => exact List.prefix_refl _
  | lit _ _ _ ih => exact (List.prefix_append _ _).trans ih
  | copy _ _ _ _ _ _ _ _ _ ih =>
      exact (copyBack_prefix _ _ _ _).trans ih

/-- The bytes held in the final physical output array are an exact prefix
of the independent block result, whether the loop stopped early or on EOB. -/
theorem FastFutureExit.output_prefix
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L}
    (exit : FastFutureExit ctx L D dict future tail target h q) :
    ∃ (array : Array UInt8) (k made : Nat),
      Space.get h ctx.dest = some array ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (k + made) ((k - ctx.bg) + made) <+: target := by
  rcases exit with ⟨_, before, beforeLocal, incoming, body, slow, bs, array, k, made, next,
    done, input, history, packet, get, token, bytes, continuation,
    terminal⟩
  refine ⟨array, k, made, get, ?_⟩
  rw [bytes]
  cases done with
  | false => exact future_symbols_output_prefix (continuation rfl).2
  | true => rw [(terminal rfl).2.1]; exact List.prefix_refl _

/-- The actual loop's final byte prefix is compatible with the parsed
block output. -/
theorem FastFutureReady.run_output_prefix
    {ctx : FastLoopContext} {L D : List Nat} {dict : List UInt8}
    {future tail : List Bool} {target : List UInt8}
    {h : Heap} {q : Zlib.Inffast.L}
    (semantic : FastFutureReady ctx L D dict future tail target h q) :
    ∃ result after array k made,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      Space.get after ctx.dest = some array ∧
      ZlibF.Math.LZ77Copy.writtenBytes array
        (k + made) ((k - ctx.bg) + made) <+: target := by
  obtain ⟨result, after, run, final⟩ := semantic.run
  obtain ⟨array, k, made, get, outputPrefix⟩ := final.output_prefix
  exact ⟨result, after, array, k, made, run, final.1, get, outputPrefix⟩

#print axioms future_symbols_output_prefix
#print axioms FastFutureExit.output_prefix
#print axioms FastFutureReady.run_output_prefix
end Zlib.Inflate.Proofs
