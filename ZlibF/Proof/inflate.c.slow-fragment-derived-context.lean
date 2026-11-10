import ZlibF.Proof.«inflate.c.slow-fragment-bit-bound»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- Every persistent syntax phase is an actual active payload mode. -/
theorem PendingSyntax.data_mode {L D : List Nat} {p : CopySyntax L D} {s : InflateState} {residual : List Bool}
    (phase : PendingSyntax p s residual) : DataTableMode s.mode := by
  cases phase with
  | len selected => rcases selected with mode | mode <;> rw [mode] <;> unfold DataTableMode <;> decide
  | lenext mode _ _ _ => rw [mode]; unfold DataTableMode; decide
  | dist mode _ _ _ => rw [mode]; unfold DataTableMode; decide
  | distext mode _ _ _ _ _ => rw [mode]; unfold DataTableMode; decide
  | matching mode _ _ _ _ => rw [mode]; unfold DataTableMode; decide

/-- A valid physical distance into the initial call prefix remains valid
at the parsed MATCH cut. Parsing has emitted no output or changed saved
window bytes. The generic buffer view is produced from public CallerRange. -/
theorem ParsePoint.match_context {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h heap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s ps : InflateState}
    {l parsed : IL} {bs dict : List UInt8} {future : List Bool} {used : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (buffers : DispatchBuffers h r l bs)
    (dictionary : InflateDictionary h s dict)
    (point : ParsePoint p h s l bs future r zs z heap ps parsed used p.rest)
    (mode : ps.mode = MATCH)
    (available : distBases.getD p.distanceSymbol 0 + p.distanceValue ≤ dict.length + (l.out_.toNat - l.left.toNat)) :
    Env c heap r zs z ps ∧ InflateDictionary heap ps dict ∧ DispatchBuffers heap r parsed (bs.drop used) ∧
    ps.offset.toNat ≤ dict.length + (parsed.out_.toNat - parsed.left.toNat) := by
  obtain ⟨_was, _remaining, offset, _back⟩ := SlowMatchCompletion.pending_matching_fields mode point.phase
  refine ⟨⟨E.strm, E.st, point.good.live.hz, point.good.live.hs⟩, ?_, point.buffers good buffers, ?_⟩
  · rw [point.heap]
    exact SlowCopyTokenPath.dictionary_decode_frame dictionary point.frame
  · rw [offset, point.shape]
    exact available

#print axioms PendingSyntax.data_mode
#print axioms ParsePoint.match_context
end Zlib.Inflate.Proofs.SlowInputFragment
