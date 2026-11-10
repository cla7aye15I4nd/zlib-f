import ZlibF.Proof.«inflate.c.slow-copy-fragment-consumer»
import ZlibF.Proof.«inflate.c.slow-fragment-wait-public»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowMatchCompletion
set_option autoImplicit false

/-- The independent actual-dispatch safety ledger bounds the parser's
MATCH-entry bit buffer on the same run. No final held-bit bound is assumed. -/
theorem parsed_match_bits_bound {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h heap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s ps : InflateState}
    {l parsed : IL} {bs : List UInt8} {future : List Bool} {used : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s)
    (initialMode : DataTableMode s.mode)
    (slow : s.mode = LEN_ ∨ s.mode = LEN → ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (point : ParsePoint p h s l bs future r zs z heap ps parsed used p.rest)
    (mode : ps.mode = MATCH) (positive : 0 < ps.length.toNat) (distance : 0 < ps.offset.toNat)
    (cut : runX (inflate_dispatch c) l h = runX (inflate_MATCH c) parsed heap) :
    parsed.bits.toNat ≤ max l.bits.toNat 22 := by
  obtain ⟨safeResult, safeRegs, safeHeap, safeStream, safeState, _safeUsed, _consumed, _made,
    _usedBound, _consumedBound, safeRun, _good, _data, _packet, _invariant, _sizes, _frame,
    _cursor, _count, _put, _source, _kind, bitBound⟩ :=
      inflate_dispatch_pending E good (fun _ => tables) buffers pending initialMode slow
  have parsedBuffers := point.buffers good buffers
  have env : Env c heap r zs z ps := ⟨E.strm, E.st, point.good.live.hz, point.good.live.hs⟩
  obtain ⟨result, regs, after, stream, state, _copied, actual, _good2, _data2, _bits2,
    _output2, _separate, _sizes2, _frame2, emit, _count2, _put2, _source2, _kind2, _ro, _residual⟩ :=
      inflate_MATCH_output_step_frame env point.good point.tables point.bits parsedBuffers.output
        parsedBuffers.separate mode positive distance (by rw [point.frame, pending.sane]; decide)
  have same := Except.ok.inj (safeRun.symm.trans (cut.trans actual))
  cases same
  rw [emit] at bitBound
  exact bitBound

#print axioms parsed_match_bits_bound
end Zlib.Inflate.Proofs.SlowInputFragment
