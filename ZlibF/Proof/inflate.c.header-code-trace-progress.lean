import ZlibF.Proof.«inflate.c.header-code-trace-contents»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- An actual reader event either exposes the separate empty-table source
case or extends the finite causal trace; no target prefix is supplied. -/
theorem CodeSourceTrace.read_progress
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (trace : CodeSourceTrace r zs h z s l bs alphabet)
    (event : CodeReadObservation c h r zs z s l bs alphabet) (mode : event.state.mode = CODELENS) :
    (∀ length ∈ alphabet, length = 0) ∨
      Nonempty (CodeSourceTrace r zs event.heap event.streamZ event.state event.regs (bs.drop event.used) alphabet) := by
  by_cases empty : ∀ length ∈ alphabet, length = 0
  · exact Or.inl empty
  · exact Or.inr ⟨.read trace event mode empty⟩

/-- Continue the actual accepted/rejected/waiting reader classification
using a produced source trace. Accepted output supplies the independent
Header packet without an input Header or successful-tail premise. -/
theorem CodeSourceTrace.classify_packet
    {c : Ctx} {h callHeap : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs credited history : List UInt8} {alphabet : List Nat}
    (trace : CodeSourceTrace r zs h z s l bs alphabet)
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s) (mode : s.mode = CODELENS)
    (allocator : DefAlloc z) (credit : WrapperGlue.AdlerCredit z s credited) (dictionary : InflateDictionary h s history)
    (incoming : l.bits.toNat ≤ 39)
    (main : runX (inflate_run c) IL.init callHeap = runX (xwhile (pure true) (inflate_dispatch c)) l h)
    (event : CodeReadObservation c h r zs z s l bs alphabet) :
    (∃ exit, event.outcome = .error exit ∧
      (event.state.mode = BAD ∨ (∀ length ∈ alphabet, length = 0) ∨
        Nonempty (CodeSourceTrace r zs event.heap event.streamZ event.state event.regs (bs.drop event.used) alphabet))) ∨
    (event.outcome = .ok () ∧ event.state.mode = BAD) ∨
    (event.outcome = .ok () ∧ event.state.mode = CODELENS ∧
      Nonempty (TailRejected c event.heap r zs event.streamZ event.state event.regs)) ∨
    Nonempty (AcceptedPacket c h callHeap r zs z s l bs alphabet credited history) := by
  obtain ⟨data⟩ := trace.prefix
  have lower : 256 < s.nlen.toNat := by rw [data.literalCount]; omega
  rcases event.classify_tail E.strm E.st lower with waiting | bad | complete
  · obtain ⟨exit, outcome⟩ := waiting
    refine Or.inl ⟨exit, outcome, ?_⟩
    rcases event.modes with code | bad
    · exact Or.inr (trace.read_progress event code)
    · exact Or.inl bad
  · exact Or.inr (Or.inl bad)
  · obtain ⟨normal, code, rejected | completed⟩ := complete
    · exact Or.inr (Or.inr (Or.inl ⟨normal, code, rejected⟩))
    · obtain ⟨ready, _parse, _validL, _validD, _actual⟩ := completed
      exact Or.inr (Or.inr (Or.inr
        (trace.accepted_packet E origin mode allocator credit dictionary incoming main event normal code ready)))

#print axioms CodeSourceTrace.read_progress
#print axioms CodeSourceTrace.classify_packet
end Zlib.Inflate.Proofs.ActualHeader
