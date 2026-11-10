import ZlibF.Proof.«inflate.c.header-count-credited-resume»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Cancel the untouched caller suffix from the actual CODELENS source
observation. Only consumed bytes enter the shared credited-input ledger. -/
theorem CodeReadObservation.ordinary_held_credit
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {alphabet : List Nat}
    (event : CodeReadObservation c h r zs z s l bs alphabet)
    (mode : event.state.mode = CODELENS) (ordinary : ¬ ∀ length ∈ alphabet, length = 0) :
    ∃ word, natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take event.used) =
        word ++ natBits event.regs.bits.toNat event.regs.hold.toNat ∧
      ZlibF.Math.CodeLengthPrefix.Trace alphabet (s.nlen.toNat + s.ndist.toNat)
        (actualLengthPrefix s) word (actualLengthPrefix event.state) := by
  rcases event.format with empty | full
  · exact False.elim (ordinary empty.2.1)
  obtain ⟨word, source, parser⟩ := full.1 (by rw [mode]; decide)
  refine ⟨word, ?_, parser⟩
  apply (List.append_left_inj (bytesBits (bs.drop event.used))).mp
  have split : bytesBits bs = bytesBits (bs.take event.used) ++ bytesBits (bs.drop event.used) := by
    rw [← bytesBits_append, List.take_append_drop]
  simpa only [stream, split, List.append_assoc] using source

/-- Advance the actual parser trace and the global exact input ledger in
one source-derived step. The separate malformed empty-alphabet case is
explicit; no parser result or consumed word is requested as a premise. -/
theorem CodeSourceTrace.read_source_credit
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs input : List UInt8} {alphabet : List Nat} {committed : List Bool}
    (trace : CodeSourceTrace r zs h z s l bs alphabet)
    (before : CausalInput.Credited input committed l.bits l.hold)
    (event : CodeReadObservation c h r zs z s l bs alphabet) (mode : event.state.mode = CODELENS) :
    (∀ length ∈ alphabet, length = 0) ∨
      ∃ word, CausalInput.Credited (input ++ bs.take event.used) (committed ++ word) event.regs.bits event.regs.hold ∧
        natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take event.used) =
          word ++ natBits event.regs.bits.toNat event.regs.hold.toNat ∧
        Nonempty (CodeSourceTrace r zs event.heap event.streamZ event.state event.regs (bs.drop event.used) alphabet) := by
  by_cases empty : ∀ length ∈ alphabet, length = 0
  · exact Or.inl empty
  · obtain ⟨word, source, _parser⟩ := event.ordinary_held_credit mode empty
    exact Or.inr ⟨word, before.append source, source, ⟨.read trace event mode empty⟩⟩

#print axioms CodeReadObservation.ordinary_held_credit
#print axioms CodeSourceTrace.read_source_credit
end Zlib.Inflate.Proofs.ActualHeader
