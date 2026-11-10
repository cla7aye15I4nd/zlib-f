import ZlibF.Proof.«inflate.c.payload-loop-token-cursor-stage»
import ZlibF.Proof.«inffast.c.dist-two-pull-ledger»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The semantic byte count and the safety byte count agree when both
are produced by the same real fast-body result. This only uses the physical
input pointer offset; repeated input bytes are harmless. -/
theorem FastInputPacket.same_used_of_actual_cursor
    {h after : Heap} {slow slowAfter : IL} {raw rawAfter : List UInt8}
    {entry result : Zlib.Inffast.L}
    (packet : FastInputPacket h slow raw entry)
    (afterPacket : FastInputPacket after slowAfter rawAfter result)
    {inputRef : BRef} {off usedSem usedSafety : Nat}
    (start : slow.next = .ref inputRef off)
    (semantic : result.in_ = inputAdvance entry.in_ usedSem)
    (safety : slowAfter.next = inputAdvance slow.next usedSafety) :
    usedSem = usedSafety := by
  apply Zlib.Inffast.Proofs.input_count_eq_of_cursor
    (finish := result.in_) (ref := inputRef) (start := off)
  · rw [semantic, packet.cursor, start]
  · rw [afterPacket.cursor, safety, start]

#print axioms FastInputPacket.same_used_of_actual_cursor
end Zlib.Inflate.Proofs

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate.Spec Zlib.Inffast.Spec
set_option autoImplicit false

/-- After count alignment, the two proof-side slow states describe the
same unread bit stream because both are synchronized to the actual result. -/
theorem FastInputPacket.same_stream_of_same_result
    {h : Heap} {raw : List UInt8} {result : Zlib.Inffast.L}
    {semanticSlow safetySlow : IL} {semanticUsed safetyUsed : Nat}
    (semantic : FastInputPacket h semanticSlow
      (raw.drop semanticUsed) result)
    (safety : FastInputPacket h safetySlow
      (raw.drop safetyUsed) result)
    (count : semanticUsed = safetyUsed) :
    stream semanticSlow (raw.drop semanticUsed) =
      stream safetySlow (raw.drop safetyUsed) := by
  subst safetyUsed
  have bits : semanticSlow.bits = safetySlow.bits :=
    semantic.bits.symm.trans safety.bits
  have hold : semanticSlow.hold = safetySlow.hold :=
    semantic.hold.symm.trans safety.hold
  simp only [stream, bits, hold]

#print axioms FastInputPacket.same_stream_of_same_result
end Zlib.Inflate.Proofs
