import ZlibF.Proof.«inflate.c.call-safety»
import ZlibF.Proof.«inflate.c.call-refused»
import ZlibF.Proof.«inflate.c.default-public-memory-contract»
import ZlibF.Proof.«inflate.c.reset-default-state»
import ZlibF.Proof.«inflate.c.prime-default-state»
import ZlibF.Proof.«inflate.c.heap-call»

/-!
# inflate.c: the safety clause of one `inflate` call

`InflateCall` gives the frame and ledger of `StreamSequenceSafety` for an
`inflate` call: the written output prefix widens to the caller's whole output
region, the decoder's own blocks are the blocks `StreamOwned` names, and no
owned block is released.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- One `inflate` call with the conclusion of `Goal.inflate` satisfies the
per-call clause of `StreamSequenceSafety`. -/
theorem InflateCall.safe {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    {flush : Int32} (current : InflateInv h r i z s) (call : InflateCall h r i z s flush) :
    ∃ value after, (Call.inflate (some r) flush).execute default h = .ok ((value, default), after) ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨
          StreamHeaderRecord h r (.inflate (some r) flush) b)
        (StreamWriteRegions h r (.inflate (some r) flush)) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  obtain ⟨rc, after, z', s', used, out, run, next, accounting, _, _, _, _, _, _, _, _, _, _, _, _,
    frame, ledger, owned⟩ := call
  have regions : StreamWriteRegions h r (.inflate (some r) flush) =
      ⟨z.next_out, z.avail_out.toNat⟩ :: HeaderRegions h s.head := by
    simp only [StreamWriteRegions, current.good.live.hz, current.good.live.zst, current.good.live.hs]
  refine ⟨rc, after, heapCall_of_actual_run run default, ?_, ?_⟩
  · rw [regions]
    apply inflate_buffer_frame_mono (BufferFrame.widen_head frame accounting.2.1)
    intro b changed
    rcases changed with root | own | head
    · exact Or.inl root
    · exact Or.inr (Or.inl ((current.good.streamOwned_iff b).mpr own))
    · exact Or.inr (Or.inr (Or.inr ⟨z, i, s, current.good.live.hz, current.good.live.zst,
        current.good.live.hs, head, flush, rfl⟩))
  · intro b
    rw [ledger b]
    simp only []
    rw [current.good.streamOwned_iff b, next.good.streamOwned_iff b]
    constructor
    · rintro (⟨live, _⟩ | ⟨own, dead⟩)
      · exact Or.inl ⟨live, fun ⟨before, gone⟩ => gone (owned b before)⟩
      · exact Or.inr ⟨own, dead⟩
    · rintro (⟨live, _⟩ | ⟨own, dead⟩)
      · exact Or.inl ⟨live, id⟩
      · exact Or.inr ⟨own, dead⟩

#print axioms InflateCall.safe
end Zlib.Inflate.Proofs
