import ZlibF.Proof.«inflate.c.whole-head-reject-call-cut»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch
set_option autoImplicit false
set_option maxHeartbeats 1800000

inductive HeadNormalResult
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : FramedCallCut c entryHeap h r zs entryZ z s l base raw)
    (event : ByteWordRead h l (raw.drop before.cut.used)
      (sourceLog (callLog base raw before.cut.used before.cut.emitted)).input [] 16) : Type
  | accepted (cmf flg : UInt8)
      (bytes : (sourceLog (callLog base raw before.cut.used before.cut.emitted)).input ++
        (raw.drop before.cut.used).take event.used = [cmf, flg])
      (word : event.regs.hold.toNat = cmf.toNat + 256*flg.toNat)
      (valid : Zlib.HeaderOK cmf flg)
      (cut : FramedCallCut c entryHeap (headHeap h r zs z s event.regs) r zs entryZ
        {z with adler := 1} (headDefaultState s event.regs) (headRegs event.regs) base raw)
  | rejected
      (source : HeadBadSource c h r zs z s l (raw.drop before.cut.used)
        (sourceLog (callLog base raw before.cut.used before.cut.emitted)) event)
      (cut : FramedCallCut c entryHeap (badHeap h r zs z s source.message) r zs entryZ
        {z with msg := .ref (.str source.message) 0} {s with mode := BAD} source.regs base raw)

/-- Exhaustive actual cumulative HEAD progress. All actual bytes are
classified without a HeaderOK, successful return, or desired phase premise. -/
theorem head_call_exhaustive
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : FramedCallCut c entryHeap h r zs entryZ z s l base raw) (mode : s.mode = HEAD) :
    ∃ event : ByteWordRead h l (raw.drop before.cut.used)
      (sourceLog (callLog base raw before.cut.used before.cut.emitted)).input [] 16,
      (event.outcome = .error Ex.leave → Nonempty (WrapperTerminal c entryHeap h r zs entryZ z s event.regs base raw Ex.leave)) ∧
      (event.outcome = .ok () → Nonempty (HeadNormalResult before event)) := by
  obtain ⟨event, waiting, normal⟩ := head_call_progress before mode
  refine ⟨event, waiting, ?_⟩
  intro complete
  obtain ⟨cmf, flg, bytes, word, accepted⟩ := normal complete
  rcases head_normal_source_classification before.cut.env before.cut.wrapperOrigins before.cut.origin.header mode event complete bytes word with valid | bad
  · obtain ⟨cut⟩ := accepted valid
    exact ⟨.accepted cmf flg bytes word valid cut⟩
  · obtain ⟨source⟩ := bad
    obtain ⟨cut⟩ := head_rejected_call_cut before event source
    exact ⟨.rejected source cut⟩

#print axioms head_call_exhaustive
end Zlib.Inflate.Proofs.WholeWrapper
