import ZlibF.Proof.«inflate.c.whole-epoch-ready-payload»
import ZlibF.Proof.«inflate.c.fast-committed-call-mode-v7»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch
set_option autoImplicit false

/-- The actual ready branch of the global source spine constructs the
complete no-future fast packet. All decoder/table/window/output premises
are unpacked from that spine, never added to public history. -/
theorem EpochCallCut.ready_fast_packet
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (epoch : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (boundary : Compressed (sourceLog (callLog base raw epoch.framed.cut.used epoch.framed.cut.emitted)).dictionary
      epoch.framed.cut.word (sourceLog (callLog base raw epoch.framed.cut.used epoch.framed.cut.emitted)).output)
    (mode : (leaveState s l).mode = LEN_ ∨ (leaveState s l).mode = LEN)
    (last : (leaveState s l).last = Int32.ofNat boundary.block.last)
    (selected : epoch.framed.cut.phase = .ready boundary mode last)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    Nonempty (FastCommittedCallCut c h r zs z s l (raw.drop epoch.framed.cut.used)
      boundary.L boundary.D boundary.block.wrapper.dictionary base.output epoch.framed.cut.emitted) := by
  have representation := epoch.ready_representation boundary mode last selected
  have metadata := epoch.framed.cut.tables
  rw [selected] at metadata
  change TableBinding h s boundary.L boundary.D at metadata
  have dataMode : DataTableMode s.mode := by
    rcases mode with mode | mode
    · exact Or.inl mode
    · exact Or.inr (Or.inl mode)
  have active : s.mode < CHECK := by
    rcases mode with mode | mode <;> change s.mode = _ at mode <;> rw [mode] <;> decide
  exact representation.restore_committed_fast_call_cut_v7 epoch.framed.cut.env dataMode
    metadata.2.2 metadata.2.1 (epoch.payload_history_view active) fast

#print axioms EpochCallCut.ready_fast_packet
end Zlib.Inflate.Proofs.WholeEpoch
