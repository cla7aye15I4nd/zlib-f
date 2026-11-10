import ZlibF.Proof.«inflate.c.whole-epoch-terminal-dispatch-v4»
import ZlibF.Proof.«inflate.c.data-dispatch»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Real pending literal and match waits do not alter the heap or local
registers. Unchecked and partially emitted MATCH retain their own phase. -/
 theorem EpochCallCut4.payload_output_wait
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = MATCH ∨ s.mode = LIT) (empty : l.left = 0) :
    Nonempty (DispatchResult4 before) := by
  have notStored : (leaveState s l).mode ≠ STORED := by
    change s.mode ≠ STORED
    rcases mode with matching | literal
    · rw [matching]; decide
    · rw [literal]; decide
  apply before.unchanged_exit (before.phase.saved_of_not_stored notStored)
  rcases mode with matching | literal
  · exact (inflate_dispatch_MATCH before.facts.env l matching).trans (inflate_MATCH_wait c h l empty)
  · exact (inflate_dispatch_LIT before.facts.env l literal).trans (inflate_LIT_full c l h empty)

#print axioms EpochCallCut4.payload_output_wait
end Zlib.Inflate.Proofs.WholeEpoch
