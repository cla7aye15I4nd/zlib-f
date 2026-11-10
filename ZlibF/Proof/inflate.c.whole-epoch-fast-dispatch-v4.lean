import ZlibF.Proof.«inflate.c.whole-epoch-fast-ended-progress-v4»
namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.FunctionalEpoch Zlib.Inflate.Proofs.FastCommittedLoop
set_option autoImplicit false

/-- Every actual fast LEN run returns a complete next source cut: normal
accepted tokens, EOB into the next block/trailer, or causal BAD. It uses
no complete Symbols, future bytes, expected output or callee contract. -/
theorem EpochCallCut4.fast_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat}
    {entryZ z : ZStream} {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (epoch : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (boundary : Compressed (sourceLog (callLog base raw epoch.facts.used epoch.facts.emitted)).dictionary
      epoch.facts.word (sourceLog (callLog base raw epoch.facts.used epoch.facts.emitted)).output)
    (last : (leaveState s l).last = Int32.ofNat boundary.block.last)
    (mode : s.mode = LEN)
    (selected : epoch.phase = .legacy (.ready boundary (Or.inr mode) last))
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    Nonempty (DispatchResult4 epoch) := by
  have tables := epoch.materialized
  rw [selected] at tables
  let old := epoch.facts.with_legacy (.ready boundary (Or.inr mode) last) tables.1
  have representation := old.ready_representation boundary (Or.inr mode) last rfl
  have lower : TYPE ≤ s.mode := by rw [mode]; decide
  have active : s.mode < CHECK := by rw [mode]; decide
  obtain ⟨full⟩ := representation.restore_committed_fast_call_cut_v8 epoch.facts.env
    (Or.inr (Or.inl mode)) tables.1.2.2 tables.1.2.1 (old.payload_history_view active) fast
  rcases full.cut.loaded_mode_cases with ⟨normal, source, nextMode⟩ |
      ⟨ended, source, nextMode⟩ | ⟨bad, source, nextMode⟩
  · exact epoch.fast_normal_progress boundary last mode selected fast full normal source (nextMode.trans mode)
  · exact epoch.fast_eob_progress boundary last mode fast full ended source nextMode
  · exact epoch.fast_bad_progress boundary mode fast full bad source nextMode

#print axioms EpochCallCut4.fast_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
