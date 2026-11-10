import ZlibF.Proof.«inflate.c.header-code-credited-resume»
namespace Zlib.Inflate.Proofs.ActualHeader
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The result of real alphabet progress, carrying actual runs and
source-trace outputs. No source parser postcondition is a premise. -/
def AlphabetSourceOutcome (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l : IL) (bs : List UInt8) (received : List Bool)
    (data : CountReadSource s received bs) : Prop :=
    (∃ regs state used, used ≤ bs.length ∧
      runX (inflate_LENLENS c) l h = .ok ((.error Ex.leave, regs), setI h zs state) ∧
      DefaultOriginState (setI h zs state) r zs z state ∧ DispatchBuffers (setI h zs state) r regs (bs.drop used) ∧
      LenlensProgress state regs.hold regs.bits (received ++ bytesBits (bs.take used)) ∧
      ∃ next : CountReadSource state (received ++ bytesBits (bs.take used)) (bs.drop used), next.body = data.body) ∨
    (∃ (regs : IL) (after : Heap), runX (inflate_LENLENS c) l h = .ok ((.ok (), {regs with ret := -1}), after)) ∨
    (∃ event : AlphabetSeed c h r zs z s l bs received,
      Nonempty (CodeSourceTrace r zs (setI h zs event.state) z event.state {event.regs with ret := 0}
        (bs.drop event.used) (Zlib.Inftrees.Proofs.lensOf (fun k => (event.filled.lens.getD k 0).toNat) 19)))

theorem CountReadSource.actual_progress
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {received : List Bool}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LENLENS)
    (progress : LenlensProgress s l.hold l.bits received) (data : CountReadSource s received bs) :
    AlphabetSourceOutcome c h r zs z s l bs received data := by
  unfold AlphabetSourceOutcome
  by_cases short : (stream l bs).length < 3 * (s.ncode.toNat - s.«have».toNat)
  · exact Or.inl (actual_alphabet_wait E origin buffers mode progress data short)
  · rcases actual_alphabet_seed E origin buffers mode progress (by omega) with rejected | accepted
    · exact Or.inr (Or.inl rejected)
    · obtain ⟨event⟩ := accepted
      exact Or.inr (Or.inr ⟨event, ⟨.seed data event⟩⟩)

/-- Start the cumulative source trace from the real TABLE read, including
all actual shortage/rejection cases. Neither CountReadSource nor a desired
HeaderSourcePrefix is requested from this caller. -/
theorem table_actual_source_progress
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (origin : DefaultOriginState h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE) :
    ∃ observation : TableBranchObservation c h r zs z s l bs,
      (observation.outcome = .error Ex.leave) ∨
      (∃ i, strTable[i]? = some "too many length or distance symbols" ∧
        runX (inflate_TABLE c) l h = .ok ((.ok (), tableRegs observation.pulled), tcBadHeap h r zs z (tableCounts s observation.pulled.hold) i)) ∨
      (let state := {tableCounts s observation.pulled.hold with «have» := 0, mode := LENLENS}
       ∃ data : CountReadSource state
          (natBits (tableRegs observation.pulled).bits.toNat (tableRegs observation.pulled).hold.toNat)
          (bs.drop observation.used),
        data.body = stream l bs ∧
        runX (inflate_TABLE c) l h = runX (inflate_LENLENS c) (tableRegs observation.pulled) (setI h zs state) ∧
        AlphabetSourceOutcome c (setI h zs state) r zs z state (tableRegs observation.pulled) (bs.drop observation.used)
          (natBits (tableRegs observation.pulled).bits.toNat (tableRegs observation.pulled).hold.toNat) data) := by
  obtain ⟨observation⟩ := table_branch_classifier E origin buffers mode
  refine ⟨observation, ?_⟩
  rcases observation.kinds with normal | waiting
  · rcases observation.normal normal with rejected | accepted
    · exact Or.inr (Or.inl rejected)
    · rcases table_count_read_source observation normal with rejected | counts
      · exact Or.inr (Or.inl rejected)
      obtain ⟨data, body⟩ := counts
      obtain ⟨current, packet, progress, _reads, actual, _outcome⟩ := accepted
      have env : Env c _ r zs z _ := ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
      exact Or.inr (Or.inr ⟨data, body, actual, data.actual_progress env current packet rfl progress⟩)
  · exact Or.inl waiting

#print axioms CountReadSource.actual_progress
#print axioms table_actual_source_progress
end Zlib.Inflate.Proofs.ActualHeader
