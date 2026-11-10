import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface-v4»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- Only the explicit pre-BYTEBITS STORED constructor is not saved. -/
theorem SourcePhase4.saved_of_not_stored {log : DataLog} {s : InflateState} {wire : List Bool}
    (phase : SourcePhase4 log s wire) (mode : s.mode ≠ STORED) : phase.Saved := by
  cases phase with
  | rawStored _ stored _ _ _ _ => exact False.elim (mode stored)
  | _ => trivial

/-- A literal unchanged exit preserves the additive phase, including a
real parsed-but-unchecked MATCH pause when its saved guard is supplied. -/
theorem EpochCallCut4.unchanged_exit
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {exit : Ex}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (saved : before.phase.Saved)
    (actual : runX (inflate_dispatch c) l h = .ok ((.error exit, l), h)) :
    Nonempty (DispatchResult4 before) := by
  let facts : TerminalFacts4 c entryHeap h r zs entryZ z s l base raw exit := {
    before.facts with
    main := before.facts.exit_main actual
    normalRet := fun early => before.facts.normalRet
      (UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp early)))
  }
  exact ⟨.stopped h z s l exit actual ⟨facts, before.phase, before.materialized, saved⟩⟩

/-- A late ret-only source exit cannot publish a raw STORED cut, and
retains all other additive phases and actual heap/output observations. -/
theorem EpochCallCut4.ret_only_exit
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {exit : Ex} {rc : Int32}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (late : CHECK ≤ s.mode)
    (actual : runX (inflate_dispatch c) l h = .ok ((.error exit, {l with ret := rc}), h)) :
    Nonempty (DispatchResult4 before) := by
  let cut := before.facts
  let regs := {l with ret := rc}
  let facts : TerminalFacts4 c entryHeap h r zs entryZ z s regs base raw exit := {
    cut with
    main := cut.exit_main actual
    buffers := ⟨cut.buffers.input,
      ⟨cut.buffers.output.range, cut.buffers.output.nonnull, cut.buffers.output.count, cut.buffers.output.produced⟩,
      cut.buffers.separate, ⟨cut.buffers.bits.have_eq, cut.buffers.bits.next, cut.buffers.bits.hold_lt⟩⟩
    checksum := by
      intro lower upper
      obtain ⟨count, ledger⟩ := cut.checksum lower upper
      exact ⟨count, ⟨ledger.count, ledger.checksum, ledger.pending, ledger.physical⟩⟩
    registers := ⟨cut.registers.inputStart, cut.registers.noHeaderOutput⟩
    normalRet := by
      intro early
      have lower := UInt32.le_iff_toNat_le.mp late
      have upper := UInt32.lt_iff_toNat_lt.mp early
      omega
  }
  have notStored : (leaveState s l).mode ≠ STORED := by
    intro selected
    change s.mode = STORED at selected
    rw [selected] at late
    exact False.elim ((by decide : ¬ CHECK ≤ STORED) late)
  exact ⟨.stopped h z s regs exit actual
    ⟨facts, before.phase, before.materialized, before.phase.saved_of_not_stored notStored⟩⟩

/-- Additive terminal coverage includes MEM snapshots of either new
phase; no fabricated legacy SourcePhase is needed for these snapshots. -/
theorem EpochCallCut4.terminal_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DONE ∨ s.mode = BAD ∨ s.mode = MEM) :
    Nonempty (DispatchResult4 before) := by
  have terminal : TerminalMode s.mode := by
    rcases mode with done | bad | memory
    · exact Or.inl done
    · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (Or.inl memory))
  have actual := inflate_dispatch_terminal_run before.facts.env l terminal
  rcases mode with done | bad | memory
  · apply before.ret_only_exit (by rw [done]; decide)
    simpa [done, terminalExit, terminalRegs, DONE, BAD, MEM, SYNC] using actual
  · apply before.ret_only_exit (by rw [bad]; decide)
    simpa [bad, terminalExit, terminalRegs, DONE, BAD, MEM, SYNC] using actual
  · apply before.unchanged_exit
      (before.phase.saved_of_not_stored (by change s.mode ≠ STORED; rw [memory]; decide))
    simpa [memory, terminalExit, terminalRegs, DONE, BAD, MEM, SYNC] using actual

/-- The real TYPE block/tree pause remains unchanged in the additive
interface and cannot accidentally pause a raw STORED stage. -/
theorem EpochCallCut4.type_flush_pause
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut4 c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = TYPE) (pause : c.flush = Z_BLOCK ∨ c.flush = Z_TREES) :
    Nonempty (DispatchResult4 before) := by
  apply before.unchanged_exit
      (before.phase.saved_of_not_stored (by change s.mode ≠ STORED; rw [mode]; decide))
  rw [inflate_dispatch_block_type before.facts.env l (Or.inl mode), ite_eq_left mode]
  exact inflate_TYPE_leave c l h pause

#print axioms SourcePhase4.saved_of_not_stored
#print axioms EpochCallCut4.unchanged_exit
#print axioms EpochCallCut4.ret_only_exit
#print axioms EpochCallCut4.terminal_dispatch
#print axioms EpochCallCut4.type_flush_pause
end Zlib.Inflate.Proofs.WholeEpoch
