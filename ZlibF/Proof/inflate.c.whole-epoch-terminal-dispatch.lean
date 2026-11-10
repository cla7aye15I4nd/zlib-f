import ZlibF.Proof.«inflate.c.whole-epoch-unchanged-exit»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- A late ret-only dispatcher exit retains the physical/source packet.
The late-mode condition rules out an invented early successful ret value. -/
theorem EpochCallCut.ret_only_exit
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {exit : Ex} {rc : Int32}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (late : CHECK ≤ s.mode)
    (actual : runX (inflate_dispatch c) l h = .ok ((.error exit, {l with ret := rc}), h)) :
    Nonempty (DispatchResult before) := by
  let cut := before.framed.cut
  let regs := {l with ret := rc}
  let terminal : WholeWrapper.WrapperTerminal c entryHeap h r zs entryZ z s regs base raw exit := {
    used := cut.used
    usedBound := cut.usedBound
    emitted := cut.emitted
    word := cut.word
    env := cut.env
    origin := cut.origin
    allocator := cut.allocator
    wrapperOrigins := cut.wrapperOrigins
    main := before.exit_main actual
    buffers := ⟨cut.buffers.input,
      ⟨cut.buffers.output.range, cut.buffers.output.nonnull, cut.buffers.output.count, cut.buffers.output.produced⟩,
      cut.buffers.separate,
      ⟨cut.buffers.bits.have_eq, cut.buffers.bits.next, cut.buffers.bits.hold_lt⟩⟩
    bits := cut.bits
    next := cut.next
    haveCount := cut.haveCount
    put := cut.put
    leftCount := cut.leftCount
    credited := cut.credited
    phase := cut.phase
    tables := cut.tables
    window := cut.window
    physical := cut.physical
    checksum := by
      intro lower upper
      obtain ⟨count, ledger⟩ := cut.checksum lower upper
      exact ⟨count, ⟨ledger.count, ledger.checksum, ledger.pending, ledger.physical⟩⟩
    registers := ⟨before.framed.registers.inputStart, before.framed.registers.noHeaderOutput⟩
  }
  exact ⟨.stopped h z s regs exit actual {
    terminal := terminal
    outputStart := before.outputStart
    normalRet := by
      intro early
      have lower := UInt32.le_iff_toNat_le.mp late
      have upper := UInt32.lt_iff_toNat_lt.mp early
      omega
    allocationOracle := before.allocationOracle
  }⟩

/-- DONE and BAD use ordinary leave with their actual ret assignments;
MEM preserves registers and performs the distinct direct error return. -/
theorem EpochCallCut.terminal_dispatch
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = DONE ∨ s.mode = BAD ∨ s.mode = MEM) :
    Nonempty (DispatchResult before) := by
  have terminal : TerminalMode s.mode := by
    rcases mode with done | bad | memory
    · exact Or.inl done
    · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (Or.inl memory))
  have actual := inflate_dispatch_terminal_run before.framed.cut.env l terminal
  rcases mode with done | bad | memory
  · apply before.ret_only_exit (by rw [done]; decide)
    simpa [done, terminalExit, terminalRegs, DONE, BAD, MEM, SYNC] using actual
  · apply before.ret_only_exit (by rw [bad]; decide)
    simpa [bad, terminalExit, terminalRegs, DONE, BAD, MEM, SYNC] using actual
  · apply before.unchanged_exit
    simpa [memory, terminalExit, terminalRegs, DONE, BAD, MEM, SYNC] using actual

#print axioms EpochCallCut.ret_only_exit
#print axioms EpochCallCut.terminal_dispatch
end Zlib.Inflate.Proofs.WholeEpoch
