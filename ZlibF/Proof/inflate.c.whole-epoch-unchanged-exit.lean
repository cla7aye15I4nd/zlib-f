import ZlibF.Proof.«inflate.c.whole-epoch-dispatch-interface»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- An actual immediate exit that changes neither heap nor registers
retains every source, physical-output and counter observation. -/
theorem EpochCallCut.unchanged_exit
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8} {exit : Ex}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (actual : runX (inflate_dispatch c) l h = .ok ((.error exit, l), h)) :
    Nonempty (DispatchResult before) := by
  let cut := before.framed.cut
  let terminal : WholeWrapper.WrapperTerminal c entryHeap h r zs entryZ z s l base raw exit := {
    used := cut.used
    usedBound := cut.usedBound
    emitted := cut.emitted
    word := cut.word
    env := cut.env
    origin := cut.origin
    allocator := cut.allocator
    wrapperOrigins := cut.wrapperOrigins
    main := before.exit_main actual
    buffers := cut.buffers
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
    checksum := cut.checksum
    registers := before.framed.registers
  }
  exact ⟨.stopped h z s l exit actual {
    terminal := terminal
    outputStart := before.outputStart
    normalRet := fun early => before.normalRet
      (UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt32.lt_iff_toNat_lt.mp early)))
    allocationOracle := before.allocationOracle
  }⟩

/-- TYPE honours the real block/tree flush pause before reading another
tag or discarding final-block padding. No artificial public cut is added. -/
theorem EpochCallCut.type_flush_pause
    {c : Ctx} {entryHeap h : Heap} {r : ZStreamRef} {zs : Nat} {entryZ z : ZStream}
    {s : InflateState} {l : IL} {base : DataLog} {raw : List UInt8}
    (before : EpochCallCut c entryHeap h r zs entryZ z s l base raw)
    (mode : s.mode = TYPE) (pause : c.flush = Z_BLOCK ∨ c.flush = Z_TREES) :
    Nonempty (DispatchResult before) := by
  apply before.unchanged_exit
  rw [inflate_dispatch_block_type before.framed.cut.env l (Or.inl mode), ite_eq_left mode]
  exact inflate_TYPE_leave c l h pause

#print axioms EpochCallCut.unchanged_exit
#print axioms EpochCallCut.type_flush_pause
end Zlib.Inflate.Proofs.WholeEpoch
