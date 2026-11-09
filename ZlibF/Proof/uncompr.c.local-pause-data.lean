import ZlibF.Proof.«uncompr.c.local-pause-basic»
import ZlibF.Proof.«inflate.c.local-fast-caller»

namespace Zlib.Uncompr.Proof.LocalPause
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inflate.Local Zlib.Uncompr.Proof.InflatePause
set_option autoImplicit false

theorem match_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Zlib.Inflate.Local.LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = MATCH)
    (run : runX (inflate_MATCH c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  have facts := pending.matching mode
  by_cases empty : l.left = 0
  · have source := inflate_MATCH_wait c h l empty
    have same := xrun_state_eq source run E.hs get
    rw [←same]
    simp only [PauseGood, mode]
    decide
  · obtain ⟨dest, array, off, put, bytes, write, room, count, produced, privateWindow⟩ :=
      Zlib.Inflate.Local.callerRange_slow_output good l buffers.output.range buffers.output.nonnull buffers.output.count buffers.output.produced
    obtain ⟨outcome, _, _, stream, state, source, current, _, _, _, kinds⟩ :=
      Zlib.Inflate.Local.inflate_MATCH_boundary_ranges E good tables buffers.bits put bytes write mode facts.1 facts.2.2.2
        (by rw [pending.sane]; decide) room count produced privateWindow
        (buffers.bits.output_positions put empty buffers.separate)
    have selected := xrun_outcome_eq source run
    have same := xrun_state_eq source run current.live.hs get
    rcases kinds with ⟨_, _, _, eq⟩ | ⟨normal, _⟩ | ⟨normal, _⟩
    · rw [←same, eq]
      simp only [PauseGood, mode]
      decide
    · cases normal.symm.trans selected
    · cases normal.symm.trans selected

theorem lit_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Zlib.Inflate.Local.LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LIT)
    (run : runX (inflate_LIT c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  obtain ⟨outcome, _, _, state, source, current, _, _, _, _, _, _, _, _, kinds⟩ :=
    Zlib.Inflate.Local.inflate_LIT_step E good tables buffers.bits buffers.output buffers.separate
  have selected := xrun_outcome_eq source run
  have same := xrun_state_eq source run current.live.hs get
  rcases kinds with ⟨_, _, _, eq⟩ | ⟨normal, _⟩
  · rw [←same, eq]
    simp only [PauseGood, mode]
    decide
  · cases normal.symm.trans selected

theorem distext_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Zlib.Inflate.Local.LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = DISTEXT)
    (run : runX (inflate_DISTEXT c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  rcases Zlib.Inflate.Local.inflate_DISTEXT_pending_boundary E good tables buffers pending mode with wait | continued
  · obtain ⟨_, _, source, _⟩ := wait
    have same := xrun_state_eq source run E.hs get
    rw [←same]
    simp only [PauseGood, mode]
    decide
  · obtain ⟨current, heap, state, used, cut, _, currentGood, currentTables,
      packet, currentPending, nextMode, _⟩ := continued
    have env : Env c heap r zs z state := ⟨E.strm, E.st, currentGood.live.hz, currentGood.live.hs⟩
    exact match_leave_pause env currentGood currentTables packet currentPending nextMode (cut.symm.trans run) get

theorem dist_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Zlib.Inflate.Local.LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = DIST)
    (run : runX (inflate_DIST c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  have actualRun := run
  obtain ⟨lengthFacts, before, backBound, back⟩ := pending.dist mode
  rcases Zlib.Inflate.Local.inflate_DIST_lookup_boundary_bounded before E.st good tables buffers.bits back backBound with wait | continued
  · obtain ⟨regs, used, _, usedBound, run, inv, _, bits, shape, cursor, bitBound⟩ := wait
    have same := xrun_state_eq run actualRun good.live.hs get
    rw [←same]
    simp only [PauseGood, mode]
    decide
  · obtain ⟨regs, rootHeap, rootState, used, dropped, _, usedBound, droppedBound,
      sourceRun, rootGood, rootTables, rootInv, leaf, enough, rootBack, rootBits, rootShape,
      _, _, rootHeapEq, rootStateEq, rootCursor, rootBitBound⟩ := continued
    obtain ⟨leafRegs, leafHeap, leafState, consumeRun, leafGood, leafTables, leafInv,
      _, leafShape, leafHeapEq, leafStateEq, leafBits, leafCount, _, leafCursor⟩ :=
      Zlib.Inflate.Local.distFinish_consume_cursor before dropped E.st rootGood rootTables leaf rootBack backBound enough rootInv
    let codeBits := dropped + regs.here.bits.toNat
    have codeBound : codeBits ≤ 15 := by have := leaf.1; omega
    have parsed : Zlib.Inflate.Proofs.stream leafRegs (bs.drop used) =
        (Zlib.Inflate.Proofs.stream l bs).drop codeBits := by rw [leafBits, rootBits, List.drop_drop]
    have leafBitBound : leafRegs.bits.toNat ≤ max l.bits.toNat 22 := by rw [leafCount]; omega
    have leafHeapOriginal : leafHeap = setI h zs leafState := by rw [leafHeapEq, rootHeapEq, setI_setI]
    have leafFrame : DecodeStateFrame s leafState := by
      unfold DecodeStateFrame
      rw [leafStateEq, rootStateEq]
    have leafPacket : DispatchBuffers leafHeap r leafRegs (bs.drop used) := by
      apply dispatch_consume_local buffers good leafGood (by rw [leafFrame]) _ _ (rootShape.trans leafShape)
        (leafCursor.trans rootCursor) usedBound leafInv
      · intro ref
        rw [leafHeapOriginal, byte_view_get_setI]
      · intro ref
        rw [leafHeapOriginal, byte_view_ro_setI]
    have source : runX (inflate_DIST c) l h = runX (distLeafTail c regs.here) leafRegs leafHeap :=
      sourceRun.trans consumeRun
    rcases Zlib.Inflate.Local.distLeafTail_boundary_frame E.strm E.st leafGood leafTables leafInv leaf with invalid | valid
    · obtain ⟨_, _, _, source, _⟩ := invalid
      have impossible := xrun_outcome_eq (sourceRun.trans (consumeRun.trans source)) actualRun
      cases impossible
    · obtain ⟨baseHeap, baseState, classifyRun, baseGood, baseTables, baseInv, nextMode,
        baseHeapEq, baseStateEq, extra, lower, budget⟩ := valid
      have baseFrame : DecodeStateFrame s baseState := by
        unfold DecodeStateFrame
        rw [baseStateEq, leafStateEq, rootStateEq]
      have baseHeapOriginal : baseHeap = setI h zs baseState := by rw [baseHeapEq, leafHeapOriginal, setI_setI]
      have baseLength : PendingLengthSafe baseState := by
        rw [baseStateEq, leafStateEq, rootStateEq]
        exact lengthFacts
      have baseBack : baseState.back = Int32.ofNat (before + codeBits) := by
        rw [baseStateEq, leafStateEq]
        simp only [codeBits, Nat.add_assoc]
      have basePending := dataPendingInvariant_distext (by rw [baseFrame]; exact pending.sane) nextMode
        ⟨baseLength, extra, lower, budget, before + codeBits, by omega, baseBack⟩
      have basePacket : DispatchBuffers baseHeap r leafRegs (bs.drop used) := by
        apply dispatch_consume_local buffers good baseGood (by rw [baseFrame]) _ _ (rootShape.trans leafShape)
          (leafCursor.trans rootCursor) usedBound baseInv
        · intro ref
          rw [baseHeapOriginal, byte_view_get_setI]
        · intro ref
          rw [baseHeapOriginal, byte_view_ro_setI]
      have baseEnv : Env c baseHeap r zs z baseState := ⟨E.strm, E.st, baseGood.live.hz, baseGood.live.hs⟩
      exact distext_leave_pause baseEnv baseGood baseTables basePacket basePending nextMode
        ((source.trans classifyRun).symm.trans actualRun) get

theorem lenext_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Zlib.Inflate.Local.LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = LENEXT)
    (run : runX (inflate_LENEXT c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  rcases Zlib.Inflate.Local.inflate_LENEXT_pending_boundary E good tables buffers pending mode with wait | continued
  · obtain ⟨_, _, source, _⟩ := wait
    have same := xrun_state_eq source run E.hs get
    rw [←same]
    simp only [PauseGood, mode]
    decide
  · obtain ⟨current, heap, state, used, cut, _, currentGood, currentTables,
      packet, currentPending, nextMode, _⟩ := continued
    have env : Env c heap r zs z state := ⟨E.strm, E.st, currentGood.live.hz, currentGood.live.hs⟩
    exact dist_leave_pause env currentGood currentTables packet currentPending nextMode (cut.symm.trans run) get

theorem len_slow_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Zlib.Inflate.Local.LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = LEN)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (run : runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  have actualRun := run
  rcases Zlib.Inflate.Local.inflate_LEN_slow_lookup_boundary_mode E.st good tables buffers.bits slow with wait | continued
  · obtain ⟨regs, after, state, used, _, usedBound, run, finalGood, finalTables,
      inv, _, bits, shape, frame, bitBound, cursor, heapEq, modeEq⟩ := wait
    have same := xrun_state_eq run actualRun finalGood.live.hs get
    rw [←same]
    simp only [PauseGood, modeEq, mode]
    decide
  · obtain ⟨regs, rootHeap, rootState, used, dropped, _, usedBound, droppedBound, sourceRun,
      rootGood, rootTables, rootInv, leaf, enough, rootBack, rootBits, rootShape, rootFrame,
      _, rootBitBound, rootHeapEq, rootCursor⟩ := continued
    have backNat : rootState.back.toInt = dropped := by rw [rootBack]; exact back_ofNat_small dropped droppedBound
    obtain ⟨leafRegs, leafHeap, leafState, consumeRun, leafGood, leafTables, leafInv,
      leafFrame, leafShape, lengthEq, leafBack, leafBits, leafCount, _, leafHeapEq, leafCursor⟩ :=
      Zlib.Inflate.Local.lenFinish_consume_cursor dropped E.st rootGood rootTables leaf backNat enough rootInv
    let codeBits := dropped + regs.here.bits.toNat
    have codeBound : codeBits ≤ 15 := by have := leaf.1; omega
    have parsed : Zlib.Inflate.Proofs.stream leafRegs (bs.drop used) =
        (Zlib.Inflate.Proofs.stream l bs).drop codeBits := by rw [leafBits, rootBits, List.drop_drop]
    have leafBitBound : leafRegs.bits.toNat ≤ max l.bits.toNat 22 := by rw [leafCount]; omega
    have leafHeapOriginal : leafHeap = setI h zs leafState := by rw [leafHeapEq, rootHeapEq, setI_setI]
    have source : runX (inflate_LEN c) l h = runX (lenLeafTail c regs.here) leafRegs leafHeap :=
      sourceRun.trans consumeRun
    rcases Zlib.Inflate.Local.lenLeafTail_boundary_frame E.strm E.st leafGood leafTables leafInv leaf lengthEq with terminal | valid
    · obtain ⟨_, _, _, source, _⟩ := terminal
      have impossible := xrun_outcome_eq (sourceRun.trans (consumeRun.trans source)) actualRun
      cases impossible
    · obtain ⟨baseHeap, baseState, classifyRun, baseGood, baseTables, baseInv, nextMode,
        baseFrame, extra, lower, budget, retainedBack, baseHeapEq⟩ := valid
      have prefixFrame := rootFrame.trans (leafFrame.trans baseFrame)
      have baseHeapOriginal : baseHeap = setI h zs baseState := by rw [baseHeapEq, leafHeapOriginal, setI_setI]
      have basePending := dataPendingInvariant_lenext (by rw [prefixFrame]; exact pending.sane) nextMode
        ⟨extra, lower, budget, codeBits, codeBound, retainedBack.trans leafBack⟩
      have basePacket : DispatchBuffers baseHeap r leafRegs (bs.drop used) := by
        apply dispatch_consume_local buffers good baseGood (by rw [prefixFrame]) _ _ (rootShape.trans leafShape)
          (leafCursor.trans rootCursor) usedBound baseInv
        · intro ref
          rw [baseHeapOriginal, byte_view_get_setI]
        · intro ref
          rw [baseHeapOriginal, byte_view_ro_setI]
      have baseEnv : Env c baseHeap r zs z baseState := ⟨E.strm, E.st, baseGood.live.hz, baseGood.live.hs⟩
      exact lenext_leave_pause baseEnv baseGood baseTables basePacket basePending nextMode
        ((source.trans classifyRun).symm.trans actualRun) get

/-- Actual fast LEN always returns normally; its ordinary leave is the
proved slow decoder pause, whose full continuation is included. -/
theorem len_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN)
    (run : runX (inflate_LEN c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  by_cases fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · have active : DataTableMode s.mode := by rw [mode]; unfold DataTableMode; decide
    obtain ⟨_, _, _, _, _, _, _, source, _⟩ := Zlib.Inflate.Local.inflate_LEN_fast_view_step E invariant buffers mode fast
    have impossible := xrun_outcome_eq source run
    cases impossible
  · exact len_slow_leave_pause E invariant.good (invariant.tables (by rw [mode]; unfold DataTableMode; decide))
      buffers invariant.pending mode fast run get

/-- Actual LEN_ mode normalization precedes that same real LEN call. -/
theorem len_start_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = LEN_)
    (run : runX (inflate_LEN_ c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  by_cases fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true
  · obtain ⟨_, _, _, _, _, _, _, source, _⟩ := Zlib.Inflate.Local.inflate_LEN_start_fast_view_step E invariant buffers mode fast
    have impossible := xrun_outcome_eq source run
    cases impossible
  · let state := { s with mode := LEN }
    let heap := setI h zs state
    have good := invariant.good.decode_update (state := state) rfl
      (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
    have env : Env c heap r zs z state := ⟨E.strm, E.st, good.live.hz, good.live.hs⟩
    have tables := (invariant.tables (by rw [mode]; unfold DataTableMode; decide)).decode_update invariant.good.live.hs (after := state) rfl
    have pending : DataPendingInvariant state := by
      apply dataPendingInvariant_idle (s := state) invariant.pending.sane
      change LEN ≠ LENEXT ∧ LEN ≠ DIST ∧ LEN ≠ DISTEXT ∧ LEN ≠ MATCH
      decide
    have packet := dispatch_byte_views_local buffers invariant.good good rfl
      (fun ref => byte_view_get_setI h zs state ref) (fun ref => byte_view_ro_setI h zs state ref)
    have cut : runX (inflate_LEN_ c) l h = runX (inflate_LEN c) l heap := by
      unfold inflate_LEN_
      rw [runX_bind, runX_setMode E]
    exact len_slow_leave_pause env good tables packet pending rfl fast (cut.symm.trans run) get

/-- Every actual active data dispatch leaves in a resumable data mode.
Malformed code and distance branches return normally in BAD first. -/
theorem data_dispatch_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  have tables := invariant.tables mode
  rcases mode with mode | mode | mode | mode | mode | mode | mode
  · exact len_start_leave_pause E invariant buffers mode ((inflate_dispatch_LEN_start E l mode).symm.trans run) get
  · exact len_leave_pause E invariant buffers mode ((inflate_dispatch_LEN E l mode).symm.trans run) get
  · exact lenext_leave_pause E invariant.good tables buffers invariant.pending mode ((inflate_dispatch_LENEXT E l mode).symm.trans run) get
  · exact dist_leave_pause E invariant.good tables buffers invariant.pending mode ((inflate_dispatch_DIST E l mode).symm.trans run) get
  · exact distext_leave_pause E invariant.good tables buffers invariant.pending mode ((inflate_dispatch_DISTEXT E l mode).symm.trans run) get
  · exact match_leave_pause E invariant.good tables buffers invariant.pending mode ((inflate_dispatch_MATCH E l mode).symm.trans run) get
  · exact lit_leave_pause E invariant.good tables buffers mode ((inflate_dispatch_LIT E l mode).symm.trans run) get

#print axioms data_dispatch_leave_pause
#print axioms len_start_leave_pause
end Zlib.Uncompr.Proof.LocalPause
