import ZlibF.Proof.«inflate.c.length-mode-output-frame»
import ZlibF.Proof.«inflate.c.pending-extra»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem byte_view_ro_of_ro_eq {h after : Heap} (ro : after.ro = h.ro) (ref : BRef) :
    Space.ro after ref = Space.ro h ref := by
  cases ref <;> simp only [Space.ro, ro]

/-- The complete actual distance decode and immediate MATCH call only
write their produced output prefix and the private stream/state records. -/
theorem inflate_DIST_exact_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = DIST) :
    ∃ outcome regs after stream state made,
      runX (inflate_DIST c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨lengthFacts, before, backBound, back⟩ := pending.dist mode
  rcases inflate_DIST_to_MATCH_frame before E.strm E.st good tables buffers.bits back backBound with stopped | continued
  · obtain ⟨outcome, regs, after, stream, state, _, _, _, _, run, current, _, _, _,
      shape, _, _, _, heapEq⟩ := stopped
    refine ⟨outcome, regs, after, stream, state, 0, run, current, ?_, ?_, ?_⟩
    · rw [shape]; rfl
    · rw [shape, inputAdvance_zero]
    · rw [heapEq]
      exact (fastWriteback_heap_frame E.hz E.hs stream state [⟨l.put, 0⟩]).1
  · obtain ⟨middleRegs, middle, middleState, used, _, usedBound, _, source,
      current, currentTables, currentBits, _, shape, heapEq, stateEq, distance, _, cursor⟩ := continued
    have stateFrame : DecodeStateFrame s middleState := by unfold DecodeStateFrame; rw [stateEq]
    have packet : DispatchBuffers middle r middleRegs (bs.drop used) := by
      apply buffers.consume good current (by rw [stateEq]) _ _ shape cursor usedBound currentBits
      · intro ref; rw [heapEq, byte_view_get_setI]
      · intro ref; rw [heapEq, byte_view_ro_setI]
    have env1 : Env c middle r zs z middleState := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    obtain ⟨outcome, regs, after, stream, state, made, run, final, count, put, frame⟩ :=
      inflate_MATCH_exact_frame env1 current currentTables packet (by rw [stateEq])
        (by rw [stateEq]; have lower := lengthFacts.1; change 0 < s.length.toNat; omega)
        (by omega) (by rw [stateEq, pending.sane]; decide)
    have actual := source.trans run
    have originalLeft : middleRegs.left = l.left := by rw [shape]
    have originalPut : middleRegs.put = l.put := by rw [shape]
    refine ⟨outcome, regs, after, stream, state, made, actual, final,
      by rwa [originalLeft] at count, by rwa [originalPut] at put, ?_⟩
    obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
      callerRange_slow_output good l buffers.output.range buffers.output.nonnull
        buffers.output.count buffers.output.produced
    have ro : after.ro = h.ro := congrArg Prod.fst
      (fastMemoryMetaFrameX_inflate_DIST r c E.strm l h outcome regs after actual)
    have writable : Space.ro after dest = false := by rw [byte_view_ro_of_ro_eq ro]; exact write
    rw [originalPut, pointer, heapEq] at frame
    have frame' : BufferFrame (setI (r.put h z) zs middleState) after
        (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩] := by
      simpa only [ZStreamRef.put_self E.hz] using frame
    rw [pointer]
    exact metadata_then_output_buffer_frame E.hz E.hs get write frame' writable

/-- Resumed extra-distance decoding composes its actual private prefix
with its actual MATCH continuation, including exhausted-input returns. -/
theorem inflate_DISTEXT_exact_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = DISTEXT) :
    ∃ outcome regs after stream state made,
      runX (inflate_DISTEXT c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  rcases inflate_DISTEXT_pending_boundary E good tables buffers pending mode with wait | continued
  · obtain ⟨regs, _, run, _, _, _, shape, _⟩ := wait
    obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
      callerRange_slow_output good l buffers.output.range buffers.output.nonnull
        buffers.output.count buffers.output.produced
    refine ⟨.error Ex.leave, regs, h, z, s, 0, run, good, ?_, ?_, ?_⟩
    · rw [shape]; rfl
    · rw [shape, inputAdvance_zero]
    · rw [pointer]; exact BufferFrame.singleton_refl get write
  · obtain ⟨middleRegs, middle, middleState, _, source, _, current, currentTables,
      packet, currentPending, nextMode, _, _, _, shape, _, heapEq, _⟩ := continued
    have env1 : Env c middle r zs z middleState := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    have matchSafe := currentPending.matching nextMode
    obtain ⟨outcome, regs, after, stream, state, made, run, final, count, put, frame⟩ :=
      inflate_MATCH_exact_frame env1 current currentTables packet nextMode matchSafe.1
        matchSafe.2.2.2 (by rw [currentPending.sane]; decide)
    have actual := source.trans run
    have originalLeft : middleRegs.left = l.left := by rw [shape]
    have originalPut : middleRegs.put = l.put := by rw [shape]
    refine ⟨outcome, regs, after, stream, state, made, actual, final,
      by rwa [originalLeft] at count, by rwa [originalPut] at put, ?_⟩
    obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
      callerRange_slow_output good l buffers.output.range buffers.output.nonnull
        buffers.output.count buffers.output.produced
    have ro : after.ro = h.ro := congrArg Prod.fst
      (fastMemoryMetaFrameX_inflate_DISTEXT r c E.strm l h outcome regs after actual)
    have writable : Space.ro after dest = false := by rw [byte_view_ro_of_ro_eq ro]; exact write
    rw [originalPut, pointer, heapEq] at frame
    have frame' : BufferFrame (setI (r.put h z) zs middleState) after
        (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩] := by
      simpa only [ZStreamRef.put_self E.hz] using frame
    rw [pointer]
    exact metadata_then_output_buffer_frame E.hz E.hs get write frame' writable

/-- Resumed extra-length decoding composes its actual private prefix with
its real distance and MATCH continuation. -/
theorem inflate_LENEXT_exact_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (pending : DataPendingInvariant s) (mode : s.mode = LENEXT) :
    ∃ outcome regs after stream state made,
      runX (inflate_LENEXT c) l h = .ok ((outcome, regs), after) ∧
      Good after r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  rcases inflate_LENEXT_pending_boundary E good tables buffers pending mode with wait | continued
  · obtain ⟨regs, _, run, _, _, _, shape, _⟩ := wait
    obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
      callerRange_slow_output good l buffers.output.range buffers.output.nonnull
        buffers.output.count buffers.output.produced
    refine ⟨.error Ex.leave, regs, h, z, s, 0, run, good, ?_, ?_, ?_⟩
    · rw [shape]; rfl
    · rw [shape, inputAdvance_zero]
    · rw [pointer]; exact BufferFrame.singleton_refl get write
  · obtain ⟨middleRegs, middle, middleState, _, source, _, current, currentTables,
      packet, currentPending, nextMode, _, _, _, shape, _, heapEq, _⟩ := continued
    have env1 : Env c middle r zs z middleState := ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
    obtain ⟨outcome, regs, after, stream, state, made, run, final, count, put, frame⟩ :=
      inflate_DIST_exact_frame env1 current currentTables packet currentPending nextMode
    have actual := source.trans run
    have originalLeft : middleRegs.left = l.left := by rw [shape]
    have originalPut : middleRegs.put = l.put := by rw [shape]
    refine ⟨outcome, regs, after, stream, state, made, actual, final,
      by rwa [originalLeft] at count, by rwa [originalPut] at put, ?_⟩
    obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
      callerRange_slow_output good l buffers.output.range buffers.output.nonnull
        buffers.output.count buffers.output.produced
    have ro : after.ro = h.ro := congrArg Prod.fst
      (fastMemoryMetaFrameX_inflate_LENEXT r c E.strm l h outcome regs after actual)
    have writable : Space.ro after dest = false := by rw [byte_view_ro_of_ro_eq ro]; exact write
    rw [originalPut, pointer, heapEq] at frame
    have frame' : BufferFrame (setI (r.put h z) zs middleState) after
        (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩] := by
      simpa only [ZStreamRef.put_self E.hz] using frame
    rw [pointer]
    exact metadata_then_output_buffer_frame E.hz E.hs get write frame' writable

#print axioms inflate_DIST_exact_frame
#print axioms inflate_DISTEXT_exact_frame
#print axioms inflate_LENEXT_exact_frame
end Zlib.Inflate.Proofs
