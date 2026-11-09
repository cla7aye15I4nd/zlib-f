import ZlibF.Proof.«inflate.c.local-public-resources-slow-output»
import ZlibF.Proof.«inflate.c.slow-length-exact-frame»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Exact output frames compose across the actual decoder-record prefix.
The prefix may update stream scalars but preserves all caller byte views. -/
theorem metadata_then_output_buffer_frame
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z current : ZStream} {s state : InflateState}
    {dest : BRef} {off made : Nat} {array : Array UInt8}
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (get : Space.get h dest = some array) (write : Space.ro h dest = false)
    (suffix : BufferFrame (setI (r.put h current) zs state) after
      (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩])
    (writable : Space.ro after dest = false) :
    BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩] := by
  have firstFrame := (fastWriteback_heap_frame hz hs current state [⟨.ref dest off, made⟩]).1
  have shape := (shape_put hz current).trans (shape_setI (by simpa using hs) state)
  exact BufferFrame.singleton_trans firstFrame suffix shape get
    (by rw [byte_view_ro_setI, byte_view_ro_stream_put]; exact write) writable

/-- Actual slow length decoding, including its immediate distance and MATCH
continuations, has the exact output frame of its produced prefix. -/
theorem inflate_LEN_slow_exact_frame {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (sane : s.sane ≠ 0)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ outcome regs after stream state made,
      runX (inflate_LEN c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  rcases inflate_LEN_slow_to_MATCH_frame E.strm E.st good tables buffers.bits slow with stopped | continued
  · obtain ⟨outcome, regs, after, stream, state, _, _, _, _,
      run, current, _, _, _, shape, _, _, _, heapEq⟩ := stopped
    refine ⟨outcome, regs, after, stream, state, 0, run, current, ?_, ?_, ?_⟩
    · rw [shape]
      rfl
    · rw [shape, inputAdvance_zero]
    · rw [heapEq]
      exact (fastWriteback_heap_frame E.hz E.hs stream state [⟨l.put, 0⟩]).1
  · obtain ⟨middleRegs, middle, pending, used, consumed, usedBound, _, source,
      pendingGood, pendingTables, pendingInv, _, shape, mode, _, lower, _, distance, _, _,
      stateFrame, heapEq, cursor⟩ := continued
    have env1 : Env c middle r zs z pending :=
      ⟨E.strm, E.st, pendingGood.live.hz, pendingGood.live.hs⟩
    have packet : DispatchBuffers middle r middleRegs (bs.drop used) := by
      apply dispatch_consume_local buffers good pendingGood (by rw [stateFrame]) _ _ shape cursor usedBound pendingInv
      · intro ref
        rw [heapEq, byte_view_get_setI]
      · intro ref
        rw [heapEq, byte_view_ro_setI]
    obtain ⟨outcome, regs, after, stream, state, made, run, current, count, put, frame⟩ :=
      inflate_MATCH_exact_frame env1 pendingGood pendingTables packet mode (by omega) (by omega)
        (by rw [stateFrame]; exact sane)
    have actual : runX (inflate_LEN c) l h = .ok ((outcome, regs), after) := source.trans run
    have originalLeft : middleRegs.left = l.left := by rw [shape]
    have originalPut : middleRegs.put = l.put := by rw [shape]
    refine ⟨outcome, regs, after, stream, state, made, actual, current,
      by rwa [originalLeft] at count, by rwa [originalPut] at put, ?_⟩
    obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
      callerRange_slow_output good l buffers.output.range buffers.output.nonnull
        buffers.output.count buffers.output.produced
    have metadata := fastMemoryMetaFrameX_inflate_LEN r c E.strm l h outcome regs after actual
    have ro : after.ro = h.ro := congrArg Prod.fst metadata
    have writable : Space.ro after dest = false := by
      cases dest <;> simp only [Space.ro] at write ⊢
      all_goals first | exact write | (rw [ro]; exact write) | rfl
    rw [originalPut, pointer, heapEq] at frame
    have frame' : BufferFrame (setI (r.put h z) zs pending) after
        (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩] := by
      simpa only [ZStreamRef.put_self E.hz] using frame
    rw [pointer]
    exact metadata_then_output_buffer_frame E.hz E.hs get write frame' writable

#print axioms inflate_LEN_slow_exact_frame
end Zlib.Inflate.Local
