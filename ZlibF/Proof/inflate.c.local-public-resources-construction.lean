import ZlibF.Proof.«inflate.c.local-public-resources-construction-boundary»
import ZlibF.Proof.«inflate.c.local-public-resources-length»
import ZlibF.Proof.«inflate.c.construction-output-frame»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A real metadata prefix composes with a produced caller slice on the
same object. The caller's original writable view supplies the domain. -/
theorem record_frame_then_output {h middle after : Heap} {r : ZStreamRef} {zs : Nat}
    {dest : BRef} {off made : Nat} {array : Array UInt8}
    (preFrame : RecordFrame r (some (.tab zs)) h middle)
    (output : BufferFrame middle after (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩])
    (get : Space.get h dest = some array) (write : Space.ro h dest = false)
    (writeAfter : Space.ro after dest = false) :
    BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩] := by
  have first : BufferFrame h middle (fun b => StreamRoot r b ∨ b = zs) [⟨.ref dest off, made⟩] := by
    simpa only [DecoderRecordRoot] using preFrame.buffer [⟨.ref dest off, made⟩]
  have writeMiddle : Space.ro middle dest = false := by
    rw [byte_view_ro_of_ro_eq preFrame.2.2.2 dest]
    exact write
  exact BufferFrame.singleton_trans first output preFrame.2.2.1 get writeMiddle writeAfter

/-- All three actual construction modes preserve private metadata until
LEN_, then compose its proved slow or fast output frame. Wait, malformed
alphabets and the real TREES return keep an empty output prefix. -/
theorem inflate_dispatch_construction_exact_frame
    {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = TABLE ∨ s.mode = LENLENS ∨ s.mode = CODELENS) :
    ∃ outcome regs after stream state made,
      runX (inflate_dispatch c) l h = .ok ((outcome, regs), after) ∧
      LocalGood after cutoff r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  obtain ⟨regs, after, stream, state, used, _bound, nextJ, _config, preFrame,
    packet, _sizes, _cursor, _count, put, left, _total, _bits, _budget, stopped | continued⟩ :=
    inflate_dispatch_construction_record_boundary E invariant buffers mode
  · obtain ⟨outcome, run, _why⟩ := stopped
    refine ⟨outcome, regs, after, stream, state, 0, run, nextJ.good,
      by rw [left]; omega, by rw [inputAdvance_zero]; exact put, ?_⟩
    simpa only [DecoderRecordRoot] using preFrame.buffer [⟨l.put, 0⟩]
  · obtain ⟨nextMode, source⟩ := continued
    by_cases trees : c.flush = Z_TREES
    · rw [if_pos trees] at source
      refine ⟨.error Ex.leave, regs, after, stream, state, 0, source, nextJ.good,
        by rw [left]; omega, by rw [inputAdvance_zero]; exact put, ?_⟩
      simpa only [DecoderRecordRoot] using preFrame.buffer [⟨l.put, 0⟩]
    · rw [if_neg trees] at source
      have nextEnv : Env c after r zs stream state :=
        ⟨E.strm, E.st, nextJ.good.live.hz, nextJ.good.live.hs⟩
      obtain ⟨outcome, finalRegs, finalHeap, finalStream, finalState, made,
        run, current, leftCount, output, frame⟩ :=
        inflate_LEN_start_exact_frame nextEnv nextJ packet nextMode
      have actual := source.trans run
      obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
        callerRange_slow_output invariant.good l buffers.output.range buffers.output.nonnull
          buffers.output.count buffers.output.produced
      have metadata := fastMemoryMetaFrameX_inflate_dispatch r c E.strm l h outcome finalRegs finalHeap actual
      have writeAfter : Space.ro finalHeap dest = false := by
        rw [byte_view_ro_of_ro_eq (congrArg Prod.fst metadata) dest]
        exact write
      refine ⟨outcome, finalRegs, finalHeap, finalStream, finalState, made, actual, current,
        by rw [left] at leftCount; exact leftCount, by rw [output, put], ?_⟩
      rw [put, pointer] at frame
      rw [pointer]
      exact record_frame_then_output preFrame frame get write writeAfter

#print axioms inflate_dispatch_construction_exact_frame
end Zlib.Inflate.Local
