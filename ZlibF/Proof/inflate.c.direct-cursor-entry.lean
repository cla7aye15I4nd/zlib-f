import ZlibF.Proof.«inflate.c.direct-cursor-loop»
import ZlibF.Proof.«inflate.c.default-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual entry and loop publish DICT's final cursors. Other direct
returns retain the complete original public stream, even though entry
may normalize a private TYPE record. -/
theorem inflate_run_default_direct_cursors
    {c : Ctx} {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} {regs : IL} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (raw : RawFastIO (dispatchRegs z s))
    (run : runX (inflate_run c) IL.init h = .ok ((.error (.ret rc), regs), after))
    (observed : r.get after = some stream) :
    (rc = Z_NEED_DICT → RestoredCursors stream regs) ∧ (rc ≠ Z_NEED_DICT → stream = z) := by
  obtain ⟨heap0, state0, bs, entry, current, env0, packet, bits, sizes, frame, heapEq⟩ :=
    inflate_run_default_state_entry E invariant buffers nonnull inputValid
  have currentRaw : RawFastIO (dispatchRegs z state0) := raw
  obtain ⟨exit, regs2, heap2, stream2, state2, used, made, bound, loopRun,
    final, finalPacket, finalRaw, finalBits, finalSizes, next, count, put, left, meaning⟩ :=
    inflate_default_raw_direct_cursor_loop env0 current packet currentRaw bits
  have executed := entry.symm.trans run
  have same := Except.ok.inj (loopRun.symm.trans executed)
  have sameRegs : regs2 = regs := congrArg (fun pair => pair.1.2) same
  have outcomeEq : (.error exit : Except Ex Unit) = .error (.ret rc) := congrArg (fun pair => pair.1.1) same
  have sameHeap : heap2 = after := congrArg Prod.snd same
  have selected : exit = .ret rc := Except.error.inj outcomeEq
  rw [selected] at meaning
  change (rc = Z_NEED_DICT → ∀ stream, r.get heap2 = some stream → RestoredCursors stream regs2) ∧
    (rc ≠ Z_NEED_DICT → regs2 = dispatchRegs z state0 ∧ heap2 = heap0) at meaning
  constructor
  · intro needed
    have get : r.get heap2 = some stream := sameHeap.symm ▸ observed
    have restored := meaning.1 needed stream get
    rwa [sameRegs] at restored
  · intro notNeeded
    have heap : heap2 = heap0 := (meaning.2 notNeeded).2
    have get : r.get after = some z := by rw [← sameHeap, heap]; exact env0.hz
    exact Option.some.inj (observed.symm.trans get)

end Zlib.Inflate.Proofs
