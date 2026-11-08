import ZlibF.Proof.«inflate.c.output-frame-compose»
import ZlibF.Proof.«inflate.c.fast-view-public-exact-frame»
import ZlibF.Proof.«inflate.c.fast-view-caller-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual fast LEN branch retains its exact output prefix through
RESTORE, the complete fast call, LOAD and the TYPE back-counter update. -/
theorem inflate_LEN_fast_exact_frame {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs after stream state made,
      runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) ∧
      DefaultStateJ after r zs stream state ∧ regs.left.toNat + made = l.left.toNat ∧
      regs.put = inputAdvance l.put made ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
  have facts : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
  have bitBound : l.bits.toNat ≤ 39 := by
    have small : l.bits.toNat < 8 := by simpa using UInt32.lt_iff_toNat_lt.mp facts.2
    omega
  obtain ⟨restored, packet⟩ := invariant.leave_restore E buffers bitBound
  obtain ⟨finished, stream, state, used, made, call, current, accounting, fastFrame⟩ :=
    inflate_fast_default_view_public_exact_frame restored packet mode
      rfl rfl rfl rfl rfl rfl fast
  have execution : Zlib.Inffast.inflate_fast c.strm l.out_
      (setI (r.put h (leaveStream z l)) zs (leaveState s l)) = .ok ((), finished) := by
    rw [E.strm]
    exact call
  have cut : runX (inflate_LEN c) l h = runX (inflateAfterFast c) l finished := by
    unfold inflate_LEN
    rw [runX_bind, runX_get]
    simp only [fast, ↓reduceIte]
    rw [runX_bind, RESTORE_pending_run E]
    simp only []
    rw [runX_bind, runX_lift_ok execution]
    rfl
  obtain ⟨dest, array, off, pointer, get, write, _⟩ :=
    callerRange_slow_output invariant.good l buffers.output.range buffers.output.nonnull
      buffers.output.count buffers.output.produced
  have metadata := fastMemoryMetaFrameM_inflate_fast r l.out_ _ () _ call
  have ro : finished.ro = (setI (r.put h (leaveStream z l)) zs (leaveState s l)).ro :=
    congrArg Prod.fst metadata
  have writable : Space.ro finished dest = false := by
    cases dest <;> simp only [Space.ro] at write ⊢
    all_goals first | exact write | (rw [ro, setI_ro, ZStreamRef.put_ro]; exact write) | rfl
  have fullFrame : BufferFrame h finished (fun b => StreamRoot r b ∨ b = zs) [⟨l.put, made⟩] := by
    rw [pointer] at fastFrame ⊢
    exact metadata_then_output_buffer_frame E.hz E.hs get write fastFrame writable
  have count : stream.avail_out.toNat + made = l.left.toNat := accounting.2.2.2.1
  have put : stream.next_out = inputAdvance l.put made := accounting.2.2.2.2.2.1
  have env1 : Env c finished r zs stream state :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  let regs : IL := { l with
    put := stream.next_out, left := stream.avail_out,
    next := stream.next_in, have_ := stream.avail_in, hold := state.hold, bits := state.bits }
  rw [cut, inflateAfterFast_run env1]
  by_cases type : state.mode = TYPE
  · rw [if_pos type]
    exact ⟨regs, _, stream, { state with back := -1 }, made, rfl,
      current.type_set_back type (-1), count, put, bufferFrame_setI_after fullFrame (Or.inr rfl)⟩
  · rw [if_neg type]
    exact ⟨regs, finished, stream, state, made, rfl, current, count, put, fullFrame⟩

#print axioms inflate_LEN_fast_exact_frame
end Zlib.Inflate.Proofs
