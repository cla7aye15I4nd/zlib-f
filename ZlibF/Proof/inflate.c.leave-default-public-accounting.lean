import ZlibF.Proof.«inflate.c.leave-public-accounting»
import ZlibF.Proof.«inflate.c.leave-default-boundary»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The same actual leave execution retains J, exact cursor bindings and
public counter timing. A real window failure returns the restored stream
before suffix counters; an ordinary exit credits the remaining local base.
Any earlier CHECK credit is already in z and must be accounted by the loop. -/
theorem inflate_leave_default_public_accounting
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39) :
    ∃ rc after stream state,
      inflate_leave c l h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      stream.next_in = l.next ∧ stream.avail_in = l.have_ ∧
      stream.next_out = l.put ∧ stream.avail_out = l.left ∧
      ((rc = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || c.flush == Z_FINISH) &&
          l.ret == Z_OK) then Z_BUF_ERROR else l.ret) ∧
        stream = { leaveCountStream (leaveStream z l) (leaveStream z l) l with
          adler := stream.adler, data_type := stream.data_type } ∧ state.mode = s.mode) ∨
        (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ stream = leaveStream z l)) := by
  obtain ⟨rc, after, stream, state, run, final, finalAllocator⟩ :=
    inflate_leave_default_state E invariant allocator buffers bits
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [invariant.globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨otherRc, otherHeap, otherZ, otherS, otherRun, otherGood,
    _, _, _, outcome, _⟩ :=
    inflate_leave_public_accounting E invariant.good allocator.1 statics buffers
      invariant.tables invariant.pending bits
  have same : (rc, after) = (otherRc, otherHeap) :=
    Except.ok.inj (run.symm.trans otherRun)
  cases same
  have sameZ : stream = otherZ :=
    Option.some.inj (final.good.live.hz.symm.trans otherGood.live.hz)
  have sameS : state = otherS :=
    Option.some.inj (final.good.live.hs.symm.trans otherGood.live.hs)
  subst otherZ
  subst otherS
  refine ⟨rc, after, stream, state, run, final, finalAllocator, ?_, ?_, ?_, ?_, outcome⟩
  all_goals rcases outcome with ⟨_, fields, _⟩ | ⟨_, _, fields⟩ <;> rw [fields] <;> rfl

#print axioms inflate_leave_default_public_accounting
end Zlib.Inflate.Proofs
