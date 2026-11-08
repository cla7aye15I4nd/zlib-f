import ZlibF.Proof.«inflate.c.default-view-return-trace»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual returning body exposes bounded accumulated byte
counts. Every ordinary leave, including window failure, has full public
StreamAccounting. Direct API exits remain explicitly classified; their
cursor-accounting connection is not assumed. -/
theorem inflate_default_view_local_accounting
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes used made,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false ∧
      used ≤ z.avail_in.toNat ∧ made ≤ z.avail_out.toNat ∧
      (DirectInflateCode rc ∨ StreamAccounting z stream used made) := by
  obtain ⟨rc, after, stream, state, bytes, exit, regs, loopHeap, loopZ, loopS,
    used, made, run, final, finalAllocator, get, size, ro, _, current, frame,
    next, count, put, left, trace⟩ :=
    inflate_default_view_local_return_trace E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  refine ⟨rc, after, stream, state, bytes, used, made, run, final, finalAllocator,
    get, size, ro, by omega, by omega, ?_⟩
  cases exit with
  | ret value =>
    obtain ⟨same, _, _, _, allowed⟩ := trace
    exact Or.inl (same ▸ allowed)
  | leave =>
    obtain ⟨nextIn, availIn, nextOut, availOut, outcome⟩ := trace
    obtain ⟨stateEq, allocEq, freeEq, opaqueEq, reservedEq⟩ :=
      frame.fields invariant.good.live.hz current.good.live.hz
    have preserved : stream.state = loopZ.state ∧ stream.zalloc = loopZ.zalloc ∧
        stream.zfree = loopZ.zfree ∧ stream.opaque = loopZ.opaque ∧
        stream.reserved = loopZ.reserved := by
      rcases outcome with ⟨_, fields, _⟩ | ⟨_, _, fields⟩
      all_goals rw [fields]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    apply Or.inr
    refine ⟨by omega, by omega, ?_, ?_, ?_, ?_,
      preserved.1.trans stateEq, preserved.2.1.trans allocEq,
      preserved.2.2.1.trans freeEq, preserved.2.2.2.1.trans opaqueEq,
      preserved.2.2.2.2.trans reservedEq⟩
    · rw [availIn]
      exact count
    · rw [availOut]
      exact left
    · rw [nextIn, next]
      cases z.next_in <;> rfl
    · rw [nextOut, put]
      cases z.next_out <;> rfl

#print axioms inflate_default_view_local_accounting
end Zlib.Inflate.Proofs
