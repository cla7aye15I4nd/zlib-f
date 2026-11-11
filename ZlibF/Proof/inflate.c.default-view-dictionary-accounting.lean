import ZlibF.Proof.«inflate.c.default-view-return-trace»
import ZlibF.Proof.«inflate.c.dictionary-return-sync-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual complete body retains byte accounting through ordinary
leave and the direct dictionary request. Only direct MEM/STREAM exits
remain alternatives; no direct-return cursor contract is assumed. -/
theorem inflate_default_view_local_dictionary_accounting
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
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
      ((rc = Z_MEM_ERROR ∨ rc = Z_STREAM_ERROR) ∨ StreamAccounting z stream used made) := by
  obtain ⟨rc, after, stream, state, bytes, exit, regs, loopHeap, loopZ, loopS,
    used, made, bodyRun, final, finalAllocator, get, size, ro, run, current, frame,
    next, count, put, left, trace⟩ :=
    inflate_default_view_local_return_trace E invariant allocator buffers nonnull inputValid local_
      localGet localSize localRo
  obtain ⟨stateEq, allocEq, freeEq, opaqueEq, reservedEq⟩ :=
    frame.fields invariant.good.live.hz current.good.live.hz
  have account (candidate : ZStream)
      (nextIn : candidate.next_in = regs.next) (availIn : candidate.avail_in = regs.have_)
      (nextOut : candidate.next_out = regs.put) (availOut : candidate.avail_out = regs.left)
      (fixed : candidate.state = loopZ.state ∧ candidate.zalloc = loopZ.zalloc ∧
        candidate.zfree = loopZ.zfree ∧ candidate.opaque = loopZ.opaque ∧
        candidate.reserved = loopZ.reserved) : StreamAccounting z candidate used made := by
    refine ⟨by omega, by omega, ?_, ?_, ?_, ?_,
      fixed.1.trans stateEq, fixed.2.1.trans allocEq,
      fixed.2.2.1.trans freeEq, fixed.2.2.2.1.trans opaqueEq,
      fixed.2.2.2.2.trans reservedEq⟩
    · rw [availIn]
      exact count
    · rw [availOut]
      exact left
    · rw [nextIn, next]
      cases z.next_in <;> rfl
    · rw [nextOut, put]
      cases z.next_out <;> rfl
  refine ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, by omega, by omega, ?_⟩
  cases exit with
  | ret value =>
    obtain ⟨same, _, streamEq, _, allowed⟩ := trace
    rcases allowed with needed | memory | refused
    · have sync := inflate_run_need_dict_sync E.strm E.st (by simpa only [needed] using run)
      obtain ⟨candidate, candidateGet, nextIn, availIn, nextOut, availOut⟩ := sync
      have candidateEq : candidate = loopZ :=
        Option.some.inj (candidateGet.symm.trans current.good.live.hz)
      subst candidate
      apply Or.inr
      rw [streamEq]
      exact account loopZ nextIn availIn nextOut availOut ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact Or.inl (Or.inl (same.trans memory))
    · exact Or.inl (Or.inr (same.trans refused))
  | leave =>
    obtain ⟨nextIn, availIn, nextOut, availOut, outcome⟩ := trace
    have fixed : stream.state = loopZ.state ∧ stream.zalloc = loopZ.zalloc ∧
        stream.zfree = loopZ.zfree ∧ stream.opaque = loopZ.opaque ∧
        stream.reserved = loopZ.reserved := by
      rcases outcome with ⟨_, fields, _⟩ | ⟨_, _, fields⟩
      all_goals rw [fields]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    exact Or.inr (account stream nextIn availIn nextOut availOut fixed)

#print axioms inflate_default_view_local_dictionary_accounting
end Zlib.Inflate.Proofs
