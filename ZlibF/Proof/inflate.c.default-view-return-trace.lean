import ZlibF.Proof.«inflate.c.low-output»
import ZlibF.Proof.«inflate.c.default-view-return»
import ZlibF.Proof.«inflate.c.leave-default-public-accounting»
import ZlibF.Proof.«inflate.c.exit-code-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Preserve the actual mode-loop exit and its accumulated caller cursors
through the complete returning body. Direct returns retain their source code;
leave retains exact cursor bindings, return selection and suffix counter
writes. CHECK credit and the direct-return cursor relation remain to be
composed before this yields the complete public accounting contract. -/
theorem inflate_default_view_local_return_trace
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (local_ : HeaderLocal c h r s (dispatchRegs z s))
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes exit regs loopHeap loopZ loopS used made,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false ∧
      runX (inflate_run c) IL.init h = .ok ((.error exit, regs), loopHeap) ∧
      DefaultStateJ loopHeap r zs loopZ loopS ∧ StreamRootFrame r h loopHeap ∧
      regs.next = inputAdvance z.next_in used ∧ regs.have_.toNat + used = z.avail_in.toNat ∧
      regs.put = inputAdvance z.next_out made ∧ regs.left.toNat + made = z.avail_out.toNat ∧
      (match exit with
       | .ret value => rc = value ∧ after = loopHeap ∧ stream = loopZ ∧ state = loopS ∧
           DirectInflateCode value
       | .leave => stream.next_in = regs.next ∧ stream.avail_in = regs.have_ ∧
           stream.next_out = regs.put ∧ stream.avail_out = regs.left ∧
           ((rc = (if ((regs.in_ - regs.have_ == 0 && regs.out_ - regs.left == 0 || c.flush == Z_FINISH) &&
               regs.ret == Z_OK) then Z_BUF_ERROR else regs.ret) ∧
             stream = { leaveCountStream (leaveStream loopZ regs) (leaveStream loopZ regs) regs with
               adler := stream.adler, data_type := stream.data_type } ∧ state.mode = loopS.mode) ∨
            (rc = Z_MEM_ERROR ∧ state.mode = MEM ∧ stream = leaveStream loopZ regs))) := by
  obtain ⟨rc, after, stream, state, bytes, bodyRun, final, finalAllocator,
    finalLocal, finalSize, finalRo⟩ :=
    inflate_default_view_local_state_return E invariant allocator buffers nonnull inputValid local_
      localGet localSize localRo
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, used, made, _, run, current,
    ⟨_, _, packet⟩, _, bits, _, next, count, put, left, frame, loopAllocator⟩ :=
    inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid local_
  refine ⟨rc, after, stream, state, bytes, exit, regs, loopHeap, loopZ, loopS, used, made,
    bodyRun, final, finalAllocator, finalLocal, finalSize, finalRo, run, current,
    frame, next, count, put, left, ?_⟩
  cases exit with
  | ret value =>
    have body := bodyRun
    rw [bind_app, run] at body
    change (Except.ok (value, loopHeap) : Except Fault (Int32 × Heap)) = .ok (rc, after) at body
    have same := Except.ok.inj body
    cases same
    have sameZ : stream = loopZ :=
      Option.some.inj (final.good.live.hz.symm.trans current.good.live.hz)
    have sameS : state = loopS :=
      Option.some.inj (final.good.live.hs.symm.trans current.good.live.hs)
    exact ⟨rfl, rfl, sameZ, sameS, inflate_run_direct_codes run⟩
  | leave =>
    have currentEnv : Env c loopHeap r zs loopZ loopS :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨leaveRc, leaveHeap, leaveZ, leaveS, leaveRun, leaveJ, _,
      nextIn, availIn, nextOut, availOut, outcome⟩ :=
      inflate_leave_default_public_accounting currentEnv current loopAllocator packet bits
        (inflate_run_default_low_out E invariant buffers nonnull inputValid local_ run current.good.live.hs)
    have body := bodyRun
    rw [bind_app, run] at body
    change inflate_leave c regs loopHeap = .ok (rc, after) at body
    have same : (leaveRc, leaveHeap) = (rc, after) :=
      Except.ok.inj (leaveRun.symm.trans body)
    cases same
    have sameZ : stream = leaveZ :=
      Option.some.inj (final.good.live.hz.symm.trans leaveJ.good.live.hz)
    have sameS : state = leaveS :=
      Option.some.inj (final.good.live.hs.symm.trans leaveJ.good.live.hs)
    subst leaveZ
    subst leaveS
    exact ⟨nextIn, availIn, nextOut, availOut, outcome⟩

#print axioms inflate_default_view_local_return_trace
end Zlib.Inflate.Proofs
