import ZlibF.Proof.«inflate.c.default-view-output-accounting»
import ZlibF.Proof.«inflate.c.output-credit-run»
import ZlibF.Proof.«inflate.c.leave-zero-output-memory»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Both public totals remain original on MEM_ERROR. CHECK credit cannot
precede a late allocation failure: its actual rebase leaves a zero-sized
suffix, for which the actual leave cannot return MEM_ERROR. -/
theorem inflate_default_view_local_memory_totals
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
      used ≤ z.avail_in.toNat ∧ made ≤ z.avail_out.toNat ∧ StreamAccounting z stream used made ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        stream.total_in = z.total_in + UInt64.ofNat used ∧
        stream.total_out = z.total_out + UInt64.ofNat made) ∧
      (rc = Z_OK → used ≠ 0 ∨ made ≠ 0) ∧ PublicInflateCode rc ∧
      (rc = Z_MEM_ERROR → stream.total_in = z.total_in ∧ stream.total_out = z.total_out) ∧
      ReturnedModes rc state := by
  obtain ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, totals, progress, codes, memoryInput, modes⟩ :=
    inflate_default_view_local_output_accounting E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  refine ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, totals, progress, codes, ?_, modes⟩
  intro memory
  refine ⟨memoryInput memory, ?_⟩
  obtain ⟨otherRc, otherHeap, otherZ, otherS, _, exit, regs, loopHeap, loopZ, loopS,
    used2, made2, source, otherFinal, _, _, _, _, run, current, _, _, _, _, _, trace⟩ :=
    inflate_default_view_local_return_trace E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  have same := Except.ok.inj (source.symm.trans bodyRun)
  cases same
  have sameZ : otherZ = stream :=
    Option.some.inj (otherFinal.good.live.hz.symm.trans final.good.live.hz)
  subst otherZ
  cases exit with
  | ret value =>
    obtain ⟨sameRc, _, streamEq, _, _⟩ := trace
    have valueEq : value = Z_MEM_ERROR := sameRc.symm.trans memory
    obtain ⟨original, _, _⟩ :=
      inflate_run_terminal_direct E invariant buffers nonnull inputValid local_ run (Or.inl valueEq)
    have originalEq : loopZ = z := Option.some.inj (current.good.live.hz.symm.trans original)
    rw [streamEq, originalEq]
  | leave =>
    obtain ⟨_, _, _, _, outcome⟩ := trace
    have ret := inflate_run_leave_ret_codes E invariant buffers nonnull inputValid local_ run
    rcases outcome with success | failure
    · have ordinary := leave_return_ordinary_code regs c.flush ret
      have selected : OrdinaryPublicCode rc := success.1.symm ▸ ordinary
      exact False.elim (selected.not_memory memory)
    · have shape := inflate_run_output_credit_shape E invariant buffers nonnull inputValid local_ run
        current.good.live.hz current.good.live.hs
      rcases shape with uncredited | ⟨_, zero⟩
      · rw [failure.2.2]
        exact uncredited
      · have leaveRun := bodyRun
        rw [bind_app, run] at leaveRun
        change inflate_leave c regs loopHeap = .ok (rc, after) at leaveRun
        rw [memory] at leaveRun
        obtain ⟨bs, exit2, regs2, heap2, stream2, state2, _, _, _, run2, final2,
          packet2, bits2, _, _, _, _, _, _, allocator2⟩ :=
          inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid local_
        have same2 := Except.ok.inj (run2.symm.trans run)
        cases same2
        have env2 : Env c loopHeap r zs stream2 state2 :=
          ⟨E.strm, E.st, final2.good.live.hz, final2.good.live.hs⟩
        exact False.elim (inflate_leave_zero_output_not_memory env2 final2.good allocator2.1
          final2.pending packet2 bits2 ret zero leaveRun)

#print axioms inflate_default_view_local_memory_totals
end Zlib.Inflate.Proofs
