import ZlibF.Proof.«inflate.c.local-return-codes»
import ZlibF.Proof.«inflate.c.local-return-mode-run»
import ZlibF.Proof.«inflate.c.default-view-return-modes»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual returning body has the public terminal mode
clauses, including genuine window allocation failure into MEM. -/
theorem inflate_default_view_local_return_modes
    {c : Ctx} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes used made,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false ∧
      used ≤ z.avail_in.toNat ∧ made ≤ z.avail_out.toNat ∧ StreamAccounting z stream used made ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        stream.total_in = z.total_in + UInt64.ofNat used) ∧
      (rc = Z_OK → used ≠ 0 ∨ made ≠ 0) ∧ PublicInflateCode rc ∧
      (rc = Z_MEM_ERROR → stream.total_in = z.total_in) ∧ ReturnedModes rc state := by
  obtain ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, totals, progress, codes, memoryInput⟩ :=
    inflate_default_view_local_return_codes E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  refine ⟨rc, after, stream, state, bytes, used, made, bodyRun, final, finalAllocator,
    get, size, ro, usedBound, madeBound, accounting, totals, progress, codes, memoryInput, ?_⟩
  obtain ⟨otherRc, otherHeap, otherZ, otherS, _, exit, regs, loopHeap, loopZ, loopS,
    used2, made2, source, otherFinal, _, _, _, _, run, current, _, _, _, _, _, trace⟩ :=
    inflate_default_view_local_return_trace E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  have same := Except.ok.inj (source.symm.trans bodyRun)
  cases same
  have sameS : otherS = state :=
    Option.some.inj (otherFinal.good.live.hs.symm.trans final.good.live.hs)
  subst otherS
  obtain ⟨returned, privateGet, needMode, memoryMode, leaveModes⟩ :=
    inflate_run_return_modes E invariant buffers nonnull inputValid run
  have stateEq : returned = loopS := Option.some.inj (privateGet.symm.trans current.good.live.hs)
  subst returned
  cases exit with
  | ret value =>
    obtain ⟨sameRc, _, _, sameState, direct⟩ := trace
    rw [sameRc, sameState]
    exact ReturnedModes.direct direct (fun code => needMode (congrArg Ex.ret code))
      (fun code => memoryMode (congrArg Ex.ret code))
  | leave =>
    obtain ⟨_, _, _, _, outcome⟩ := trace
    rcases outcome with success | failure
    · obtain ⟨ended, error⟩ := leaveModes rfl
      have ordinary := leave_return_ordinary_code regs c.flush
        (inflate_run_leave_ret_codes E invariant buffers nonnull inputValid run)
      have selected : OrdinaryPublicCode rc := success.1.symm ▸ ordinary
      apply ReturnedModes.ordinary selected success.1
      · intro code
        rw [success.2.2]
        exact ended code
      · intro code
        rw [success.2.2]
        exact error code
    · rw [failure.1]
      exact ReturnedModes.memory failure.2.1

#print axioms inflate_default_view_local_return_modes
end Zlib.Inflate.Local
