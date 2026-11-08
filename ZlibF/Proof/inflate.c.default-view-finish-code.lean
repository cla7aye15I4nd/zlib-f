import ZlibF.Proof.«inflate.c.default-view-return-trace»
import ZlibF.Proof.«inflate.c.default-view-public»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual return expression never leaves Z_OK under Z_FINISH. -/
theorem leave_return_ok_not_finish {l : IL} {flush code : Int32}
    (result : code = (if ((l.in_ - l.have_ == 0 && l.out_ - l.left == 0 || flush == Z_FINISH) &&
      l.ret == Z_OK) then Z_BUF_ERROR else l.ret)) (ok : code = Z_OK) : flush ≠ Z_FINISH := by
  intro finish
  subst flush
  by_cases returned : l.ret = Z_OK
  · simp only [returned, beq_self_eq_true, Bool.or_true, Bool.and_self, ite_true] at result
    rw [ok] at result
    exact (by decide : Z_OK ≠ Z_BUF_ERROR) result
  · have no : (l.ret == Z_OK) = false := by
      cases equal : l.ret == Z_OK with
      | false => rfl
      | true => exact False.elim (returned (by simpa only [beq_iff_eq] using equal))
    simp only [no, Bool.and_false, Bool.false_eq_true, ite_false] at result
    exact returned (result.symm.trans ok)

/-- The complete actual returning body retains the Z_FINISH refusal to
return Z_OK, including direct returns and genuine window failure. -/
theorem inflate_default_view_local_finish_code
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (localGet : h.bytes block = some array) (localSize : array.size = 4) (localRo : h.ro block = false) :
    ∃ rc after stream state bytes,
      (do
        let (result, regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes block = some bytes ∧ bytes.size = 4 ∧ after.ro block = false ∧
      (rc = Z_OK → c.flush ≠ Z_FINISH) := by
  obtain ⟨rc, after, stream, state, bytes, exit, regs, loopHeap, loopZ, loopS,
    used, made, run, final, finalAllocator, get, size, ro, _, _, _, _, _, _, _, trace⟩ :=
    inflate_default_view_local_return_trace E invariant allocator buffers nonnull inputValid
      localGet localSize localRo
  refine ⟨rc, after, stream, state, bytes, run, final, finalAllocator, get, size, ro, ?_⟩
  intro ok
  cases exit with
  | ret value =>
    obtain ⟨same, _, _, _, allowed⟩ := trace
    have code : value = Z_OK := same.symm.trans ok
    rcases allowed with needed | memory | refused
    · exact False.elim ((by decide : Z_OK ≠ Z_NEED_DICT) (code.symm.trans needed))
    · exact False.elim ((by decide : Z_OK ≠ Z_MEM_ERROR) (code.symm.trans memory))
    · exact False.elim ((by decide : Z_OK ≠ Z_STREAM_ERROR) (code.symm.trans refused))
  | leave =>
    obtain ⟨_, _, _, _, result⟩ := trace
    rcases result with ⟨selected, _, _⟩ | ⟨memory, _, _⟩
    · exact leave_return_ok_not_finish selected ok
    · exact False.elim ((by decide : Z_OK ≠ Z_MEM_ERROR) (ok.symm.trans memory))

/-- `int inflate(z_streamp strm, int flush)`.
The actual complete public default call preserves J and allocator, frees
its local object, and cannot return Z_OK for Z_FINISH. This is one actual
public result clause; full counts, results, frame and history remain open. -/
theorem inflate_default_view_finish_code
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ rc after stream state,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧ (rc = Z_OK → flush ≠ Z_FINISH) := by
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  by_cases rejected : (z.next_out == .null ||
      (z.next_in == .null && z.avail_in != 0)) = true
  · have final := allocated.free_local (syncAlloc_bytes_buf h)
      (by simp only [syncJunk, Array.size_ofFn])
    refine ⟨Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h), z, s,
      ?_, final, allocator, ?_, ?_⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
      dsimp only [syncBuf]
      rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]
    · simp only [syncBuf, freeWin, upd_same]
    · intro ok
      exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_OK) ok)
  · have accepted : (z.next_out == .null ||
        (z.next_in == .null && z.avail_in != 0)) = false := by
      cases value : (z.next_out == .null ||
        (z.next_in == .null && z.avail_in != 0)) <;> simp_all
    have nonnull : z.next_out ≠ .null := by
      intro null
      apply rejected
      simp [null]
    have inputValid : z.next_in = .null → z.avail_in = 0 := by
      intro null
      by_cases zero : z.avail_in = 0
      · exact zero
      · exact False.elim (rejected (by simp [null, zero]))
    obtain ⟨rc, heap1, stream, state, bytes, bodyRun, current, finalAllocator,
      localGet, localSize, localRo, noFinish⟩ :=
      inflate_default_view_local_finish_code env allocated allocator
        (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid
        (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
    have final := current.free_local localGet localSize
    refine ⟨rc, freeWin heap1 (syncBuf h), stream, state, ?_, final, finalAllocator, ?_, noFinish⟩
    · unfold C.run inflate
      rw [bind_app, allocLocalB_run h invariant.good.fresh]
      simp only []
      rw [bind_app]
      simp only [bind_app, stateCheck_live allocated.good.live,
        bne_self_eq_false, Bool.false_eq_true, ite_false,
        ldZStream_ok allocated.good.live.hz, accepted, allocated.good.live.zst, castI]
      rw [bind_app] at bodyRun
      unfold runX at bodyRun
      dsimp only [c] at bodyRun
      erw [bodyRun]
      simp only []
      change (do freeB (syncBuf h); pure rc) heap1 = .ok (rc, freeWin heap1 (syncBuf h))
      rw [bind_app]
      dsimp only [syncBuf]
      rw [freeBuf_run localGet localRo]
      rfl
    · simp only [syncBuf, freeWin, upd_same]


#print axioms inflate_default_view_finish_code
end Zlib.Inflate.Proofs
