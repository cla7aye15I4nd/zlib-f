import ZlibF.Proof.«uncompr.c.local-return-causes»

namespace Zlib.Uncompr.Proof.LocalCauses
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inflate.Local
set_option autoImplicit false

/-- A legal actual body can report STREAM_ERROR only for the pre-existing
SYNC mode. Ordinary mode transitions cannot manufacture that direct return. -/
theorem inflate_body_not_stream_error
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0) (initial : s.mode ≠ SYNC)
    (body : (do
      let (result, regs) ← runX (inflate_run c) IL.init
      match result with
      | .error (.ret value) => pure value
      | _ => inflate_leave c regs) h = .ok (Z_STREAM_ERROR, after)) : False := by
  obtain ⟨bs, exit, regs, loopHeap, loopZ, loopS, used, made, _, run, current,
    packet, bits, _, _, _, _, _, _, loopAllocator⟩ :=
    Zlib.Inflate.Local.inflate_run_default_view_framed E invariant allocator buffers nonnull inputValid
  rw [bind_app, run] at body
  cases exit with
  | ret code =>
    change (Except.ok (code, loopHeap) : Except Fault (Int32 × Heap)) = .ok (Z_STREAM_ERROR, after) at body
    have codeEq : code = Z_STREAM_ERROR := congrArg Prod.fst (Except.ok.inj body)
    subst code
    exact inflate_run_direct_terminal_excluded E invariant buffers nonnull inputValid
      (Or.inr ⟨rfl, rfl⟩) initial run
  | leave =>
    change inflate_leave c regs loopHeap = .ok (Z_STREAM_ERROR, after) at body
    have env : Env c loopHeap r zs loopZ loopS :=
      ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
    obtain ⟨rc, heap1, returned, state, actual, _, _, _, _, _, _, outcome⟩ :=
      inflate_leave_local_public_accounting env current loopAllocator packet bits
    have selected : rc = Z_STREAM_ERROR := congrArg Prod.fst (Except.ok.inj (actual.symm.trans body))
    rcases outcome with ordinary | memory
    · have ret := ordinary_public_ret (Zlib.Inflate.Local.inflate_run_leave_ret_codes E invariant buffers nonnull inputValid run)
      have code : OrdinaryPublicCode rc := by
        rw [ordinary.1]
        split
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact ret
      rw [selected] at code
      rcases code with code | code | code | code <;> revert code <;> decide
    · exact (by decide : Z_STREAM_ERROR ≠ Z_MEM_ERROR) (selected.symm.trans memory.1)

/-- `int inflate(z_streamp strm, int flush)`.
The real public call cannot produce STREAM_ERROR when the initialized
state is not SYNC and its actual input/output pointers pass the C guards.
This does not assert that all initialized histories exclude SYNC. -/
theorem inflate_public_not_stream_error
    {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {rc : Int32}
    (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) (initial : s.mode ≠ SYNC)
    (nonnull : z.next_out ≠ .null) (inputValid : z.next_in = .null → z.avail_in = 0)
    (run : C.run (inflate (some r) flush) h = .ok (rc, after)) : rc ≠ Z_STREAM_ERROR := by
  intro codeEq
  subst rc
  let c : Ctx := ⟨some r, some (.tab zs), syncBuf h, flush⟩
  have allocated := Zlib.Inflate.Local.default_state_syncAlloc invariant
  have env : Env c (syncAlloc h) r zs z s :=
    ⟨rfl, rfl, allocated.good.live.hz, allocated.good.live.hs⟩
  have accepted : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = false := by
    have valid : z.next_in ≠ .null ∨ z.avail_in = 0 := by
      by_cases null : z.next_in = .null
      · exact Or.inr (inputValid null)
      · exact Or.inl null
    rcases valid with valid | valid <;> simp [nonnull, valid]
  have localBuffers := streamBuffers_syncAlloc invariant.good.fresh buffers
  obtain ⟨rc, heap1, stream, state, bytes, bodyRun, current, finalAllocator,
    get, size, ro⟩ :=
    Zlib.Inflate.Local.inflate_default_view_local_state_return env allocated allocator localBuffers nonnull inputValid
      (syncAlloc_bytes_buf h) (by simp only [syncJunk, Array.size_ofFn]) (syncAlloc_ro_buf h)
  have actual : C.run (inflate (some r) flush) h = .ok (rc, freeWin heap1 (syncBuf h)) := by
    unfold C.run inflate
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
    rw [freeBuf_run get ro]
    rfl
  have selected : rc = Z_STREAM_ERROR := congrArg Prod.fst (Except.ok.inj (actual.symm.trans run))
  rw [selected] at bodyRun
  exact inflate_body_not_stream_error env allocated allocator localBuffers nonnull inputValid initial bodyRun

#print axioms inflate_public_not_stream_error
#print axioms inflate_body_not_stream_error
end Zlib.Uncompr.Proof.LocalCauses
