import ZlibF.Proof.«inflate.c.local-window-j»
import ZlibF.Proof.«inflate.c.local-leave-state»
import ZlibF.Proof.«inflate.c.local-fast-state»
import ZlibF.Proof.«inflate.c.local-trailer-core»

/-! The complete actual inf_leave path retains the full local decoder J,
including allocation refusal and every optional checksum/return guard. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem LocalStateJ.mem_update {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} (invariant : LocalStateJ h cutoff r zs z s)
    (good : LocalGood after cutoff r zs stream { s with mode := MEM })
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after) (static : after.static = h.static) :
    LocalStateJ after cutoff r zs stream { s with mode := MEM } := by
  refine ⟨⟨good, ?_, dataPendingInvariant_idle invariant.pending.sane ?_, ?_, ?_,
    invariant.held, invariant.window, invariant.wrapper, invariant.header,
    Or.inr ?_, ?_, ?_, platform⟩, invariant.requestedBits, invariant.requestedWrap,
    Or.inr (Or.inr (Or.inl rfl)),
    ⟨invariant.roots.stream, invariant.roots.state, invariant.roots.window⟩⟩
  · intro active
    exact False.elim ((by unfold DataTableMode; decide : ¬ DataTableMode MEM) active)
  · change MEM ≠ LENEXT ∧ MEM ≠ DIST ∧ MEM ≠ DISTEXT ∧ MEM ≠ MATCH
    decide
  · intro active
    change MEM = CODELENS at active
    contradiction
  · intro active
    change MEM = LENLENS at active
    contradiction
  · change DICTID ≤ MEM ∧ MEM ≤ SYNC
    decide
  · rintro (active | active)
    · change MEM = CHECK at active
      contradiction
    · change MEM = LENGTH at active
      contradiction
  · change after.static = _
    rw [static]
    exact invariant.globals

theorem leaveWithWindow_local_state {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (invariant : LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (output : OutputCursorInvariant h r l) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveWithWindow c l z h = .ok (rc, after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DefAlloc stream := by
  obtain ⟨ref, bytes, off, put, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output invariant.good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ bytes.size := by omega
  have separate : Separate (.ref ref (off - (l.out_ - z.avail_out).toNat))
      (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
    rcases invariant.good.inv.win.block with null | ⟨w, a, win, _, _, _⟩
    · simp [Separate, null]
    · simp [Separate, win, unowned w win]
  obtain ⟨wr, heap1, state1, windowRun, current, windowFrame, sourceView, codeViews,
      publicFrame, ledger, nextCount, allocCount, origin, outcome⟩ :=
    updatewindow_local_state (copy := l.out_ - z.avail_out) invariant allocator.1 get start bound unowned
  have good1 := current.good
  rcases outcome with success | failure
  · subst wr
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, bytes, put, sourceView, by rw [count] at start; exact start, bound⟩
    obtain ⟨rc, after, stream, state, finish, final, finalAllocator⟩ :=
      leaveFinalize_local_state (z := z) env1 current allocator view cursor count
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact finish
  · obtain ⟨eqrc, _, stateEq, heapEq⟩ := failure
    subst wr
    subst state1
    let state := { s with mode := MEM }
    have good : LocalGood (setI heap1 zs state) cutoff r zs z state :=
      good1.decode_update (by rfl) (by change HEAD ≤ MEM ∧ MEM ≤ SYNC; decide)
    have final := current.mem_update good (current.platform.with_istates _) rfl
    refine ⟨Z_MEM_ERROR, setI heap1 zs state, z, state, ?_, final, allocator⟩
    unfold leaveWithWindow
    rw [bind_app, E.strm, cursor, put, windowRun]
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app]
    rfl

/-- The complete actual inf_leave boundary preserves the full default
relation and allocator. No extra mode, wrapper, checksum or allocation
success restriction is imposed at return. -/
theorem inflate_leave_local_state {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (E : Env c h r zs z s)
    (invariant : LocalStateJ h cutoff r zs z s) (allocator : DefAlloc z)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DefAlloc stream := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  obtain ⟨current, packet0⟩ := invariant.leave_restore E buffers bits
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l := packet0.output
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · obtain ⟨rc, after, stream, state, run, final, finalAllocator⟩ :=
      leaveWithWindow_local_state env0 current allocator output0 rfl rfl
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update]
    exact run
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    obtain ⟨rc, after, stream, state, run, final, finalAllocator⟩ :=
      leaveFinalize_local_state (z := stream0) env0 current allocator
        (leaveOutputView_of_cursor current.good output0) rfl rfl
    refine ⟨rc, after, stream, state, ?_, final, finalAllocator⟩
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip]
    exact run


#print axioms LocalStateJ.mem_update
#print axioms leaveWithWindow_local_state
#print axioms inflate_leave_local_state
end Zlib.Inflate.Local
