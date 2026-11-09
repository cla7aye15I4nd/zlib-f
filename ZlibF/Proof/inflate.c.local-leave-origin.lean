import ZlibF.Proof.«inflate.c.local-leave-live»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem leaveWithWindow_effects_local {c : Ctx} {l : IL} {h after : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (output : OutputCursorInvariant h r l)
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (run : leaveWithWindow c l z h = .ok (rc, after))
    (final : LocalGood after cutoff r zs stream state) :
    after.nextBlk = h.nextBlk + (if s.window = .null ∧ h.allocOk h.nalloc = true then 1 else 0) ∧
    after.nalloc = h.nalloc + (if s.window = .null then 1 else 0) ∧
    (state.window = s.window ∨ (s.window = .null ∧ state.window = .ref (.blk h.nextBlk) 0)) := by
  obtain ⟨ref, bytes, off, put, get, _, room, leftCount, produced, unowned⟩ :=
    callerRange_slow_output good l output.range output.nonnull output.count output.produced
  have amount : (l.out_ - z.avail_out).toNat = l.out_.toNat - l.left.toNat := by
    rw [count, UInt32.toNat_sub_of_le _ _ leftCount]
  have start : (l.out_ - z.avail_out).toNat ≤ off := by rw [amount]; exact produced
  have bound : off ≤ bytes.size := by omega
  have sep : Separate (.ref ref (off - (l.out_ - z.avail_out).toNat))
      (l.out_ - z.avail_out).toNat s.window (2 ^ s.wbits.toNat) := by
    rcases good.inv.win.block with null | ⟨w, a, win, _, _, _⟩
    · simp [Separate, null]
    · simp [Separate, win, unowned w win]
  obtain ⟨wr, heap1, state1, windowRun, good1, _, sourceView, _, outcome⟩ :=
    updatewindow_decoder_boundary_local (copy := l.out_ - z.avail_out) good allocator get start bound unowned
  rcases outcome with success | failure
  · subst wr
    have env1 : Env c heap1 r zs z state1 := ⟨E.strm, E.st, good1.live.hz, good1.live.hs⟩
    have view : LeaveOutputView heap1 l :=
      ⟨ref, off, bytes, put, sourceView, by rw [count] at start; exact start, bound⟩
    have endpoint : off - (l.out_ - z.avail_out).toNat + (l.out_ - z.avail_out).toNat = off :=
      Nat.sub_add_cancel start
    have actualWindow : C.run (updatewindow (some r)
        (.ref ref (off - (l.out_ - z.avail_out).toNat + (l.out_ - z.avail_out).toNat))
        (l.out_ - z.avail_out)) h = .ok (0, heap1) := by
      simpa only [C.run, endpoint] using windowRun
    obtain ⟨frame, windowLedger, nextCount, allocCount, origin⟩ :=
      updatewindow_local_effects good allocator get start bound sep windowRun good1.live.hs
    have statics1 : Zlib.Crc32.Proofs.StaticsOK heap1 := by
      simpa only [Zlib.Crc32.Proofs.StaticsOK, ← frame.1] using statics
    obtain ⟨rc2, heap2, stream2, state2, finish, good2, fields, _, _, _, _⟩ :=
      leaveFinalize_local_safe (z := z) env1 good1 view statics1 cursor count
    unfold leaveWithWindow at run
    rw [bind_app, E.strm, cursor, put, windowRun] at run
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
    have same := Except.ok.inj (finish.symm.trans run)
    cases same
    have states : state = state2 := Option.some.inj (final.live.hs.symm.trans good2.live.hs)
    subst state2
    have metadata := fastMemoryMetaFrameM_leaveFinalize r c l z E.strm heap1 rc after finish
    have next : after.nextBlk = heap1.nextBlk := congrArg (fun x => x.2.1) metadata
    have alloc : after.nalloc = heap1.nalloc := congrArg (fun x => x.2.2.1) metadata
    have window : state.window = state1.window := by rw [fields]
    exact ⟨next.trans nextCount, alloc.trans allocCount, by simpa only [window] using origin⟩
  · obtain ⟨eqrc, oldnull, stateEq, heapEq⟩ := failure
    subst wr
    subst state1
    unfold leaveWithWindow at run
    rw [bind_app, E.strm, cursor, put, windowRun] at run
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app] at run
    cases run
    have states : state = {s with mode := MEM} := by
      have stored := final.live.hs
      simp only [setI_istates_same] at stored
      exact (Option.some.inj stored).symm
    have noalloc : h.allocOk h.nalloc ≠ true := by
      intro ok
      have actual := uw_new_local_exact good allocator oldnull ok get start bound
      have wrong := Except.ok.inj (windowRun.symm.trans actual)
      have : (1 : Int32) = 0 := congrArg Prod.fst wrong
      contradiction
    rw [heapEq]
    simp [setI, states, oldnull, noalloc]
/-- Exact window origin and allocation accounting for the entire actual leave. -/
theorem inflate_leave_effects_local {c : Ctx} {l : IL} {h after : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (run : inflate_leave c l h = .ok (rc, after)) (final : LocalGood after cutoff r zs stream state) :
    let update := (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
    after.nextBlk = h.nextBlk + (if update ∧ s.window = .null ∧ h.allocOk h.nalloc = true then 1 else 0) ∧
    after.nalloc = h.nalloc + (if update ∧ s.window = .null then 1 else 0) ∧
    (state.window = s.window ∨ (s.window = .null ∧ state.window = .ref (.blk h.nextBlk) 0)) := by
  dsimp only
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  obtain ⟨current, packet0⟩ := invariant.leave_restore E buffers bits
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have output0 : OutputCursorInvariant heap0 r l := packet0.output
  have statics0 : Zlib.Crc32.Proofs.StaticsOK heap0 := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [current.globals]
    exact ⟨rfl, rfl⟩
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update] at run
    have effect := leaveWithWindow_effects_local env0 current.good allocator.1 output0
      statics0 rfl rfl run final
    simpa only [heap0, state0, leaveState, setI, ZStreamRef.put_nextBlk,
      ZStreamRef.put_nalloc, ZStreamRef.put_allocOk, update, true_and] using effect
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip] at run
    have metadata := fastMemoryMetaFrameM_leaveFinalize r c l stream0 E.strm heap0 rc after run
    have next : after.nextBlk = heap0.nextBlk := congrArg (fun x => x.2.1) metadata
    have alloc : after.nalloc = heap0.nalloc := congrArg (fun x => x.2.2.1) metadata
    obtain ⟨rc2, heap2, stream2, state2, finish, good2, fields, _, _, _, _⟩ :=
      leaveFinalize_local_safe (z := stream0) env0 current.good
        (leaveOutputView_of_cursor current.good output0) statics0 rfl rfl
    have same := Except.ok.inj (finish.symm.trans run)
    cases same
    have states : state = state2 := Option.some.inj (final.live.hs.symm.trans good2.live.hs)
    have window : state.window = s.window := by rw [states, fields]; rfl
    simpa [skip] using (show after.nextBlk = h.nextBlk ∧ after.nalloc = h.nalloc ∧
      (state.window = s.window ∨ (s.window = .null ∧ state.window = .ref (.blk h.nextBlk) 0)) from
      ⟨by simpa [heap0, setI] using next, by simpa [heap0, setI] using alloc, Or.inl window⟩)

#print axioms leaveWithWindow_effects_local
#print axioms inflate_leave_effects_local
end Zlib.Inflate.Local
