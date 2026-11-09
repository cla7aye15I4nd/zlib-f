import ZlibF.Proof.«inflate.c.local-leave-frame»
import ZlibF.Proof.«inflate.c.local-window-live»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- If the live set is unchanged, a good returned decoder cannot own an
unaccounted new object. This is the no-allocation case of the public ledger. -/
theorem local_live_change_of_eq {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : LocalGood after cutoff r zs z s)
    (live : after.live = h.live) :
    LiveChange h after (fun b => InflateOwned zs s b ∧ ¬ h.live b) (fun _ => False) := by
  intro b
  have owned : InflateOwned zs s b → h.live b := by
    intro owner
    rw [← live]
    exact local_inflate_owned_live good owner
  rw [live]
  simp only [not_false_eq_true, and_true]
  constructor
  · exact Or.inl
  · rintro (old | ⟨owner, fresh⟩)
    · exact old
    · exact False.elim (fresh (owned owner))

/-- The actual window continuation adds only its returned owned window.
Both genuine allocation failure and the actual successful suffix are covered. -/
theorem leaveWithWindow_live_local {c : Ctx} {l : IL} {h after : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (output : OutputCursorInvariant h r l)
    (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (run : leaveWithWindow c l z h = .ok (rc, after))
    (final : LocalGood after cutoff r zs stream state) :
    LiveChange h after (fun b => InflateOwned zs state b ∧ ¬ h.live b) (fun _ => False) := by
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
    obtain ⟨frame, windowLedger, _, _, _⟩ :=
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
    have live : after.live = heap1.live := congrArg (fun x => x.2.2.2.2.2.2)
      (fastMemoryMetaFrameM_leaveFinalize r c l z E.strm heap1 rc after finish)
    have window : state.window = state1.window := by rw [fields]
    intro b
    change after.live b ↔ (h.live b ∧ ¬ False) ∨ (InflateOwned zs state b ∧ ¬ h.live b)
    rw [live]
    have ledger := updatewindow_local_live good allocator get start bound sep windowRun good1
    simpa only [LiveChange, InflateOwned, window] using ledger b
  · obtain ⟨eqrc, _, stateEq, heapEq⟩ := failure
    subst wr
    subst state1
    unfold leaveWithWindow at run
    rw [bind_app, E.strm, cursor, put, windowRun] at run
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app] at run
    cases run
    have live : (setI heap1 zs { s with mode := MEM }).live = h.live := by
      have shape := shape_setI good1.live.hs { s with mode := MEM }
      have same : setI { h with nalloc := h.nalloc + 1 } zs s = { h with nalloc := h.nalloc + 1 } :=
        tcSetI_same good.live.hs
      rw [fastMemoryMeta_live_eq_of_shape shape, heapEq, same]
      rfl
    exact local_live_change_of_eq final live

/-- The complete actual leave boundary retains every old live object.
The only possible new object is the returned decoder's owned window. -/
theorem inflate_leave_live_local {c : Ctx} {l : IL} {h after : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (run : inflate_leave c l h = .ok (rc, after)) (final : LocalGood after cutoff r zs stream state) :
    LiveChange h after (fun b => InflateOwned zs state b ∧ ¬ h.live b) (fun _ => False) := by
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
  have shape : Shape h heap0 :=
    (shape_put invariant.good.live.hz stream0).trans
      (shape_setI (by simpa only [ZStreamRef.put_istates] using invariant.good.live.hs) state0)
  have live0 : heap0.live = h.live := fastMemoryMeta_live_eq_of_shape shape
  have statics0 : Zlib.Crc32.Proofs.StaticsOK heap0 := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [current.globals]
    exact ⟨rfl, rfl⟩
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update] at run
    have ledger := leaveWithWindow_live_local env0 current.good allocator.1 output0
      statics0 rfl rfl run final
    simpa only [LiveChange, live0] using ledger
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip] at run
    have live : after.live = heap0.live := congrArg (fun x => x.2.2.2.2.2.2)
      (fastMemoryMetaFrameM_leaveFinalize r c l stream0 E.strm heap0 rc after run)
    exact local_live_change_of_eq final (live.trans live0)

#print axioms inflate_leave_live_local
end Zlib.Inflate.Local
