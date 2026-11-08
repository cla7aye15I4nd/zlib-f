import ZlibF.Proof.«inflate.c.default-run-output-frame»
import ZlibF.Proof.«inflate.c.live-frame-leave»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Enlarge the explicitly permitted private-object footprint. -/
theorem inflate_frame_mono {h after : Heap} {small large : Nat → Prop}
    (frame : Frame h after small) (included : ∀ b, small b → large b) : Frame h after large := by
  obtain ⟨statics, alloc, garbage, next, count, objects⟩ := frame
  exact ⟨statics, alloc, garbage, next, count,
    fun b live outside => objects b live (fun changed => outside (included b changed))⟩

theorem RecordFrame.owned_frame {h after : Heap} {r : ZStreamRef} {zs : Nat} (state : InflateState)
    (frame : RecordFrame r (some (.tab zs)) h after) :
    Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs state b) := by
  apply inflate_frame_mono frame.1
  intro b allowed
  rcases allowed with root | decoder
  · exact Or.inl root
  · exact Or.inr (Or.inl decoder)

/-- The actual counter/checksum/return suffix changes only its records.
The observer covers every successful source run, with no callee assumption. -/
theorem recordFrameM_leaveFinalize (r : ZStreamRef) (c : Ctx) (l : IL) (z : ZStream)
    (root : c.strm = some r) : RecordFrameM r c.st (leaveFinalize c l z) := by
  unfold leaveFinalize
  rw [root]
  repeat' first
    | with_reducible exact recordFrameM_pure r c.st _
    | with_reducible exact recordFrameM_ldS r c.st _
    | with_reducible exact recordFrameM_wrS r c.st _
    | with_reducible exact recordFrameM_UPDATE_CHECK r c.st _ _ _ _
    | with_reducible exact recordFrameM_ptr_add r c.st _ _
    | with_reducible exact recordFrameM_chkI32 r c.st _
    | with_reducible exact recordFrameM_wrZ r c.st _
    | with_reducible apply recordFrameM_ite
    | with_reducible refine recordFrameM_bind ?_ (fun _ => ?_)
    | rfl

/-- Successful window copy changes only private storage. Genuine failed
allocation changes the attempt counter and MEM record, without freeing
caller storage. The suffix is the actual source continuation. -/
theorem leaveWithWindow_frame_public {c : Ctx} {l : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {rc : Int32}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (output : OutputCursorInvariant h r l)
    (cursor : z.next_out = l.put) (count : z.avail_out = l.left)
    (run : leaveWithWindow c l z h = .ok (rc, after)) :
    Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) := by
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
  obtain ⟨wr, heap1, state1, windowRun, good1, _, _sourceView, _, outcome⟩ :=
    updatewindow_decoder_boundary (copy := l.out_ - z.avail_out) good allocator get start bound unowned
  rcases outcome with success | failure
  · subst wr
    have endpoint : off - (l.out_ - z.avail_out).toNat + (l.out_ - z.avail_out).toNat = off :=
      Nat.sub_add_cancel start
    have actualWindow : C.run (updatewindow (some r)
        (.ref ref (off - (l.out_ - z.avail_out).toNat + (l.out_ - z.avail_out).toNat))
        (l.out_ - z.avail_out)) h = .ok (0, heap1) := by
      simpa only [C.run, endpoint] using windowRun
    have frame := updatewindow_frame_public good allocator get (by omega) sep actualWindow
    have ledger := updatewindow_live_public good allocator get (by omega) sep actualWindow good1.live.hs
    unfold leaveWithWindow at run
    rw [bind_app, E.strm, cursor, put, windowRun] at run
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at run
    have finish := recordFrameM_leaveFinalize r c l z E.strm heap1 rc after run
    rw [E.st] at finish
    exact frame_trans_live frame (finish.owned_frame s)
      (fun b live => (ledger b).mpr (Or.inl ⟨live, fun impossible => impossible⟩))
  · obtain ⟨eqrc, _, stateEq, heapEq⟩ := failure
    subst wr
    subst state1
    unfold leaveWithWindow at run
    rw [bind_app, E.strm, cursor, put, windowRun] at run
    simp only [show ((1 : Int32) != 0) = true from rfl, ↓reduceIte, bind_app, E.st,
      setMode_tab good1.live.hs, pure_app] at run
    cases run
    have same : setI { h with nalloc := h.nalloc + 1 } zs s = { h with nalloc := h.nalloc + 1 } :=
      tcSetI_same good.live.hs
    rw [heapEq, same]
    have attempt : Frame h { h with nalloc := h.nalloc + 1 }
        (fun b => StreamRoot r b ∨ InflateOwned zs s b) := by
      exact ⟨rfl, rfl, rfl, Nat.le_refl _, by change h.nalloc ≤ h.nalloc + 1; omega,
        fun _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    have updated := RecordFrame.setI r zs (show ({ h with nalloc := h.nalloc + 1 } : Heap).istates zs = some s from E.hs) { s with mode := MEM }
    exact frame_trans_live attempt (updated.owned_frame s) (fun _ live => live)

/-- RESTORE and the actual optional window/return continuation change
only the stream, decoder and its incoming owned window. -/
theorem inflate_leave_frame_public {c : Ctx} {l : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (run : inflate_leave c l h = .ok (rc, after)) :
    Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  have current := invariant.restore E buffers bits
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport invariant.good current.good rfl views0 (by
      intro ref
      rw [byte_view_ro_setI, byte_view_ro_stream_put]) buffers.output.range,
      buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  have preFrame : RecordFrame r (some (.tab zs)) h heap0 :=
    RecordFrame.stream_state E.hz E.hs stream0 state0
  have liveNext : ∀ b, h.live b → heap0.live b :=
    fun b live => (preFrame.2.2.1.live b).mpr live
  by_cases update : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = true
  · rw [inflate_leave_restore_cut E, leaveAfterRestore_window env0 update] at run
    have frame := leaveWithWindow_frame_public env0 current.good allocator.1 output0 rfl rfl run
    have oldFrame : Frame heap0 after (fun b => StreamRoot r b ∨ InflateOwned zs s b) := by
      simpa only [state0, leaveState, InflateOwned] using frame
    exact frame_trans_live (preFrame.owned_frame s) oldFrame liveNext
  · have skip : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
      (s.mode < CHECK || c.flush != Z_FINISH))) = false := by
      cases eq : (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) <;> simp_all
    rw [inflate_leave_restore_cut E, leaveAfterRestore_no_window env0 skip] at run
    have finish := recordFrameM_leaveFinalize r c l stream0 E.strm heap0 rc after run
    rw [E.st] at finish
    exact frame_trans_live (preFrame.owned_frame s) (finish.owned_frame s) liveNext

#print axioms inflate_leave_frame_public
end Zlib.Inflate.Proofs
