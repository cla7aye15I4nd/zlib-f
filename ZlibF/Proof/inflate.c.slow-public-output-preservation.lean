import ZlibF.Proof.«inflate.c.slow-pending-output-public»
import ZlibF.Proof.«inflate.c.leave-output-footprint»
import ZlibF.Proof.«inflate.c.caller-input-frame»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false
/-- Actual public leave touches only owned storage, using just its real
payload safety packet. No whole default invariant is assumed. -/
theorem inflate_leave_payload_frame {c : Ctx} {l : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (allocator : z.zalloc = .fn "zcalloc") (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (run : inflate_leave c l h = .ok (rc, after)) :
    Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) := by
  let stream0 := leaveStream z l
  let state0 := leaveState s l
  let heap0 := setI (r.put h stream0) zs state0
  obtain ⟨current, _pending0, _held0, _sizes0⟩ := leave_restore_invariant E good pending buffers.bits bits
  have env0 : Env c heap0 r zs stream0 state0 :=
    ⟨E.strm, E.st, current.live.hz, current.live.hs⟩
  have views0 : ∀ ref : BRef, (Space.get heap0 ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have output0 : OutputCursorInvariant heap0 r l :=
    ⟨callerRange_transport good current rfl views0 (by
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
    have frame := leaveWithWindow_frame_public env0 current allocator output0 rfl rfl run
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

/-- The exact emitted output array survives the real public return,
including window update and its allocation-failure branch. -/
theorem inflate_leave_output_array {c : Ctx} {l : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {rc : Int32}
    {dest : BRef} {off : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (allocator : z.zalloc = .fn "zcalloc") (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (put : l.put = .ref dest off) (get : Space.get h dest = some array)
    (run : inflate_leave c l h = .ok (rc, after)) : Space.get after dest = some array := by
  have frame := inflate_leave_payload_frame E good pending allocator buffers bits run
  have readable : CallerRange h r l.put l.left.toNat false := by
    rcases buffers.output.range with null | ⟨readable, _writable, outside⟩
    · exact Or.inl null
    · exact Or.inr ⟨readable, (fun impossible => by cases impossible), outside⟩
  apply frame_byte_view_get frame get (off := off)
  intro b root
  exact caller_byte_root_outside good get (by rw [← put]; exact readable) root

/-- Public return exposes the exact restored input and output cursors on
both ordinary and window-allocation-failure branches. -/
theorem inflate_leave_cursors {c : Ctx} {l : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s : InflateState} {bs : List UInt8} {rc : Int32}
    (E : Env c h r zs z s) (good : Good h r zs z s) (pending : DataPendingInvariant s)
    (allocator : z.zalloc = .fn "zcalloc") (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (buffers : DispatchBuffers h r l bs) (tables : DataTableInvariant h s) (bits : l.bits.toNat ≤ 39)
    (run : inflate_leave c l h = .ok (rc, after)) (get : r.get after = some stream) :
    stream.next_in = l.next ∧ stream.avail_in = l.have_ ∧ stream.next_out = l.put ∧ stream.avail_out = l.left := by
  obtain ⟨rc0, heap, observed, state, actual, current, _tables, _pending, _held, outcome, _static⟩ :=
    inflate_leave_public_accounting E good allocator statics buffers tables pending bits
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have streamEq : observed = stream := Option.some.inj (current.live.hz.symm.trans get)
  subst observed
  rcases outcome with normal | failure
  · rw [normal.2.1]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [failure.2.2]
    exact ⟨rfl, rfl, rfl, rfl⟩

#print axioms inflate_leave_payload_frame
#print axioms inflate_leave_output_array
#print axioms inflate_leave_cursors
end Zlib.Inflate.Proofs.SlowInputFragment
