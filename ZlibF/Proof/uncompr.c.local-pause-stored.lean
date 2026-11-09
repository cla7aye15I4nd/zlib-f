import ZlibF.Proof.«uncompr.c.local-pause-basic»

namespace Zlib.Uncompr.Proof.LocalPause
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
open Zlib.Inflate.Local Zlib.Uncompr.Proof.InflatePause
set_option autoImplicit false

theorem copy_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Zlib.Inflate.Local.LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY)
    (run : runX (inflate_COPY c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  obtain ⟨outcome, _, _, state, _, _, source, current, _, _, _, _, _, _, _, _, _, _, _, kinds, _, _⟩ :=
    Zlib.Inflate.Local.inflate_COPY_boundary_frame E good pending buffers mode
  have selected := xrun_outcome_eq source run
  have same := xrun_state_eq source run current.live.hs get
  rcases kinds with ⟨_, _, eq⟩ | ⟨normal, _⟩ | ⟨normal, _⟩
  · rw [←same, eq]
    simp only [PauseGood, mode]
    decide
  · cases normal.symm.trans selected
  · cases normal.symm.trans selected

theorem copy_start_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (good : Zlib.Inflate.Local.LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = COPY_)
    (run : runX (inflate_COPY_ c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  obtain ⟨outcome, _, _, state, _, _, source, current, _, _, _, _, _, _, _, _, _, _, _, kinds, _, _⟩ :=
    Zlib.Inflate.Local.inflate_COPY_start_boundary_frame E good pending buffers mode
  have selected := xrun_outcome_eq source run
  have same := xrun_state_eq source run current.live.hs get
  rcases kinds with ⟨_, _, eq⟩ | ⟨normal, _⟩ | ⟨normal, _⟩
  · rw [←same, eq]
    change COPY < MEM ∧ COPY ≠ BAD ∧ COPY ≠ DICT
    decide
  · cases normal.symm.trans selected
  · cases normal.symm.trans selected

/-- A rejected stored length first returns normally in BAD. An ordinary
NO_FLUSH leave is a header wait or the real COPY continuation's pause. -/
theorem stored_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED)
    (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_STORED c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  obtain ⟨aligned, _, _⟩ := BYTEBITS_inv buffers.bits
  obtain ⟨outcome, current, used, pull, usedBound, bitInv, _, _, shape, _, _, _, _, kinds, cursor⟩ :=
    NEEDBITS_run_cursor aligned 32 (by decide)
  rcases kinds with normal | wait
  · rw [normal] at pull
    by_cases bad : ((current.hold &&& (0xffff : UInt64)) != ((current.hold >>> 16) ^^^ (0xffff : UInt64))) = true
    · obtain ⟨i, _, source⟩ := inflate_STORED_bad E l current pull bad
      have impossible := xrun_outcome_eq source run
      cases impossible
    · let ready := { s with length := current.hold.toUInt32 &&& 0xffff, mode := COPY_ }
      let heap := setI h zs ready
      let first := { current with hold := 0, bits := 0 }
      have good0 : Zlib.Inflate.Local.LocalGood heap cutoff r zs z ready := invariant.good.decode_update (by rfl)
        (by change HEAD ≤ COPY_ ∧ COPY_ ≤ SYNC; decide)
      have env : Env c heap r zs z ready := ⟨E.strm, E.st, good0.live.hz, good0.live.hs⟩
      have pending : DataPendingInvariant ready := by
        apply dataPendingInvariant_idle (s := ready) invariant.pending.sane
        change COPY_ ≠ LENEXT ∧ COPY_ ≠ DIST ∧ COPY_ ≠ DISTEXT ∧ COPY_ ≠ MATCH
        decide
      have packet : DispatchBuffers heap r first (bs.drop used) :=
        dispatch_consume_local buffers invariant.good good0 rfl
          (fun ref => byte_view_get_setI h zs ready ref)
          (fun ref => byte_view_ro_setI h zs ready ref)
          (by dsimp only [first]; rw [shape]; rfl) cursor usedBound
          ((INITBITS_inv bitInv).1.decode_update zs ready)
      have actual : runX (inflate_COPY_ c) first heap = .ok ((.error Ex.leave, regs), after) := by
        have cut := inflate_STORED_ok E l current pull bad
        rw [cut] at run
        simpa only [flush, Z_NO_FLUSH, Z_TREES, show ((0 : Int32) == 6) = false from rfl,
          Bool.false_eq_true, ↓reduceIte] using run
      exact copy_start_leave_pause env good0 pending packet rfl actual get
  · have source := inflate_STORED_wait (c := c) l current h Ex.leave (by rwa [wait] at pull)
    have same := xrun_state_eq source run E.hs get
    rw [←same]
    simp only [PauseGood, mode]
    decide

theorem stored_dispatch_leave_pause
    {c : Ctx} {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s returned : InflateState} {l regs : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : Zlib.Inflate.Local.LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = STORED ∨ s.mode = COPY_ ∨ s.mode = COPY)
    (flush : c.flush = Z_NO_FLUSH)
    (run : runX (inflate_dispatch c) l h = .ok ((.error Ex.leave, regs), after))
    (get : after.istates zs = some returned) : PauseGood returned := by
  rcases mode with mode | mode | mode
  · exact stored_leave_pause E invariant buffers mode flush ((inflate_dispatch_STORED E l mode).symm.trans run) get
  · exact copy_start_leave_pause E invariant.good invariant.pending buffers mode
      ((inflate_dispatch_COPY_start E l mode).symm.trans run) get
  · exact copy_leave_pause E invariant.good invariant.pending buffers mode
      ((inflate_dispatch_COPY E l mode).symm.trans run) get

#print axioms stored_dispatch_leave_pause
end Zlib.Uncompr.Proof.LocalPause
