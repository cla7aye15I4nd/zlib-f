import ZlibF.Proof.«inflate.c.header-progress»
import ZlibF.Proof.«inflate.c.leave-restore»
import ZlibF.Proof.«inflate.c.stored-call»
import ZlibF.Proof.«inflate.c.origin-history»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Real LOAD uses the stored held word. New caller buffer bindings do not
alter the field-word index retained in the decoder record. -/
theorem LOAD_header_progress {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {received : List Bool}
    (E : Env c h r zs z s) (l : IL) (progress : LenlensProgress s s.hold s.bits received) :
    ∃ regs, runX (LOAD c.strm c.st) l h = .ok ((.ok (), regs), h) ∧
      LenlensProgress s regs.hold regs.bits received := by
  exact ⟨_, LOAD_run E l, progress⟩

/-- The actual leave RESTORE prefix saves the same word and field prefix. -/
theorem leaveRestore_header_progress {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {received : List Bool}
    (E : Env c h r zs z s) (progress : LenlensProgress s l.hold l.bits received) :
    ∃ state after,
      leaveRestore c l h = .ok ((), after) ∧ after.istates zs = some state ∧
      LenlensProgress state state.hold state.bits received := by
  exact ⟨leaveState s l, _, leaveRestore_run E, by simp, progress⟩

/-- The real RESTORE macro exposes the same stored boundary. -/
theorem RESTORE_header_progress {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {received : List Bool}
    (E : Env c h r zs z s) (progress : LenlensProgress s l.hold l.bits received) :
    ∃ state after, runX (RESTORE c.strm c.st) l h = .ok ((.ok (), l), after) ∧
      after.istates zs = some state ∧ LenlensProgress state state.hold state.bits received := by
  refine ⟨leaveState s l, setI (r.put h (leaveStream z l)) zs (leaveState s l), ?_, by simp, progress⟩
  unfold RESTORE
  rw [E.strm, E.st]
  simp [runX_bind, runX_get, runX_lift, wrZ_eq, E.hz, ZStreamRef.put_istates, wrI_eq, E.hs,
    leaveState, leaveStream]

/-- Caller rebuffering preserves the actual private record. The new unread
bytes are unrestricted by this phase relation. -/
theorem rebuffer_header_progress {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {received : List Bool}
    (before : DefaultOriginState h r zs z s) (edit : Rebuffer h after r)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after)
    (progress : LenlensProgress s s.hold s.bits received) :
    ∃ stream, DefaultOriginState after r zs stream s ∧
      after.istates zs = some s ∧ LenlensProgress s s.hold s.bits received := by
  obtain ⟨stream, current⟩ := rebuffer_default_origin before edit platform
  exact ⟨stream, current, current.good.live.hs, progress⟩

#print axioms LOAD_header_progress
#print axioms leaveRestore_header_progress
#print axioms RESTORE_header_progress
#print axioms rebuffer_header_progress
end Zlib.Inflate.Proofs
