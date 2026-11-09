import ZlibF.Proof.«inflate.c.local-leave-finalize»
import ZlibF.Proof.«inflate.c.local-default-state»
import ZlibF.Proof.«inflate.c.leave-default-boundary»

/-! Full local decoder relation across the actual final counter, checksum
and return suffix. No independent history relation is inferred from J. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Retain every default decoder and history clause across the checked
counter and checksum fields while admitting the actual returned heap. -/
theorem LocalStateJ.leave_metadata {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : LocalStateJ h cutoff r zs z s)
    (good : LocalGood after cutoff r zs stream state) (frame : LeaveMetadataFrame s state)
    (codeViews : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after) (static : after.static = h.static) :
    LocalStateJ after cutoff r zs stream state := by
  refine ⟨⟨good, frame.tables codeViews invariant.tables, frame.pending invariant.pending,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, platform⟩, ?_, ?_, ?_, ?_⟩
  · rw [frame]
    exact invariant.lengths
  · rw [frame]
    exact invariant.headerLengths
  · rw [frame]
    exact invariant.held
  · rw [frame]
    exact invariant.window
  · rw [frame]
    exact invariant.wrapper
  · rw [frame]
    exact invariant.header
  · rw [frame]
    exact invariant.modes
  · rw [frame]
    exact invariant.trailer
  · change after.static = _
    rw [static]
    exact invariant.globals
  · rw [frame]
    exact invariant.requestedBits
  · rw [frame]
    exact invariant.requestedWrap
  · rw [frame]
    exact invariant.phase

  · refine ⟨invariant.roots.stream, invariant.roots.state, ?_⟩
    intro w ptr
    rw [frame] at ptr
    exact invariant.roots.window w ptr

/-- The actual complete post-window suffix retains the full default state
relation and default allocator, on the same checked returning execution. -/
theorem leaveFinalize_local_state {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z current : ZStream} {s : InflateState} (E : Env c h r zs current s)
    (invariant : LocalStateJ h cutoff r zs current s) (allocator : DefAlloc current)
    (output : LeaveOutputView h l) (cursor : z.next_out = l.put) (count : z.avail_out = l.left) :
    ∃ rc after stream state, leaveFinalize c l z h = .ok (rc, after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DefAlloc stream := by
  have statics : Zlib.Crc32.Proofs.StaticsOK h := by
    unfold Zlib.Crc32.Proofs.StaticsOK
    rw [invariant.globals]
    exact ⟨rfl, rfl⟩
  obtain ⟨rc, after, stream, state, run, good, frame, views, ret, codes, static⟩ :=
    leaveFinalize_local_safe E invariant.good output statics cursor count
  have sizes : ByteViewSizes h after := by
    intro ref
    rw [views ref]
  have final := invariant.leave_metadata good frame codes (sizes.platform invariant.platform) static
  have fixed := streamFrameM_leaveFinalize r c l z E.strm h rc after run
  exact ⟨rc, after, stream, state, run, final,
    fixed.allocator invariant.good.live.hz good.live.hz allocator⟩


#print axioms LocalStateJ.leave_metadata
#print axioms leaveFinalize_local_state
end Zlib.Inflate.Local
