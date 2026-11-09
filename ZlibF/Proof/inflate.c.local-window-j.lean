import ZlibF.Proof.«inflate.c.local-window-effects»
import ZlibF.Proof.«inflate.c.local-default-state»
import ZlibF.Proof.«inflate.c.leave-window»

/-! Actual window updates retain the complete local decoder relation and
private-root ages. The precise allocation origin is preserved for cleanup. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- New-root age comes from the actual before.nextBlk allocation origin. -/
theorem LocalStateJ.window_update {h after : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : LocalStateJ h cutoff r zs z s)
    (good : LocalGood after cutoff r zs stream state) (frame : WindowStateFrame s state)
    (codeViews : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after) (static : after.static = h.static)
    (origin : state.window = s.window ∨ (s.window = .null ∧ state.window = .ref (.blk h.nextBlk) 0)) :
    LocalStateJ after cutoff r zs stream state := by
  refine ⟨⟨good, frame.tables codeViews invariant.tables, frame.pending invariant.pending,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, platform⟩, ?_, ?_, ?_, ?_⟩
  · rw [frame]; exact invariant.lengths
  · rw [frame]; exact invariant.headerLengths
  · rw [frame]; exact invariant.held
  · rw [frame]; exact invariant.window
  · rw [frame]; exact invariant.wrapper
  · rw [frame]; exact invariant.header
  · rw [frame]; exact invariant.modes
  · rw [frame]; exact invariant.trailer
  · change after.static = _
    rw [static]; exact invariant.globals
  · rw [frame]; exact invariant.requestedBits
  · rw [frame]; exact invariant.requestedWrap
  · rw [frame]; exact invariant.phase
  · refine ⟨invariant.roots.stream, invariant.roots.state, ?_⟩
    intro w ptr
    rcases origin with same | ⟨_, fresh⟩
    · rw [same] at ptr
      exact invariant.roots.window w ptr
    · have root : h.nextBlk = w := by
        rw [fresh] at ptr
        exact BRef.blk.inj (Ptr.ref.inj ptr).1
      have stateLive : h.live zs := by simp [Heap.live, invariant.good.live.hs]
      have upper := invariant.good.fresh.lt stateLive
      rw [← root]
      exact Nat.le_trans invariant.roots.state (Nat.le_of_lt upper)

/-- Every actual window branch, including malloc refusal, establishes J on
its returned heap plus the exact source/table views and resource effects. -/
theorem updatewindow_local_state {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {eo : Nat} {source : BRef} {bytes : Array UInt8} {copy : UInt32}
    (invariant : LocalStateJ h cutoff r zs z s) (allocator : z.zalloc = .fn "zcalloc")
    (get : Space.get h source = some bytes) (count : copy.toNat ≤ eo) (bound : eo ≤ bytes.size)
    (unowned : ∀ w, s.window = .ref (.blk w) 0 → source ≠ .blk w) :
    ∃ rc after state, updatewindow (some r) (.ref source eo) copy h = .ok (rc, after) ∧
      LocalStateJ after cutoff r zs z state ∧ WindowStateFrame s state ∧
      Space.get after source = some bytes ∧
      (∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref) ∧
      Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) ∧
      LiveChange h after (fun b => s.window = .null ∧ h.allocOk h.nalloc = true ∧ b = h.nextBlk) (fun _ => False) ∧
      after.nextBlk = h.nextBlk + (if s.window = .null ∧ h.allocOk h.nalloc = true then 1 else 0) ∧
      after.nalloc = h.nalloc + (if s.window = .null then 1 else 0) ∧
      (state.window = s.window ∨ (s.window = .null ∧ state.window = .ref (.blk h.nextBlk) 0)) ∧
      (rc = 0 ∨ (rc = 1 ∧ s.window = .null ∧ state = s ∧ after = setI {h with nalloc := h.nalloc + 1} zs s)) := by
  have separate : Separate (.ref source (eo - copy.toNat)) copy.toNat s.window (2 ^ s.wbits.toNat) := by
    rcases invariant.good.inv.win.block with null | ⟨w, a, window, _, _, _⟩
    · simp [Separate, null]
    · simp [Separate, window, unowned w window]
  obtain ⟨rc, after, state, run, good, frame, sourceView, codes, outcome⟩ :=
    updatewindow_decoder_boundary_local invariant.good allocator get count bound unowned
  obtain ⟨platform, static⟩ := updatewindow_platform_local invariant.good invariant.platform
    allocator get count bound separate run
  have effects := updatewindow_local_effects invariant.good allocator get count bound separate run good.live.hs
  have final := invariant.window_update good frame codes platform static effects.2.2.2.2
  exact ⟨rc, after, state, run, final, frame, sourceView, codes, effects.1,
    effects.2.1, effects.2.2.1, effects.2.2.2.1, effects.2.2.2.2, outcome⟩

#print axioms LocalStateJ.window_update
#print axioms updatewindow_local_state
end Zlib.Inflate.Local
