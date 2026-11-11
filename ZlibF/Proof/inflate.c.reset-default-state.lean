import ZlibF.Proof.«inflate.c.default-foundation»
import ZlibF.Proof.«inflate.c.reset»
import ZlibF.Proof.«inflate.c.block-type»
import ZlibF.Proof.«inflate.c.init»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated reset-keep call returns the stream to HEAD while
retaining the initialized default configuration and window. -/
theorem inflateResetKeep_default_state
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) :
    ∃ after,
      C.run (inflateResetKeep (some r)) h = .ok (Z_OK, after) ∧
      after = setI (r.put h (resetKeepStream z s)) zs (resetKeepState zs s) ∧
      DefaultStateJ after r zs (resetKeepStream z s) (resetKeepState zs s) ∧
      (∀ b, after.live b ↔ h.live b) := by
  obtain ⟨after, run, exactHeap, good, live⟩ :=
    inflateResetKeep_safe invariant.good
  subst after
  let stream := resetKeepStream z s
  let state := resetKeepState zs s
  have stateMode : state.mode = HEAD := rfl
  have sizes : ByteViewSizes h (setI (r.put h stream) zs state) :=
    (byte_view_sizes_stream_put h r stream).trans (byte_view_sizes_setI _ zs state)
  have pending : DataPendingInvariant state :=
    dataPendingInvariant_head (by rfl) stateMode
  have table : DataTableInvariant (setI (r.put h stream) zs state) state :=
    dataTableInvariant_inactive (by rw [stateMode]; unfold DataTableMode; decide)
  have result : DefaultStateJ (setI (r.put h stream) zs state) r zs stream state := by
    refine ⟨⟨good, table, pending, ?_, ?_, ?_, ?_, ?_, ?_, Or.inl stateMode,
      ?_, ?_, sizes.platform invariant.platform⟩, ?_, ?_, Or.inl stateMode⟩
    · intro active
      rw [stateMode] at active
      contradiction
    · intro active
      rw [stateMode] at active
      contradiction
    · change (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat
      decide
    · rcases invariant.window with range | ⟨zero, null, _, nonraw⟩
      · exact Or.inl range
      · exact Or.inr ⟨zero, null, rfl, nonraw⟩
    · exact invariant.wrapper
    · exact fun cause => cause.elim (fun attached => absurd rfl attached) (fun read => absurd rfl read.1)
    · rintro (active | active) <;> rw [stateMode] at active <;> contradiction
    · simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals
    · exact invariant.requestedBits
    · exact invariant.requestedWrap
  exact ⟨_, run, rfl, result, live⟩

#print axioms inflateResetKeep_default_state


/-- Freeing the window (or nothing) cannot create an oversized byte view. -/
theorem platform_freeWin {h : Heap} (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (p : BPtr) :
    ZlibF.PlatformMemory.ByteObjectsFit (freeWin h p) := by
  intro ref array get
  unfold freeWin at get
  split at get
  · rename_i block
    cases ref with
    | blk b =>
      by_cases same : b = block
      · subst b
        simp only [Space.get, upd_same] at get
        cases get
      · have old : h.bytes b = some array := by
          simpa only [Space.get, upd_ne _ _ _ _ same] using get
        exact platform (BRef.blk b) array old
    | str index => exact platform (.str index) array get
    | dstate_depth index => exact platform (.dstate_depth index) array get
    | st_dist_code => exact platform .st_dist_code array get
    | st_length_code => exact platform .st_length_code array get
  · exact platform ref array get

theorem platform_reset2Heap {h : Heap} (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (wb : Int32) (s : InflateState) : ZlibF.PlatformMemory.ByteObjectsFit (reset2Heap h wb s) := by
  unfold reset2Heap
  split
  · exact platform_freeWin platform s.window
  · exact platform

theorem reset2Heap_static (h : Heap) (wb : Int32) (s : InflateState) :
    (reset2Heap h wb s).static = h.static := by
  unfold reset2Heap freeWin
  split
  · split <;> rfl
  · rfl


end Zlib.Inflate.Proofs
