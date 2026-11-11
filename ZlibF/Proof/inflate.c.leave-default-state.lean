import ZlibF.Proof.«inflate.c.default-public»
import ZlibF.Proof.«inflate.c.window-platform»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Retain every default decoder and history clause across the checked
window fields while admitting the actual returned heap. -/
theorem DefaultStateJ.window_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultStateJ h r zs z s)
    (good : Good after r zs stream state) (frame : WindowStateFrame s state)
    (codeViews : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after) (static : after.static = h.static) :
    DefaultStateJ after r zs stream state := by
  refine ⟨⟨good, frame.tables codeViews invariant.tables, frame.pending invariant.pending,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, platform⟩, ?_, ?_, ?_⟩
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
  · exact HeaderMemory.step invariant.header invariant.good current (by rw [frame]) (by rw [frame]) sizes
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
/-- Retain every default decoder and history clause across the checked
counter and checksum fields while admitting the actual returned heap. -/
theorem DefaultStateJ.leave_metadata {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s state : InflateState} (invariant : DefaultStateJ h r zs z s)
    (good : Good after r zs stream state) (frame : LeaveMetadataFrame s state)
    (codeViews : ∀ ref : CodeRef, (Space.get after ref : Option (Array Code)) = Space.get h ref)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after) (static : after.static = h.static) :
    DefaultStateJ after r zs stream state := by
  refine ⟨⟨good, frame.tables codeViews invariant.tables, frame.pending invariant.pending,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, platform⟩, ?_, ?_, ?_⟩
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
  · exact HeaderMemory.step invariant.header invariant.good current (by rw [frame]) (by rw [frame]) sizes
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

/-- RESTORE writes the actual register bit buffer and caller cursors, while
retaining construction state and every requested/default configuration field. -/
theorem DefaultStateJ.restore {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {l : IL} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39) :
    DefaultStateJ (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      r zs (leaveStream z l) (leaveState s l) := by
  obtain ⟨good, pending, held, sizes⟩ :=
    leave_restore_invariant E invariant.good invariant.pending buffers.bits bits
  exact ⟨⟨good, leave_restore_tables l E.hs invariant.tables, pending,
    invariant.lengths, invariant.headerLengths, held, invariant.window,
    invariant.wrapper, invariant.header, invariant.modes, invariant.trailer,
    by simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals,
    sizes.platform invariant.platform⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

/-- A genuine window-allocation failure selects MEM and retains the
complete default relation, including the requested reset configuration. -/
theorem DefaultStateJ.mem_update {h after : Heap} {r : ZStreamRef} {zs : Nat}
    {z stream : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (good : Good after r zs stream { s with mode := MEM })
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after) (static : after.static = h.static) :
    DefaultStateJ after r zs stream { s with mode := MEM } := by
  refine ⟨⟨good, ?_, dataPendingInvariant_idle invariant.pending.sane ?_, ?_, ?_,
    invariant.held, invariant.window, invariant.wrapper, invariant.header,
    Or.inr ?_, ?_, ?_, platform⟩, invariant.requestedBits, invariant.requestedWrap,
    Or.inr (Or.inr (Or.inl rfl))⟩
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

/-- Removing a raw local object cannot create an oversized byte view. -/
theorem platform_free_local {h : Heap} (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (block : Nat) :
    ZlibF.PlatformMemory.ByteObjectsFit (freeWin h (.ref (.blk block) 0)) := by
  intro ref array get
  cases ref with
  | blk b =>
    by_cases same : b = block
    · subst b
      simp only [Space.get, freeWin, upd_same] at get
      cases get
    · have old : h.bytes b = some array := by
        simpa only [Space.get, freeWin, upd_ne _ _ _ _ same] using get
      exact platform (BRef.blk b) array old
  | str index => exact platform (.str index) array get
  | dstate_depth index => exact platform (.dstate_depth index) array get
  | st_dist_code => exact platform .st_dist_code array get
  | st_length_code => exact platform .st_length_code array get

/-- Final local cleanup retains the full initialized decoder relation.
The actual local size and default window size prove the necessary separation. -/
theorem DefaultStateJ.free_local {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {block : Nat} {array : Array UInt8}
    (invariant : DefaultStateJ h r zs z s) (localGet : h.bytes block = some array)
    (localSize : array.size = 4) :
    DefaultStateJ (freeWin h (.ref (.blk block) 0)) r zs z s := by
  have good := good_freeBuf invariant.good (nb := block) (by
    intro w window same
    subst w
    exact default_local_not_window invariant.good localGet localSize invariant.window.1 window)
  have tables : DataTableInvariant (freeWin h (.ref (.blk block) 0)) s := by
    intro active
    have old := invariant.tables active
    constructor
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.lengthTable
      exact ⟨ref, offset, array, pointer, by cases ref <;> exact get, safe⟩
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.distanceTable
      exact ⟨ref, offset, array, pointer, by cases ref <;> exact get, safe⟩
  exact ⟨⟨good, tables, invariant.pending, invariant.lengths, invariant.headerLengths,
    invariant.held, invariant.window, invariant.wrapper, invariant.header, invariant.modes,
    invariant.trailer, invariant.globals, platform_free_local invariant.platform block⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

end Zlib.Inflate.Proofs
