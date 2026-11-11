import ZlibF.Proof.«inflate.c.stream-frame-run»
import ZlibF.Proof.«inflate.c.leave-all-wrappers»
import ZlibF.Proof.«inflate.c.dispatch-default-state»
import ZlibF.Proof.«inflate.c.memory-meta-frame-run»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Creating the real four-byte local object retains every existing byte
view and its read-only flag. Freshness excludes aliasing the new object. -/
theorem byte_view_syncAlloc {h : Heap} (fresh : Fresh h) {ref : BRef} {array : Array UInt8}
    (get : Space.get h ref = some array) :
    Space.get (syncAlloc h) ref = some array ∧ Space.ro (syncAlloc h) ref = Space.ro h ref := by
  cases ref with
  | blk block =>
    have different : block ≠ h.nextBlk := by
      intro same
      subst block
      have absent := (fresh_dead fresh (Nat.le_refl h.nextBlk)).1
      change h.bytes h.nextBlk = some array at get
      rw [get] at absent
      cases absent
    constructor
    · exact (syncAlloc_bytes_ne h different).trans get
    · simp only [Space.ro, syncAlloc, upd_ne _ _ _ _ different]
  | str index => exact ⟨get, rfl⟩
  | dstate_depth index => exact ⟨get, rfl⟩
  | st_dist_code => exact ⟨get, rfl⟩
  | st_length_code => exact ⟨get, rfl⟩

/-- Local allocation does not change the stream's owned object graph. -/
theorem streamOwned_syncAlloc (h : Heap) (r : ZStreamRef) (block : Nat) :
    StreamOwned (syncAlloc h) r block ↔ StreamOwned h r block := by
  simp only [StreamOwned, ZStreamRef.get_syncAlloc, syncAlloc_istates, syncAlloc_dstates]

/-- Public caller ranges remain valid after the actual local declaration. -/
theorem callerRange_syncAlloc {h : Heap} {r : ZStreamRef} (fresh : Fresh h)
    {pointer : BPtr} {size : Nat} {writing : Bool} (range : CallerRange h r pointer size writing) :
    CallerRange (syncAlloc h) r pointer size writing := by
  rcases range with null | ⟨readable, writable, unowned⟩
  · exact Or.inl null
  · refine Or.inr ⟨?_, ?_, ?_⟩
    · obtain ⟨bytes, null | ⟨ref, offset, array, pointerEq, get, bound, values⟩⟩ := readable
      · exact ⟨bytes, Or.inl null⟩
      · exact ⟨bytes, Or.inr ⟨ref, offset, array, pointerEq,
          (byte_view_syncAlloc fresh get).1, bound, values⟩⟩
    · intro writingEq
      rcases writable writingEq with null | ⟨ref, offset, array, pointerEq, get, ro, bound⟩
      · exact Or.inl null
      · exact Or.inr ⟨ref, offset, array, pointerEq, (byte_view_syncAlloc fresh get).1,
          (byte_view_syncAlloc fresh get).2.trans ro, bound⟩
    · intro block root owned
      exact unowned block root ((streamOwned_syncAlloc h r block).mp owned)

/-- The public input/output buffer domain survives the four-byte local allocation. -/
theorem streamBuffers_syncAlloc {h : Heap} {r : ZStreamRef} (fresh : Fresh h)
    (buffers : StreamBuffers h r) : StreamBuffers (syncAlloc h) r := by
  obtain ⟨z, get, input, output, separate⟩ := buffers
  exact ⟨z, by simpa only [ZStreamRef.get_syncAlloc] using get,
    callerRange_syncAlloc fresh input, callerRange_syncAlloc fresh output, separate⟩

/-- The local object has its actual bounded size. No additional caller
size assumption or allocator contract is introduced. -/
theorem default_platform_syncAlloc {h : Heap} (platform : ZlibF.PlatformMemory.ByteObjectsFit h) :
    ZlibF.PlatformMemory.ByteObjectsFit (syncAlloc h) := by
  have bounded : (syncJunk h).size < ZlibF.PlatformMemory.byteObjectLimit := by
    change 4 < 2 ^ 63
    decide
  exact (platform.with_bytes (block := h.nextBlk) bounded).of_storage_eq rfl rfl rfl

/-- The initialized default relation is stable under the actual local
allocation performed at the start of public inflate. -/
theorem default_state_syncAlloc {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) :
    DefaultStateJ (syncAlloc h) r zs z s := by
  have tables : DataTableInvariant (syncAlloc h) s := by
    intro active
    have old := invariant.tables active
    constructor
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.lengthTable
      exact ⟨ref, offset, array, pointer, by cases ref <;> exact get, safe⟩
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.distanceTable
      exact ⟨ref, offset, array, pointer, by cases ref <;> exact get, safe⟩
  exact ⟨⟨good_syncAlloc invariant.good, tables, invariant.pending, invariant.lengths,
    invariant.headerLengths, invariant.held, invariant.window, invariant.wrapper,
    invariant.header, invariant.modes, invariant.trailer, invariant.globals,
    default_platform_syncAlloc invariant.platform⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

end Zlib.Inflate.Proofs
