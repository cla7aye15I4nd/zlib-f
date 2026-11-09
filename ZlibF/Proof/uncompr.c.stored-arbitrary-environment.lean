import ZlibF.Proof.«uncompr.c.stored-exact-completion»

namespace Zlib.Uncompr.Proof.StoredArbitraryEnvironment
open C Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The fixed four-object layout, with arbitrary fresh-memory integers,
initial destination bytes, allocator index/oracle and address metadata.
Only the static tables and the remaining old witness objects stay fixed. -/
def heap (payload : List UInt8) (output : Array UInt8) (garbage : Nat→Nat→UInt64)
    (oracle : Nat→Bool) (event : Nat) (base : ByteBaseRef→Fin 8) : Heap :=
  {StoredEntry.heap payload with
    bytes:=upd (StoredEntry.heap payload).bytes 3 (some output)
    garbage:=garbage,allocOk:=oracle,nalloc:=event,byteBase:=base}

private theorem raw_cell (h : Heap) (block : Nat) (value : UInt64)
    (get : h.bytes block=some (lengthBytes value).toArray) (ro : h.ro block=false) :
    LengthCell h (.ref (.blk block) 0) value := by
  constructor
  · refine Or.inr ⟨.blk block,0,_,rfl,get,by simp [lengthBytes],?_⟩
    simp only [List.toList_toArray,List.drop_zero]
    symm
    apply List.take_of_length_le
    simp [lengthBytes]
  · exact Or.inr ⟨.blk block,0,_,rfl,get,ro,by simp [lengthBytes]⟩

/-- All actual caller-domain obligations can hold for every garbage
function and every initial output array of the required size. No zeroed
fresh-memory or output assumption is hidden in this witness family. -/
theorem domain (payload : List UInt8) (output : Array UInt8) (garbage : Nat→Nat→UInt64)
    (oracle : Nat→Bool) (event : Nat) (base : ByteBaseRef→Fin 8)
    (small : payload.length<65536) (size : output.size=payload.length) :
    Fresh (heap payload output garbage oracle event base) ∧
    LibraryGlobals (heap payload output garbage oracle event base) ∧
    ZlibF.PlatformMemory.ByteObjectsFit (heap payload output garbage oracle event base) ∧
    LengthCell (heap payload output garbage oracle event base) (.ref (.blk 1) 0)
      (UInt64.ofNat (StoredWire.wire payload).length) ∧
    LengthCell (heap payload output garbage oracle event base) (.ref (.blk 2) 0)
      (UInt64.ofNat payload.length) := by
  have fresh : Fresh (heap payload output garbage oracle event base) := by
    intro block lower live
    have different : block≠3 := by change 4≤block at lower;omega
    apply StoredEntry.entry_fresh payload block lower
    simpa only [heap,Heap.live,upd_ne _ _ _ _ different] using live
  have bound : output.size<ZlibF.PlatformMemory.byteObjectLimit := by
    rw [size]
    unfold ZlibF.PlatformMemory.byteObjectLimit
    omega
  have platform := (StoredEntry.entry_platform payload small).with_bytes (block:=3) bound
  refine ⟨fresh,rfl,platform.of_storage_eq rfl rfl rfl,?_,?_⟩
  · apply raw_cell
    · simp [heap,StoredEntry.heap]
    · rfl
  · apply raw_cell
    · simp [heap,StoredEntry.heap]
    · rfl

/-- Actual complete counted decompression and both exact scalar reads for
every payload below 65536, including empty, every garbage function and
every legal initial output content. NoAllocationFailure is an explicit
success premise. The four root indices and whole-array layout remain
fixed; this theorem is not the unrestricted public utility contract. -/
theorem uncompress2_z_stored (payload : List UInt8) (output : Array UInt8)
    (garbage : Nat→Nat→UInt64) (oracle : Nat→Bool) (event : Nat) (base : ByteBaseRef→Fin 8)
    (small : payload.length<65536) (size : output.size=payload.length)
    (success : ∀i,oracle i=true) :
    ∃after,C.run (Zlib.Uncompr.uncompress2_z (.ref (.blk 3) 0) (.ref (.blk 2) 0)
      (.ref (.blk 0) 0) (.ref (.blk 1) 0)) (heap payload output garbage oracle event base)=.ok (Z_OK,after) ∧
      after.bytes 3=some payload.toArray ∧
      LengthCell after (.ref (.blk 1) 0) (UInt64.ofNat (StoredWire.wire payload).length) ∧
      LengthCell after (.ref (.blk 2) 0) (UInt64.ofNat payload.length) ∧
      Zlib.Gzguts.load64 (.ref (.blk 1) 0) after=.ok (UInt64.ofNat (StoredWire.wire payload).length,after) ∧
      Zlib.Gzguts.load64 (.ref (.blk 2) 0) after=.ok (UInt64.ofNat payload.length,after) ∧
      Zlib.Decodes [] (StoredWire.wire payload) payload := by
  obtain ⟨fresh,globals,platform,inputCell,outputCell⟩ := domain payload output garbage oracle event base small size
  exact StoredExactCompletion.uncompress2_z_stored_exact (heap payload output garbage oracle event base)
    payload output small fresh globals platform success rfl
    (by simp [heap,StoredEntry.heap]) (by simp [heap]) size rfl inputCell outputCell

#print axioms domain
#print axioms uncompress2_z_stored
end Zlib.Uncompr.Proof.StoredArbitraryEnvironment
