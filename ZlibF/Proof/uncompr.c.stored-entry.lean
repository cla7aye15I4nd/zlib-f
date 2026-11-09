import ZlibF.Math.UncompressStoredWire
import ZlibF.Proof.«uncompr.c.local-state-entry»
import ZlibF.Spec.Public.Utilities

namespace Zlib.Uncompr.Proof.StoredEntry
open C Zlib.Gzguts ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Loop
set_option autoImplicit false
set_option maxHeartbeats 1000000

def heap (payload : List UInt8) : Heap :=
  { witnessHeap with
    bytes := upd (upd (upd (upd witnessHeap.bytes 0 (some (StoredWire.wire payload).toArray))
      1 (some (lengthBytes (UInt64.ofNat (StoredWire.wire payload).length)).toArray))
      2 (some (lengthBytes (UInt64.ofNat payload.length)).toArray))
      3 (some (Array.replicate payload.length 0))
    nextBlk := 4 }

theorem wire_length (payload : List UInt8) : (StoredWire.wire payload).length = payload.length + 11 := by
  simp [StoredWire.wire,ZlibF.Spec.le16,ZlibF.Spec.be32]

theorem entry_fresh (payload : List UInt8) : Fresh (heap payload) := by
  intro b bound live
  have n0 : b ≠ 0 := by change 4 ≤ b at bound;omega
  have n1 : b ≠ 1 := by change 4 ≤ b at bound;omega
  have n2 : b ≠ 2 := by change 4 ≤ b at bound;omega
  have n3 : b ≠ 3 := by change 4 ≤ b at bound;omega
  simp [heap,witnessHeap,Heap.empty,Heap.live,n0,n1,n2,n3] at live

theorem entry_globals (payload : List UInt8) : LibraryGlobals (heap payload) := rfl

theorem entry_platform (payload : List UInt8) (small : payload.length < 65536) :
    ZlibF.PlatformMemory.ByteObjectsFit (heap payload) := by
  have wireBound : (StoredWire.wire payload).toArray.size < ZlibF.PlatformMemory.byteObjectLimit := by
    simp only [List.size_toArray,wire_length,ZlibF.PlatformMemory.byteObjectLimit]
    omega
  have cellBound (n : UInt64) : (lengthBytes n).toArray.size < ZlibF.PlatformMemory.byteObjectLimit := by
    simp [lengthBytes,ZlibF.PlatformMemory.byteObjectLimit]
  have outputBound : (Array.replicate payload.length (0:UInt8)).size < ZlibF.PlatformMemory.byteObjectLimit := by
    simp only [Array.size_replicate,ZlibF.PlatformMemory.byteObjectLimit]
    omega
  have fit := (((inflate_default_witness_platform.with_bytes (block := 0) wireBound).with_bytes
    (block := 1) (cellBound (UInt64.ofNat (StoredWire.wire payload).length))).with_bytes
    (block := 2) (cellBound (UInt64.ofNat payload.length))).with_bytes (block := 3) outputBound
  exact fit.of_storage_eq rfl rfl rfl

theorem entry_input_cell (payload : List UInt8) :
    LengthCell (heap payload) (.ref (.blk 1) 0) (UInt64.ofNat (StoredWire.wire payload).length) := by
  have get : Space.get (heap payload) (BRef.blk 1) =
      some (lengthBytes (UInt64.ofNat (StoredWire.wire payload).length)).toArray := by simp [heap,Space.get]
  constructor
  · exact Or.inr ⟨.blk 1,0,_,rfl,get,by simp [lengthBytes],by
      simp only [List.toList_toArray,List.drop_zero]
      symm
      apply List.take_of_length_le
      simp [lengthBytes]⟩
  · exact Or.inr ⟨.blk 1,0,_,rfl,get,rfl,by simp [lengthBytes]⟩

theorem entry_output_cell (payload : List UInt8) :
    LengthCell (heap payload) (.ref (.blk 2) 0) (UInt64.ofNat payload.length) := by
  have get : Space.get (heap payload) (BRef.blk 2) =
      some (lengthBytes (UInt64.ofNat payload.length)).toArray := by simp [heap,Space.get]
  constructor
  · exact Or.inr ⟨.blk 2,0,_,rfl,get,by simp [lengthBytes],by
      simp only [List.toList_toArray,List.drop_zero]
      symm
      apply List.take_of_length_le
      simp [lengthBytes]⟩
  · exact Or.inr ⟨.blk 2,0,_,rfl,get,rfl,by simp [lengthBytes]⟩

theorem entry_bytes (payload : List UInt8) (small : payload.length < 65536) :
    Bytes (heap payload) (.ref (.blk 0) 0) (UInt64.ofNat (StoredWire.wire payload).length).toNat
      (StoredWire.wire payload) := by
  have bounded : (StoredWire.wire payload).length < 2^64 := by rw [wire_length];omega
  rw [UInt64.toNat_ofNat',Nat.mod_eq_of_lt bounded]
  exact Or.inr ⟨.blk 0,0,(StoredWire.wire payload).toArray,rfl,
    by simp [Space.get,heap],by simp,by simp⟩

theorem entry_writable (payload : List UInt8) (small : payload.length < 65536) :
    Writable (heap payload) (.ref (.blk 3) 0) (UInt64.ofNat payload.length).toNat := by
  rw [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : payload.length < 2^64)]
  exact Or.inr ⟨.blk 3,0,Array.replicate payload.length 0,rfl,by simp [Space.get,heap],rfl,by simp⟩

/-- These are the actual valid caller premises of the original counted
utility, including canonical globals and all scalar/data separations. -/
theorem entry_domain (payload : List UInt8) (small : payload.length < 65536) :
    Fresh (heap payload) ∧ LibraryGlobals (heap payload) ∧
    ZlibF.PlatformMemory.ByteObjectsFit (heap payload) ∧
    LengthCell (heap payload) (.ref (.blk 1) 0) (UInt64.ofNat (StoredWire.wire payload).length) ∧
    LengthCell (heap payload) (.ref (.blk 2) 0) (UInt64.ofNat payload.length) ∧
    Bytes (heap payload) (.ref (.blk 0) 0) (UInt64.ofNat (StoredWire.wire payload).length).toNat
      (StoredWire.wire payload) ∧
    Writable (heap payload) (.ref (.blk 3) 0) (UInt64.ofNat payload.length).toNat ∧
    UtilitySeparation (.ref (.blk 3) 0) (UInt64.ofNat payload.length).toNat
      (.ref (.blk 0) 0) (UInt64.ofNat (StoredWire.wire payload).length).toNat
      (.ref (.blk 2) 0) (.ref (.blk 1) 0) := by
  exact ⟨entry_fresh payload,entry_globals payload,entry_platform payload small,
    entry_input_cell payload,entry_output_cell payload,entry_bytes payload small,entry_writable payload small,
    by simp [UtilitySeparation,Separate]⟩

/-- The complete stored wire and destination each fit the first actual
UInt32 caller chunk. This is a per-call stored-block bound, not a new
restriction on the general utility contract. -/
theorem first_chunk_fits (payload : List UInt8) (small : payload.length < 65536) :
    (StoredWire.wire payload).length < 2^32 ∧ payload.length < 2^32 := by
  rw [wire_length]
  omega

/-- Every stored payload in the 16-bit length range has a real public-domain
entry with canonical globals. Actual initialization reaches the original
utility loop and finish on the same heap; this equation does not assume or
claim that the remaining loop has already completed. -/
theorem actual_entry (payload : List UInt8) (small : payload.length < 65536) :
    Fresh (heap payload) ∧ LibraryGlobals (heap payload) ∧
    ZlibF.PlatformMemory.ByteObjectsFit (heap payload) ∧
    C.run (Zlib.Uncompr.uncompress2_z (.ref (.blk 3) 0) (.ref (.blk 2) 0)
      (.ref (.blk 0) 0) (.ref (.blk 1) 0)) (heap payload) =
      (do
        let last ← cdoWhile (loopBody (some (.tab (heap payload).nextBlk))) loopCondition
          {err := Z_OK,len := UInt64.ofNat (StoredWire.wire payload).length,left := UInt64.ofNat payload.length}
        finish (some (.tab (heap payload).nextBlk)) (.ref (.blk ((heap payload).nextBlk + 1)) 0) (.ref (.blk 2) 0) (.ref (.blk 1) 0) last)
        (coreHeap (heap payload) (.ref (.blk 0) 0) (.ref (.blk 3) 0) (UInt64.ofNat payload.length)) := by
  refine ⟨entry_fresh payload,entry_globals payload,entry_platform payload small,?_⟩
  have equation := FreshCoreEntry.uncompress2_z_to_core (heap payload) (.ref (.blk 0) 0) (.ref (.blk 3) 0)
    (.ref (.blk 1) 0) (.ref (.blk 2) 0)
    (UInt64.ofNat (StoredWire.wire payload).length) (UInt64.ofNat payload.length) (entry_fresh payload) rfl
    (entry_input_cell payload) (entry_output_cell payload) (by intro impossible;cases impossible)
    (by intro impossible;cases impossible)
  exact equation

#print axioms entry_domain
#print axioms first_chunk_fits
#print axioms actual_entry
#print axioms entry_bytes
#print axioms entry_writable
end Zlib.Uncompr.Proof.StoredEntry
