import ZlibF.Proof.«uncompr.c.stored-all-completion»
import ZlibF.Proof.«uncompr.c.stored-returned-caller-loop»

namespace Zlib.Uncompr.Proof.StoredReturnedCore
open C Zlib.Gzguts Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Finish
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The payload and initial output values, all garbage values, allocation
history and old typed tables are arbitrary. The explicit layout fixes source,
length cells and destination to roots 0/1/2/3 and the first free root to 4.
This is a caller subdomain, not the unrestricted utility contract. -/
theorem core_loop_fields (h : Heap) (payload : List UInt8) (output : Array UInt8)
    (small : payload.length<65536)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (noFailure : NoAllocationFailure h)
    (next : h.nextBlk=4) (sourceGet : h.bytes 0=some (StoredWire.wire payload).toArray)
    (outputGet : h.bytes 3=some output) (outputSize : output.size=payload.length) (outputRo : h.ro 3=false) :
    ∃after returned,C.run (cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
      {err:=Z_OK,len:=UInt64.ofNat (StoredWire.wire payload).length,left:=UInt64.ofNat payload.length})
      (coreHeap h (.ref (.blk 0) 0) (.ref (.blk 3) 0) (UInt64.ofNat payload.length))=
      .ok ({err:=Z_STREAM_END,len:=0,left:=0},after) ∧ after.bytes 3=some payload.toArray ∧ after.streams h.nextBlk=some returned ∧ returned.avail_in=0 ∧ returned.avail_out=0 := by
  let source : BPtr := .ref (.blk 0) 0
  let dest : BPtr := .ref (.blk 3) 0
  let capacity := UInt64.ofNat payload.length
  let n := UInt64.ofNat (StoredWire.wire payload).length
  have nValue : n.toNat=(StoredWire.wire payload).length := UInt64.toNat_ofNat_of_lt'
    (by change (StoredWire.wire payload).length<18446744073709551616;rw [StoredEntry.wire_length];omega)
  have capValue : capacity.toNat=payload.length := UInt64.toNat_ofNat_of_lt'
    (by change payload.length<18446744073709551616;omega)
  have inputBytes : Bytes h source n.toNat (StoredWire.wire payload) := by
    rw [nValue]
    exact Or.inr ⟨.blk 0,0,_,rfl,sourceGet,by simp,by simp⟩
  have writable : Writable h dest capacity.toNat := by
    rw [capValue]
    exact Or.inr ⟨.blk 3,0,output,rfl,outputGet,outputRo,by simp [outputSize]⟩
  have initial := LocalDefaultEntry.core_state h source dest capacity fresh (noFailure h.nalloc) globals platform
  have allocator := (LocalInitialization.core_local h source dest capacity fresh (noFailure h.nalloc)).2
  have ranges := LocalWrapperRanges.core_remaining_buffers h fresh source dest n capacity (StoredWire.wire payload)
    initial.good inputBytes writable (by simp [source,dest,Separate]) (by simp [dest])
  have inputRange : CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk)
      (coreStream h source dest capacity).next_in (StoredWire.wire payload).length false := by
    simpa only [PostRanges.RemainingBuffers,coreStream,outputStream,initializedStream,resetKeepStream,
      initStream2,initStream,Wrapper.preparedStream,UInt32.toNat_zero,Nat.add_zero,nValue] using ranges.1
  have outputRange : CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk)
      (coreStream h source dest capacity).next_out payload.length true := by
    simpa only [coreStream,outputStream,UInt32.toNat_zero,Nat.add_zero,capValue] using ranges.2.1
  have copiedSource := WrapperRanges.core_get h fresh source dest capacity (BRef.blk 0) _ sourceGet
  have copiedOutput := WrapperRanges.core_get h fresh source dest capacity (BRef.blk 3) _ outputGet
  have copiedRo := WrapperRanges.core_ro h fresh source dest capacity (BRef.blk 3) _ outputGet
  apply StoredReturnedCallerLoop.loop_end_fields initial allocator payload small
    (by rfl) copiedSource inputRange outputRange rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [coreStream,outputStream,normalizedDest,dest])
    _ copiedOutput outputSize (copiedRo.trans outputRo)
    (by simp [coreStream,outputStream,normalizedDest,source,dest,initializedStream,resetKeepStream,initStream2,initStream,Wrapper.preparedStream,Separate])

#print axioms core_loop_fields
end Zlib.Uncompr.Proof.StoredReturnedCore
