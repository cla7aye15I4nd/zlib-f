import ZlibF.Proof.«uncompr.c.stored-entry»
import ZlibF.Proof.«uncompr.c.stored-caller-loop»
import ZlibF.Proof.«uncompr.c.local-wrapper-frame»

namespace Zlib.Uncompr.Proof.StoredGenericCompletion
open C Zlib.Gzguts Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Finish
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The payload and initial output values, all garbage values, allocation
history and old typed tables are arbitrary. The explicit layout fixes source,
length cells and destination to roots 0/1/2/3 and the first free root to 4.
This is a caller subdomain, not the unrestricted utility contract. -/
theorem core_loop_end (h : Heap) (payload : List UInt8) (output : Array UInt8)
    (small : payload.length<65536) (nonempty : payload≠[])
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (noFailure : NoAllocationFailure h)
    (next : h.nextBlk=4) (sourceGet : h.bytes 0=some (StoredWire.wire payload).toArray)
    (outputGet : h.bytes 3=some output) (outputSize : output.size=payload.length) (outputRo : h.ro 3=false) :
    ∃after,C.run (cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
      {err:=Z_OK,len:=UInt64.ofNat (StoredWire.wire payload).length,left:=UInt64.ofNat payload.length})
      (coreHeap h (.ref (.blk 0) 0) (.ref (.blk 3) 0) (UInt64.ofNat payload.length))=
      .ok ({err:=Z_STREAM_END,len:=0,left:=0},after) ∧ after.bytes 3=some payload.toArray := by
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
  apply StoredCallerLoop.loop_end initial allocator payload small nonempty
    (by rfl) copiedSource inputRange outputRange rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [coreStream,outputStream,normalizedDest,dest])
    _ copiedOutput outputSize (copiedRo.trans outputRo)
    (by simp [coreStream,outputStream,normalizedDest,source,dest,initializedStream,resetKeepStream,initStream2,initStream,Wrapper.preparedStream,Separate])

/-- Actual whole utility completion on the explicit four-object layout.
Every heap field not constrained by these premises is universally quantified,
including garbage and the allocation event index. No global Uniq is assumed.
This nonempty single-stored-block family does not replace the full goal. -/
theorem uncompress2_z_stored (h : Heap) (payload : List UInt8) (output : Array UInt8)
    (small : payload.length<65536) (nonempty : payload≠[])
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (noFailure : NoAllocationFailure h)
    (next : h.nextBlk=4) (sourceGet : h.bytes 0=some (StoredWire.wire payload).toArray)
    (outputGet : h.bytes 3=some output) (outputSize : output.size=payload.length) (outputRo : h.ro 3=false)
    (inputCell : LengthCell h (.ref (.blk 1) 0) (UInt64.ofNat (StoredWire.wire payload).length))
    (outputCell : LengthCell h (.ref (.blk 2) 0) (UInt64.ofNat payload.length)) :
    ∃after,C.run (Zlib.Uncompr.uncompress2_z (.ref (.blk 3) 0) (.ref (.blk 2) 0)
      (.ref (.blk 0) 0) (.ref (.blk 1) 0)) h=.ok (Z_OK,after) ∧
      after.bytes 3=some payload.toArray ∧ Zlib.Decodes [] (StoredWire.wire payload) payload := by
  let source : BPtr := .ref (.blk 0) 0
  let dest : BPtr := .ref (.blk 3) 0
  let sourceLen : BPtr := .ref (.blk 1) 0
  let destLen : BPtr := .ref (.blk 2) 0
  let n := UInt64.ofNat (StoredWire.wire payload).length
  let capacity := UInt64.ofNat payload.length
  have nValue : n.toNat=(StoredWire.wire payload).length := UInt64.toNat_ofNat_of_lt'
    (by change (StoredWire.wire payload).length<18446744073709551616;rw [StoredEntry.wire_length];omega)
  have capValue : capacity.toNat=payload.length := UInt64.toNat_ofNat_of_lt'
    (by change payload.length<18446744073709551616;omega)
  have readable : Bytes h source n.toNat (StoredWire.wire payload) := by
    rw [nValue]
    exact Or.inr ⟨.blk 0,0,_,rfl,sourceGet,by simp,by simp⟩
  have writable : Writable h dest capacity.toNat := by
    rw [capValue]
    exact Or.inr ⟨.blk 3,0,output,rfl,outputGet,outputRo,by simp [outputSize]⟩
  have separate : Separate source n.toNat dest capacity.toNat := by simp [source,dest,Separate]
  have sourceSeparate : Separate sourceLen 8 dest capacity.toNat := by simp [sourceLen,dest,Separate]
  have destSeparate : Separate destLen 8 dest capacity.toNat := by simp [destLen,dest,Separate]
  have cellSeparate : Separate sourceLen 8 destLen 8 := by simp [sourceLen,destLen,Separate]
  have validIn : source=.null→n=0 := by simp [source]
  have validOut : dest=.null→capacity=0 := by simp [dest]
  obtain ⟨payloadAfter,actualLoop,payloadGet⟩ := core_loop_end h payload output small nonempty fresh globals platform noFailure next sourceGet outputGet outputSize outputRo
  obtain ⟨last,coreAfter,stream,state,used,made,coreRun,current,allocator,ranges,nonnull,stopped,code,
      countIn,countOut,ledger,owners⟩ :=
    LocalWrapperRanges.initialized_core_safe h source dest n capacity (StoredWire.wire payload)
      fresh globals platform (noFailure h.nalloc) readable writable separate validIn validOut
  have same := Prod.mk.inj (Except.ok.inj (coreRun.symm.trans actualLoop))
  obtain ⟨lastEq,heapEq⟩ := same
  subst last
  subst payloadAfter
  obtain ⟨inputRange,inputCell1,outputRange,outputCell1⟩ :=
    LocalObjects.initialized_loop_cells h coreAfter source dest sourceLen destLen n capacity (StoredWire.wire payload)
      {err:=Z_STREAM_END,len:=0,left:=0} stream state fresh globals platform (noFailure h.nalloc) inputCell outputCell
      readable writable separate sourceSeparate destSeparate validOut coreRun current
  obtain ⟨reservedRange,reservedBytes⟩ :=
    LocalObjects.initialized_loop_reserved h coreAfter source dest n capacity (StoredWire.wire payload)
      {err:=Z_STREAM_END,len:=0,left:=0} stream state fresh globals platform (noFailure h.nalloc) readable writable separate validOut coreRun current
  have reservedSource := WrapperRanges.reserved_separate_old h fresh sourceLen 8 (lengthBytes n) inputCell.1
  have reservedDest := WrapperRanges.reserved_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨first,written,clean,finishRun,storeIn,storeOut,writtenJ,cellIn,cellOut,storeLive,endLive,
      unique,cleanFresh,streamGet,reservedGet,tailFrame⟩ :=
    LocalTailFrame.finish_framed coreAfter h.nextBlk h.nextBlk (h.nextBlk+2) (h.nextBlk+1) stream state
      sourceLen destLen n capacity {err:=Z_STREAM_END,len:=0,left:=0} (junkBytes h).toList current allocator
      inputCell1 outputCell1 inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
  have fullRun : C.run (Zlib.Uncompr.uncompress2_z dest destLen source sourceLen) h=
      .ok (Z_OK,releasedHeap clean h.nextBlk (h.nextBlk+1)) := by
    rw [FreshCoreEntry.uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh (noFailure h.nalloc)
      inputCell outputCell validIn validOut]
    simp only [C.run] at coreRun finishRun
    simpa only [bind_app,coreRun,resultCode,beq_self_eq_true,ite_true] using finishRun
  have live : coreAfter.live 3 := Or.inl (by rw [payloadGet];simp)
  have outside : ¬ (ByteRoot sourceLen 3 ∨ ByteRoot destLen 3 ∨
      (StreamRoot (.tab h.nextBlk) 3 ∨ InflateOwned (h.nextBlk+2) state 3) ∨ 3=h.nextBlk ∨ 3=h.nextBlk+1) := by
    rintro (src|dst|(root|owner)|atStream|atReserved)
    · change (3:Nat)=1 at src;omega
    · change (3:Nat)=2 at dst;omega
    · change (3:Nat)=h.nextBlk at root;rw [next] at root;omega
    · rcases owner with stateRoot|windowRoot
      · rw [next] at stateRoot;change (3:Nat)=6 at stateRoot;omega
      · have age := current.roots.window 3 windowRoot
        rw [next] at age
        omega
    · rw [next] at atStream;omega
    · rw [next] at atReserved;omega
  have bytes := (tailFrame.2.2.2.2.2 3 live outside).1
  exact ⟨_,fullRun,bytes.trans payloadGet,StoredWire.decodes payload small⟩

#print axioms core_loop_end
#print axioms uncompress2_z_stored
end Zlib.Uncompr.Proof.StoredGenericCompletion
