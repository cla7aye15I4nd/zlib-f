import ZlibF.Proof.«uncompr.c.stored-returned-core»
import ZlibF.Proof.«uncompr.c.local-release»

namespace Zlib.Uncompr.Proof.StoredExactCompletion
open C Zlib.Gzguts Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Finish
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Actual whole utility completion on the explicit four-object layout.
Every heap field not constrained by these premises is universally quantified,
including garbage and the allocation event index. No global Uniq is assumed.
This single-stored-block family does not replace the full goal. -/
theorem uncompress2_z_stored_exact (h : Heap) (payload : List UInt8) (output : Array UInt8)
    (small : payload.length<65536)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (noFailure : NoAllocationFailure h)
    (next : h.nextBlk=4) (sourceGet : h.bytes 0=some (StoredWire.wire payload).toArray)
    (outputGet : h.bytes 3=some output) (outputSize : output.size=payload.length) (outputRo : h.ro 3=false)
    (inputCell : LengthCell h (.ref (.blk 1) 0) (UInt64.ofNat (StoredWire.wire payload).length))
    (outputCell : LengthCell h (.ref (.blk 2) 0) (UInt64.ofNat payload.length)) :
    ∃after,C.run (Zlib.Uncompr.uncompress2_z (.ref (.blk 3) 0) (.ref (.blk 2) 0)
      (.ref (.blk 0) 0) (.ref (.blk 1) 0)) h=.ok (Z_OK,after) ∧
      after.bytes 3=some payload.toArray ∧
      LengthCell after (.ref (.blk 1) 0) (UInt64.ofNat (StoredWire.wire payload).length) ∧
      LengthCell after (.ref (.blk 2) 0) (UInt64.ofNat payload.length) ∧
      load64 (.ref (.blk 1) 0) after=.ok (UInt64.ofNat (StoredWire.wire payload).length,after) ∧
      load64 (.ref (.blk 2) 0) after=.ok (UInt64.ofNat payload.length,after) ∧
      Zlib.Decodes [] (StoredWire.wire payload) payload := by
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
  obtain ⟨payloadAfter,returned,actualLoop,payloadGet,returnedGet,inZero,outZero⟩ := StoredReturnedCore.core_loop_fields h payload output small fresh globals platform noFailure next sourceGet outputGet outputSize outputRo
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
  have streamEq : stream=returned := Option.some.inj (current.good.live.hz.symm.trans returnedGet)
  have streamIn : stream.avail_in=0 := by rw [streamEq];exact inZero
  have streamOut : stream.avail_out=0 := by rw [streamEq];exact outZero
  obtain ⟨first,written,clean,finishRun,storeIn,storeOut,cellIn,cellOut,tailLive⟩ :=
    LocalRelease.finish_full coreAfter h.nextBlk (h.nextBlk+2) stream state
      sourceLen destLen n capacity {err:=Z_STREAM_END,len:=0,left:=0} (junkBytes h).toList current allocator
      inputCell1 outputCell1 inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
      (LocalRelease.length_cell_old_roots fresh inputCell) (LocalRelease.length_cell_old_roots fresh outputCell)
  have fullRun : C.run (Zlib.Uncompr.uncompress2_z dest destLen source sourceLen) h=
      .ok (Z_OK,releasedHeap clean h.nextBlk (h.nextBlk+1)) := by
    rw [FreshCoreEntry.uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh (noFailure h.nalloc)
      inputCell outputCell validIn validOut]
    simp only [C.run] at coreRun finishRun
    simpa only [bind_app,coreRun,resultCode,beq_self_eq_true,ite_true] using finishRun
  have finalInput : LengthCell (releasedHeap clean h.nextBlk (h.nextBlk+1)) sourceLen n := by
    simpa only [streamIn,show (0:UInt32).toUInt64=0 from rfl,show (0:UInt64)+0=0 from rfl,UInt64.sub_zero] using cellIn
  have finalOutput : LengthCell (releasedHeap clean h.nextBlk (h.nextBlk+1)) destLen capacity := by
    simpa only [streamOut,show (0:UInt32).toUInt64=0 from rfl,show (0:UInt64)+0=0 from rfl,UInt64.sub_zero] using cellOut
  obtain ⟨observedAfter,observedRun,observedBytes,rfc⟩ := StoredAllCompletion.uncompress2_z_stored h payload output
    small fresh globals platform noFailure next sourceGet outputGet outputSize outputRo inputCell outputCell
  have afterEq : observedAfter=releasedHeap clean h.nextBlk (h.nextBlk+1) :=
    congrArg Prod.snd (Except.ok.inj (observedRun.symm.trans fullRun))
  rw [afterEq] at observedBytes
  exact ⟨_,fullRun,observedBytes,finalInput,finalOutput,
    load64_lengthCell _ sourceLen n finalInput,load64_lengthCell _ destLen capacity finalOutput,rfc⟩

#print axioms uncompress2_z_stored_exact
end Zlib.Uncompr.Proof.StoredExactCompletion
