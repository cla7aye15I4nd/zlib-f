import ZlibF.Proof.«uncompr.c.stored-layout-core»
import ZlibF.Proof.«uncompr.c.local-release»

namespace Zlib.Uncompr.Proof.StoredLayoutCompletion
open C Zlib.Gzguts Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Finish
set_option autoImplicit false
set_option maxRecDepth 100000

/-- A scalar length cell separated from an entire output byte object cannot
occupy that output block, even when the output capacity is zero. -/
private theorem scalar_other {h : Heap} {ib db off : Nat} {value : UInt64}
    {output : Array UInt8} {n : Nat}
    (cell : LengthCell h (.ref (.blk ib) off) value) (get : h.bytes db=some output)
    (size : output.size=n) (separate : Separate (.ref (.blk ib) off) 8 (.ref (.blk db) 0) n) : ib≠db := by
  intro same
  subst ib
  rcases cell.2 with null|⟨ref,pos,a,ptr,getA,ro,room⟩
  · cases null.1
  · cases ptr
    have arrays : a=output := Option.some.inj (getA.symm.trans get)
    subst a
    rw [size] at room
    rcases separate with noCell|noOutput|different|before|later
    · omega
    · omega
    · exact different rfl
    · omega
    · omega

/-- Complete actual utility execution for arbitrary root indices and scalar
byte offsets. The original public UtilitySeparation is explicit. All garbage,
old typed tables and allocation history admitted by Fresh remain arbitrary.
Data ranges are still whole source/output arrays at offset zero, with exact
output capacity; other layouts and capacities remain the full goal. -/
theorem uncompress2_z_stored_exact (h : Heap) (sb db ib ob io oo : Nat) (payload : List UInt8) (output : Array UInt8)
    (small : payload.length<65536)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (noFailure : NoAllocationFailure h)
    (sourceGet : h.bytes sb=some (StoredWire.wire payload).toArray)
    (outputGet : h.bytes db=some output) (outputSize : output.size=payload.length) (outputRo : h.ro db=false)
    (inputCell : LengthCell h (.ref (.blk ib) io) (UInt64.ofNat (StoredWire.wire payload).length))
    (outputCell : LengthCell h (.ref (.blk ob) oo) (UInt64.ofNat payload.length))
    (separation : UtilitySeparation (.ref (.blk db) 0) payload.length (.ref (.blk sb) 0)
      (StoredWire.wire payload).length (.ref (.blk ob) oo) (.ref (.blk ib) io)) :
    ∃after,C.run (Zlib.Uncompr.uncompress2_z (.ref (.blk db) 0) (.ref (.blk ob) oo)
      (.ref (.blk sb) 0) (.ref (.blk ib) io)) h=.ok (Z_OK,after) ∧
      after.bytes db=some payload.toArray ∧
      LengthCell after (.ref (.blk ib) io) (UInt64.ofNat (StoredWire.wire payload).length) ∧
      LengthCell after (.ref (.blk ob) oo) (UInt64.ofNat payload.length) ∧
      load64 (.ref (.blk ib) io) after=.ok (UInt64.ofNat (StoredWire.wire payload).length,after) ∧
      load64 (.ref (.blk ob) oo) after=.ok (UInt64.ofNat payload.length,after) ∧
      Zlib.Decodes [] (StoredWire.wire payload) payload := by
  let source : BPtr := .ref (.blk sb) 0
  let dest : BPtr := .ref (.blk db) 0
  let sourceLen : BPtr := .ref (.blk ib) io
  let destLen : BPtr := .ref (.blk ob) oo
  let n := UInt64.ofNat (StoredWire.wire payload).length
  let capacity := UInt64.ofNat payload.length
  have nValue : n.toNat=(StoredWire.wire payload).length := UInt64.toNat_ofNat_of_lt'
    (by change (StoredWire.wire payload).length<18446744073709551616;rw [StoredEntry.wire_length];omega)
  have capValue : capacity.toNat=payload.length := UInt64.toNat_ofNat_of_lt'
    (by change payload.length<18446744073709551616;omega)
  have readable : Bytes h source n.toNat (StoredWire.wire payload) := by
    rw [nValue]
    exact Or.inr ⟨.blk sb,0,_,rfl,sourceGet,by simp,by simp⟩
  have writable : Writable h dest capacity.toNat := by
    rw [capValue]
    exact Or.inr ⟨.blk db,0,output,rfl,outputGet,outputRo,by simp [outputSize]⟩
  have separate : Separate source n.toNat dest capacity.toNat := by
    rw [nValue,capValue]
    exact separate_swap _ _ _ _ separation.1
  have sourceSeparate : Separate sourceLen 8 dest capacity.toNat := by
    rw [capValue]
    exact separation.2.2.2.1
  have destSeparate : Separate destLen 8 dest capacity.toNat := by
    rw [capValue]
    exact separation.2.1
  have cellSeparate : Separate sourceLen 8 destLen 8 :=
    separate_swap _ _ _ _ separation.2.2.2.2.2
  have validIn : source=.null→n=0 := by simp [source]
  have validOut : dest=.null→capacity=0 := by simp [dest]
  obtain ⟨payloadAfter,returned,actualLoop,payloadGet,returnedGet,inZero,outZero⟩ := StoredLayoutCore.core_loop_fields h sb db payload output small fresh globals platform noFailure sourceGet outputGet outputSize outputRo
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
  obtain ⟨f2,w2,c2,framedRun,st1,st2,j2,ci2,co2,sl2,el2,uf2,ff2,sg2,rg2,tailFrame⟩ :=
    LocalTailFrame.finish_framed coreAfter h.nextBlk h.nextBlk (h.nextBlk+2) (h.nextBlk+1) stream state
      sourceLen destLen n capacity {err:=Z_STREAM_END,len:=0,left:=0} (junkBytes h).toList current allocator
      inputCell1 outputCell1 inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
  have frameHeap : releasedHeap c2 h.nextBlk (h.nextBlk+1)=releasedHeap clean h.nextBlk (h.nextBlk+1) :=
    congrArg Prod.snd (Except.ok.inj (framedRun.symm.trans finishRun))
  rw [frameHeap] at tailFrame
  have inputOther : ib≠db := scalar_other inputCell outputGet outputSize separation.2.2.2.1
  have outputOther : ob≠db := scalar_other outputCell outputGet outputSize separation.2.1
  have oldOutput : db<h.nextBlk := fresh.lt (Or.inl (by rw [outputGet];simp))
  have live : coreAfter.live db := Or.inl (by rw [payloadGet];simp)
  have outside : ¬ (ByteRoot sourceLen db ∨ ByteRoot destLen db ∨
      (StreamRoot (.tab h.nextBlk) db ∨ InflateOwned (h.nextBlk+2) state db) ∨ db=h.nextBlk ∨ db=h.nextBlk+1) := by
    rintro (src|dst|(root|owner)|atStream|atReserved)
    · change db=ib at src
      exact inputOther src.symm
    · change db=ob at dst
      exact outputOther dst.symm
    · change db=h.nextBlk at root
      omega
    · rcases owner with stateRoot|windowRoot
      · change db=h.nextBlk+2 at stateRoot
        omega
      · have age := current.roots.window db windowRoot
        omega
    · omega
    · omega
  have outputBytes := (tailFrame.2.2.2.2.2 db live outside).1.trans payloadGet
  exact ⟨_,fullRun,outputBytes,finalInput,finalOutput,
    load64_lengthCell _ sourceLen n finalInput,load64_lengthCell _ destLen capacity finalOutput,
    StoredWire.decodes payload small⟩

#print axioms uncompress2_z_stored_exact
end Zlib.Uncompr.Proof.StoredLayoutCompletion
