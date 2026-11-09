import ZlibF.Proof.«uncompr.c.stored-entry»
import ZlibF.Proof.«uncompr.c.stored-caller-loop»
import ZlibF.Proof.«uncompr.c.local-wrapper-frame»

namespace Zlib.Uncompr.Proof.StoredValidCompletion
open C Zlib.Gzguts Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Cells Zlib.Uncompr.Proof.Finish
set_option autoImplicit false
set_option maxRecDepth 100000

theorem core_loop_end (payload : List UInt8) (small : payload.length<65536) (nonempty : payload≠[]) :
    ∃after,C.run (cdoWhile (loopBody (some (.tab (StoredEntry.heap payload).nextBlk))) loopCondition
      {err:=Z_OK,len:=UInt64.ofNat (StoredWire.wire payload).length,left:=UInt64.ofNat payload.length})
      (coreHeap (StoredEntry.heap payload) (.ref (.blk 0) 0) (.ref (.blk 3) 0) (UInt64.ofNat payload.length))=
      .ok ({err:=Z_STREAM_END,len:=0,left:=0},after) ∧ after.bytes 3=some payload.toArray := by
  let h := StoredEntry.heap payload
  let source : BPtr := .ref (.blk 0) 0
  let dest : BPtr := .ref (.blk 3) 0
  let capacity := UInt64.ofNat payload.length
  let n := UInt64.ofNat (StoredWire.wire payload).length
  have fresh := StoredEntry.entry_fresh payload
  have globals := StoredEntry.entry_globals payload
  have platform := StoredEntry.entry_platform payload small
  have inputBytes := StoredEntry.entry_bytes payload small
  have writable := StoredEntry.entry_writable payload small
  have initial := LocalDefaultEntry.core_state h source dest capacity fresh rfl globals platform
  have allocator := (LocalInitialization.core_local h source dest capacity fresh rfl).2
  have ranges := LocalWrapperRanges.core_remaining_buffers h fresh source dest n capacity (StoredWire.wire payload)
    initial.good inputBytes writable (by simp [source,dest,Separate]) (by simp [dest])
  have nValue : n.toNat=(StoredWire.wire payload).length := UInt64.toNat_ofNat_of_lt'
    (by change (StoredWire.wire payload).length<18446744073709551616;rw [StoredEntry.wire_length];omega)
  have capValue : capacity.toNat=payload.length := UInt64.toNat_ofNat_of_lt'
    (by change payload.length<18446744073709551616;omega)
  have inputRange : CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk)
      (coreStream h source dest capacity).next_in (StoredWire.wire payload).length false := by
    simpa only [PostRanges.RemainingBuffers,coreStream,outputStream,initializedStream,resetKeepStream,
      initStream2,initStream,Wrapper.preparedStream,UInt32.toNat_zero,Nat.add_zero,nValue] using ranges.1
  have outputRange : CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk)
      (coreStream h source dest capacity).next_out payload.length true := by
    simpa only [coreStream,outputStream,UInt32.toNat_zero,Nat.add_zero,capValue] using ranges.2.1
  have sourceGet : h.bytes 0=some (StoredWire.wire payload).toArray := by simp [h,StoredEntry.heap]
  have outputGet : h.bytes 3=some (Array.replicate payload.length (0:UInt8)) := by simp [h,StoredEntry.heap]
  have copiedSource := WrapperRanges.core_get h fresh source dest capacity (BRef.blk 0) _ sourceGet
  have copiedOutput := WrapperRanges.core_get h fresh source dest capacity (BRef.blk 3) _ outputGet
  have copiedRo := WrapperRanges.core_ro h fresh source dest capacity (BRef.blk 3) _ outputGet
  apply StoredCallerLoop.loop_end initial allocator payload small nonempty
    (by rfl) copiedSource inputRange outputRange rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by simp [coreStream,outputStream,normalizedDest,dest])
    _ copiedOutput (by simp) (copiedRo.trans (by rfl))
    (by simp [coreStream,outputStream,normalizedDest,source,dest,initializedStream,resetKeepStream,initStream2,initStream,Wrapper.preparedStream,Separate])

/-- A real public-domain caller with canonical library globals completes
actual uncompress2_z for every nonempty single stored payload below 65536.
The proof includes real initialization, one actual utility loop iteration,
ordered length writes, inflateEnd and both automatic frees. Independent
RFC validity is the separate stored grammar theorem, not END implies RFC.
This symbolic family does not claim completion for arbitrary zlib streams. -/
theorem uncompress2_z_stored (payload : List UInt8) (small : payload.length<65536) (nonempty : payload≠[]) :
    LibraryGlobals (StoredEntry.heap payload) ∧
    ∃after,C.run (Zlib.Uncompr.uncompress2_z (.ref (.blk 3) 0) (.ref (.blk 2) 0)
      (.ref (.blk 0) 0) (.ref (.blk 1) 0)) (StoredEntry.heap payload)=.ok (Z_OK,after) ∧
      after.bytes 3=some payload.toArray ∧ Zlib.Decodes [] (StoredWire.wire payload) payload := by
  let h := StoredEntry.heap payload
  let source : BPtr := .ref (.blk 0) 0
  let dest : BPtr := .ref (.blk 3) 0
  let sourceLen : BPtr := .ref (.blk 1) 0
  let destLen : BPtr := .ref (.blk 2) 0
  let n := UInt64.ofNat (StoredWire.wire payload).length
  let capacity := UInt64.ofNat payload.length
  have fresh := StoredEntry.entry_fresh payload
  have globals := StoredEntry.entry_globals payload
  have platform := StoredEntry.entry_platform payload small
  have inputCell := StoredEntry.entry_input_cell payload
  have outputCell := StoredEntry.entry_output_cell payload
  have readable := StoredEntry.entry_bytes payload small
  have writable := StoredEntry.entry_writable payload small
  have separate : Separate source n.toNat dest capacity.toNat := by simp [source,dest,Separate]
  have sourceSeparate : Separate sourceLen 8 dest capacity.toNat := by simp [sourceLen,dest,Separate]
  have destSeparate : Separate destLen 8 dest capacity.toNat := by simp [destLen,dest,Separate]
  have cellSeparate : Separate sourceLen 8 destLen 8 := by simp [sourceLen,destLen,Separate]
  have validIn : source=.null→n=0 := by simp [source]
  have validOut : dest=.null→capacity=0 := by simp [dest]
  obtain ⟨payloadAfter,actualLoop,payloadGet⟩ := core_loop_end payload small nonempty
  obtain ⟨last,coreAfter,stream,state,used,made,coreRun,current,allocator,ranges,nonnull,stopped,code,
      countIn,countOut,ledger,owners⟩ :=
    LocalWrapperRanges.initialized_core_safe h source dest n capacity (StoredWire.wire payload)
      fresh globals platform rfl readable writable separate validIn validOut
  have same := Prod.mk.inj (Except.ok.inj (coreRun.symm.trans actualLoop))
  obtain ⟨lastEq,heapEq⟩ := same
  subst last
  subst payloadAfter
  obtain ⟨inputRange,inputCell1,outputRange,outputCell1⟩ :=
    LocalObjects.initialized_loop_cells h coreAfter source dest sourceLen destLen n capacity (StoredWire.wire payload)
      {err:=Z_STREAM_END,len:=0,left:=0} stream state fresh globals platform rfl inputCell outputCell
      readable writable separate sourceSeparate destSeparate validOut coreRun current
  obtain ⟨reservedRange,reservedBytes⟩ :=
    LocalObjects.initialized_loop_reserved h coreAfter source dest n capacity (StoredWire.wire payload)
      {err:=Z_STREAM_END,len:=0,left:=0} stream state fresh globals platform rfl readable writable separate validOut coreRun current
  have reservedSource := WrapperRanges.reserved_separate_old h fresh sourceLen 8 (lengthBytes n) inputCell.1
  have reservedDest := WrapperRanges.reserved_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1
  obtain ⟨first,written,clean,finishRun,storeIn,storeOut,writtenJ,cellIn,cellOut,storeLive,endLive,
      unique,cleanFresh,streamGet,reservedGet,tailFrame⟩ :=
    LocalTailFrame.finish_framed coreAfter h.nextBlk h.nextBlk (h.nextBlk+2) (h.nextBlk+1) stream state
      sourceLen destLen n capacity {err:=Z_STREAM_END,len:=0,left:=0} (junkBytes h).toList current allocator
      inputCell1 outputCell1 inputRange outputRange cellSeparate reservedBytes reservedRange reservedSource reservedDest
  have fullRun : C.run (Zlib.Uncompr.uncompress2_z dest destLen source sourceLen) h=
      .ok (Z_OK,releasedHeap clean h.nextBlk (h.nextBlk+1)) := by
    rw [FreshCoreEntry.uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh rfl
      inputCell outputCell validIn validOut]
    simp only [C.run] at coreRun finishRun
    simpa only [bind_app,coreRun,resultCode,beq_self_eq_true,ite_true] using finishRun
  have live : coreAfter.live 3 := Or.inl (by rw [payloadGet];simp)
  have outside : ¬ (ByteRoot sourceLen 3 ∨ ByteRoot destLen 3 ∨
      (StreamRoot (.tab h.nextBlk) 3 ∨ InflateOwned (h.nextBlk+2) state 3) ∨ 3=h.nextBlk ∨ 3=h.nextBlk+1) := by
    rintro (src|dst|(root|owner)|atStream|atReserved)
    · change (3:Nat)=1 at src;omega
    · change (3:Nat)=2 at dst;omega
    · change (3:Nat)=4 at root;omega
    · rcases owner with stateRoot|windowRoot
      · change (3:Nat)=6 at stateRoot;omega
      · have age := current.roots.window 3 windowRoot
        change 4≤3 at age
        omega
    · change (3:Nat)=4 at atStream;omega
    · change (3:Nat)=5 at atReserved;omega
  have bytes := (tailFrame.2.2.2.2.2 3 live outside).1
  exact ⟨globals,_,fullRun,bytes.trans payloadGet,StoredWire.decodes payload small⟩

#print axioms core_loop_end
#print axioms uncompress2_z_stored
end Zlib.Uncompr.Proof.StoredValidCompletion
