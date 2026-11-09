import ZlibF.Proof.«compress.c.local-data-history»

/-! # Typed caller storage and resource counts of the actual header history -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalHistoryLedger
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocal ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.CompressLocalHeader ZlibF.Spec.Public.Proofs.CompressLocalData
open ZlibF.Spec.Public.Proofs.CompressLocalSymbols ZlibF.Spec.Public.Proofs.CompressLocalPendingData
open ZlibF.Spec.Public.Proofs.CompressLocalDataHistory
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Restoring the caller output bytes after the two real header copies
keeps every old typed slot, including other tables at that output owner.
This follows from the actual typed stores, not global owner uniqueness. -/
theorem second_header_old_slots {initialized : Heap} {cutoff ob oo x : Nat} {z : ZStream}
    {d : DeflateState} {buf output original : Array UInt8} {zi : ZStream}
    (getStream : initialized.streams cutoff = some zi) (getOriginal : initialized.bytes ob = some original) (old : x < cutoff) :
    SlotSame initialized
      (Zlib.Trees.Proofs.Out.setB
        (secondHeaderHeap ((ZStreamRef.tab cutoff).put initialized z) (.tab cutoff) (cutoff+1) (cutoff+5)
          ob oo z d buf output Z_NO_FLUSH) ob original) x := by
  have notRoot : x ≠ cutoff := by omega
  have notState : x ≠ cutoff+1 := by omega
  have notPending : x ≠ cutoff+5 := by omega
  by_cases same : x = ob
  · subst x
    simp [SlotSame,secondHeaderHeap,pendingDataHeap,pendingCopyHeap,oneHeaderHeap,
      Zlib.Trees.Proofs.Out.setB,ZStreamRef.put,setD,getStream,getOriginal,
      upd_ne _ _ _ _ notRoot,upd_ne _ _ _ _ notState,upd_ne _ _ _ _ notPending]
  · simp [SlotSame,secondHeaderHeap,pendingDataHeap,pendingCopyHeap,oneHeaderHeap,
      Zlib.Trees.Proofs.Out.setB,ZStreamRef.put,setD,getStream,
      upd_ne _ _ _ _ notRoot,upd_ne _ _ _ _ notState,upd_ne _ _ _ _ notPending,upd_ne _ _ _ _ same]

/-- Exact allocator and object-id counts from that actual successful
initializer. The automatic stream is a local object, not a malloc call. -/
theorem initialization_resource_counts {h after : Heap}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (actualInit : C.run (deflateInit_ (some (.tab h.nextBlk)) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112)
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after)) :
    after.nextBlk = h.nextBlk+6 ∧ after.nalloc = h.nalloc+5 := by
  let root := ZStreamRef.tab h.nextBlk
  let automatic := ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h
  let old := ZlibF.Spec.Public.Proofs.CompressCaller.localStream h
  let z := ZlibF.Spec.Public.preparedStream old
  let prepared := root.put automatic z
  have get : root.get automatic = some old := by
    simp [root,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap,ZStreamRef.get,old]
  obtain ⟨freshA,uniqueA⟩ := automatic_stream_local fresh
  have controls := shape_put get z
  have freshP : Fresh prepared := controls.fresh (by simp) freshA
  have uniqueP : UniqueFrom prepared h.nextBlk := uniqueA.shape controls
  have getP : root.get prepared = some z := ZStreamRef.get_put_same get _
  have allocator : DefAlloc z := by
    simp [DefAlloc,z,ZlibF.Spec.Public.preparedStream,old,ZlibF.Spec.Public.Proofs.CompressCaller.localStream]
  have static : Zlib.Trees.Proofs.Out.TreesStatic prepared.static := by
    simpa [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap] using
      ZlibF.Spec.Public.Proofs.DeflateInit.globals_trees globals
  have requests : ∀ j, j < 5 → prepared.allocOk (prepared.nalloc+j) = true := by
    intro j bound
    simpa [prepared,automatic,ZlibF.Spec.Public.Proofs.CompressCaller.localHeap] using allocations j bound
  obtain ⟨a1,a2,a3,qa,run,start⟩ := allocate_local_start freshP uniqueP getP allocator static requests
  let after := successHeap prepared root z 6 a1 a2 a3 qa
  have version : VersionValue automatic (.ref (.str 57) 0) (some 49) :=
    Or.inr ⟨49,rfl,Or.inr ⟨.str 57,0,strBytes ZLIB_VERSION,rfl,rfl,by decide +kernel,by decide +kernel⟩⟩
  have init := entry_run get version Z_DEFAULT_COMPRESSION
  have normalize : levelValue Z_DEFAULT_COMPRESSION = 6 := by decide +kernel
  rw [normalize,show ((6 : Int32) < 0 || (6 : Int32) > 9) = false from by decide +kernel] at init
  change deflateInit_ (some root) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112 automatic = allocate (some root) 6 prepared at init
  have computed : C.run (deflateInit_ (some root) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112) automatic =
      .ok (Z_OK,successHeap prepared root z 6 a1 a2 a3 qa) := init.trans run
  have heaps := (Prod.mk.inj (Except.ok.inj (computed.symm.trans actualInit))).2
  rw [←heaps]
  simp [Zlib.Deflate.Proofs.DefaultInit.successHeap,Zlib.Deflate.Proofs.DefaultInit.readyHeap,
    Zlib.Deflate.Proofs.DefaultInit.successfulBuffers,Zlib.Deflate.Proofs.DefaultInit.publishedHeap,
    Zlib.Deflate.Proofs.DefaultInit.stateHeap,prepared,automatic,
    ZlibF.Spec.Public.Proofs.CompressCaller.localHeap,Nat.add_assoc,setD,setW]


theorem local_owned_live {h : Heap} {r : ZStreamRef} {cutoff ds : Nat} {z : ZStream} {d : DeflateState}
    (state : LocalState h cutoff r ds z d) {x : Nat} (owned : DOwned d ds x) : h.live x := by
  obtain ⟨w,p,q,b,blocks⟩ := state.inv.blocks
  rcases owned with rfl | ⟨w',win,rfl⟩ | ⟨p',prev,rfl⟩ | ⟨q',head,rfl⟩ | ⟨b',pending,rfl⟩
  · simp [Heap.live,state.live.hs]
  · rw [blocks.win] at win;cases win
    obtain ⟨a,get,_⟩ := blocks.wa
    simp [Heap.live,get]
  · rw [blocks.prev] at prev;cases prev
    obtain ⟨a,get,_⟩ := blocks.pa
    simp [Heap.live,get]
  · rw [blocks.head] at head;cases head
    obtain ⟨a,get,_⟩ := blocks.qa
    simp [Heap.live,get]
  · rw [blocks.pbuf] at pending;cases pending
    obtain ⟨a,get,_⟩ := blocks.ba
    simp [Heap.live,get]

/-- The six concrete objects created by this real initialization remain
live while its initialized local state and buffer addresses are retained. -/
theorem initial_private_live {h : Heap} {cutoff : Nat} {z : ZStream} {d : DeflateState}
    (state : LocalState h cutoff (.tab cutoff) (cutoff+1) z d)
    (controls : InitialDataControls cutoff d) {x : Nat} (inside : cutoff ≤ x ∧ x < cutoff+6) : h.live x := by
  have cases : x = cutoff ∨ x = cutoff+1 ∨ x = cutoff+2 ∨ x = cutoff+3 ∨ x = cutoff+4 ∨ x = cutoff+5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl (by intro missing;have impossible := state.live.hz.symm.trans missing;cases impossible)))
  · exact local_owned_live state (Or.inl rfl)
  · exact local_owned_live state (Or.inr (Or.inl ⟨cutoff+2,controls.2.2.2.2.2.1,rfl⟩))
  · exact local_owned_live state (Or.inr (Or.inr (Or.inl ⟨cutoff+3,controls.2.2.2.2.2.2.1,rfl⟩)))
  · exact local_owned_live state (Or.inr (Or.inr (Or.inr (Or.inl ⟨cutoff+4,controls.2.2.2.2.2.2.2.1,rfl⟩))))
  · exact local_owned_live state (Or.inr (Or.inr (Or.inr (Or.inr ⟨cutoff+5,controls.2.2.2.2.2.2.2.2,rfl⟩))))


/-- The exact same real header history retains all original typed caller
slots after restoring its two output bytes, and has exactly six live
private objects from five malloc calls plus the local stream object. -/
theorem fresh_split_header_resource {h : Heap} {ob oo : Nat} {source : BPtr} {n : UInt32}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (writable : Writable h (.ref (.blk ob) oo) 2) (valid : n ≠ 0 → source ≠ .null) :
    ∃ after z d original,
      splitHeaderPrefix (.tab h.nextBlk) (.ref (.blk ob) oo) source n
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after) ∧
      LocalState after h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) z d ∧
      InitialDataControls h.nextBlk d ∧ h.bytes ob = some original ∧
      Frame h (Zlib.Trees.Proofs.Out.setB after ob original) (fun _ => False) ∧
      after.nextBlk = h.nextBlk+6 ∧ after.nalloc = h.nalloc+5 ∧
      LiveChange h after (fun x => h.nextBlk ≤ x ∧ x < h.nextBlk+6) (fun _ => False) := by
  obtain ⟨initialized,zi,di,ready,buf,output,init,start,bindings,first,refill,second,state,
      _account,_chains,_fields,controls,_symbols,_pending,_busy,_last,_source,_input,_out,_outZero⟩ :=
    fresh_two_header_data_prefix fresh globals allocations writable valid
  let bound := {zi with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := n}
  let after := secondHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5) ob oo bound di buf output Z_NO_FLUSH
  have prefixRun : splitHeaderPrefix (.tab h.nextBlk) (.ref (.blk ob) oo) source n
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after) := by
    simp only [C.run] at init bindings refill
    unfold splitHeaderPrefix
    simp only [bind_app,init,bindings,first,refill,second]
    rfl
  obtain ⟨canonical,_z0,_d0,canonicalRun,_local,frameI,liveI⟩ := fresh_utility_initialization fresh globals allocations
  have sameInit : canonical = initialized := (Prod.mk.inj (Except.ok.inj (canonicalRun.symm.trans init))).2
  subst canonical
  have countsI := initialization_resource_counts fresh globals allocations init
  have actualBinding : C.run (zwr (some (.tab h.nextBlk)) (fun s =>
      {s with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := source,avail_in := n})) initialized =
      .ok ((),(ZStreamRef.tab h.nextBlk).put initialized bound) := by
    simp only [C.run,zwr_eq,start.representation.live.hz,bound]
  have readyEq := (Prod.mk.inj (Except.ok.inj (bindings.symm.trans actualBinding))).2
  rcases writable with bad | ⟨ref,off,original,pointer,get,_rw,_room⟩
  · cases bad.1
  obtain ⟨sameRef,sameOff⟩ := Ptr.ref.inj pointer
  subst ref off
  have getH : h.bytes ob = some original := get
  have oldOutput : h.live ob := by simp [Heap.live,getH]
  have originalI : initialized.bytes ob = some original := (frameI.2.2.2.2.2 ob oldOutput (by simp)).1.trans getH
  have counts : after.nextBlk = h.nextBlk+6 ∧ after.nalloc = h.nalloc+5 := by
    simpa [after,secondHeaderHeap,pendingDataHeap,pendingCopyHeap,oneHeaderHeap,readyEq] using countsI
  have frame : Frame h (Zlib.Trees.Proofs.Out.setB after ob original) (fun _ => False) := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · simpa [after,secondHeaderHeap,pendingDataHeap,pendingCopyHeap,oneHeaderHeap,readyEq,Zlib.Trees.Proofs.Out.setB] using frameI.1
    · simpa [after,secondHeaderHeap,pendingDataHeap,pendingCopyHeap,oneHeaderHeap,readyEq,Zlib.Trees.Proofs.Out.setB] using frameI.2.1
    · simpa [after,secondHeaderHeap,pendingDataHeap,pendingCopyHeap,oneHeaderHeap,readyEq,Zlib.Trees.Proofs.Out.setB] using frameI.2.2.1
    · change h.nextBlk ≤ after.nextBlk
      rw [counts.1]; omega
    · change h.nalloc ≤ after.nalloc
      rw [counts.2]; omega
    · intro x oldLive _outside
      have row := second_header_old_slots (d := di) (buf := buf) (output := output) (oo := oo)
        (z := bound) start.representation.live.hz originalI (fresh.lt oldLive)
      have firstRow : SlotSame h initialized x := frameI.2.2.2.2.2 x oldLive (by simp)
      apply firstRow.trans
      simpa only [after,readyEq] using row
  have outBytes : after.bytes ob = some
      (copyRange (copyRange output (zlibHeaderBytes buf) oo 0 1) (zlibHeaderBytes buf) (oo+1) 1 1) := by
    simp [after,secondHeaderHeap,pendingDataHeap,pendingCopyHeap]
  have restoration := shape_setB outBytes original
  have ledger : ∀ x, after.live x ↔ h.live x ∨ h.nextBlk ≤ x ∧ x < h.nextBlk+6 := by
    intro x
    by_cases old : x < h.nextBlk
    · have row := second_header_old_slots (d := di) (buf := buf) (output := output) (oo := oo)
        (z := bound) start.representation.live.hz originalI old
      have rowLive : (Zlib.Trees.Proofs.Out.setB after ob original).live x ↔ initialized.live x := by
        simpa only [after,readyEq] using row.live
      exact (restoration.live x).symm.trans (rowLive.trans (liveI x))
    · by_cases remaining : x < h.nextBlk+6
      · have inside : h.nextBlk ≤ x ∧ x < h.nextBlk+6 := by omega
        have alive : after.live x := initial_private_live state controls inside
        exact ⟨fun _ => Or.inr inside,fun _ => alive⟩
      · have noAfter : ¬after.live x := by
          intro live
          exact state.fresh x (by rw [counts.1];omega) live
        have noOriginal : ¬h.live x := by intro live;have below := fresh.lt live;omega
        have notInside : ¬(h.nextBlk ≤ x ∧ x < h.nextBlk+6) := by omega
        simp [noAfter,noOriginal,notInside]
  refine ⟨after,_,_,original,prefixRun,state,controls,getH,frame,counts.1,counts.2,?_⟩
  intro x
  simpa [LiveChange] using ledger x


end ZlibF.Spec.Public.Proofs.CompressLocalHistoryLedger
