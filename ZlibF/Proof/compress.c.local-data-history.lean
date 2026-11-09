import ZlibF.Proof.«compress.c.local-pending-data»
import ZlibF.Proof.«compress.c.local-literal-loop»

/-! # Actual Fresh initialization, split header and first data offer

These are ordinary API histories, not a replacement translation of the
utility wrapper. All internal state facts come from the actual initializer
and preceding public calls.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalDataHistory
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalHeader ZlibF.Spec.Public.Proofs.CompressLocalData
open ZlibF.Spec.Public.Proofs.CompressLocalSymbols ZlibF.Spec.Public.Proofs.CompressLocalPendingData
open ZlibF.Spec.Public.Proofs.CompressLocalLiteralLoop
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- An ordinary client history; each invoked function is the actual
translation. Return values are known to be OK in the theorem below. -/
def splitHeaderPrefix (r : ZStreamRef) (dest source : BPtr) (n : UInt32) : M Int32 := do
  let _ ← deflateInit_ (some r) Z_DEFAULT_COMPRESSION (.ref (.str 57) 0) 112
  zwr (some r) (fun s => {s with next_out := dest,avail_out := 1,next_in := source,avail_in := n})
  let _ ← deflate (some r) Z_NO_FLUSH
  zwr (some r) (fun s => {s with avail_out := 1})
  deflate (some r) Z_NO_FLUSH

/-- The real Fresh history preserves a separate original raw source
object and supplies every data-entry fact. Caller typed-table collisions
are admitted; only this source/output nonaliasing branch is selected. -/
theorem fresh_header_source_ready {h : Heap} {ob oo ib io : Nat} {ia : Array UInt8} {n : UInt32}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (writable : Writable h (.ref (.blk ob) oo) 2)
    (inputBytes : h.bytes ib = some ia) (separate : ib ≠ ob) :
    ∃ after z d,
      splitHeaderPrefix (.tab h.nextBlk) (.ref (.blk ob) oo) (.ref (.blk ib) io) n
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after) ∧
      LocalState after h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) z d ∧
      HeapChains after d 0 ∧ InitialReadFields d ∧ InitialDataControls h.nextBlk d ∧
      SymbolBoundary after (h.nextBlk+1) d [] ∧
      d.pending = 0 ∧ d.status = BUSY_STATE ∧ d.last_flush = -1 ∧
      z.next_in = .ref (.blk ib) io ∧ z.avail_in = n ∧
      z.next_out = .ref (.blk ob) (oo+2) ∧ z.avail_out = 0 ∧ after.bytes ib = some ia := by
  have valid : n ≠ 0 → (Ptr.ref (BRef.blk ib) io : BPtr) ≠ .null := by intro _ bad;cases bad
  obtain ⟨initialized,zi,di,ready,buf,output,init,start,bindings,first,refill,second,state,
      _account,chains,fields,controls,symbols,pending,busy,last,source,input,out,outZero⟩ :=
    fresh_two_header_data_prefix fresh globals allocations writable valid
  let bound := {zi with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := .ref (.blk ib) io,avail_in := n}
  let after := secondHeaderHeap ready (.tab h.nextBlk) (h.nextBlk+1) (h.nextBlk+5) ob oo bound di buf output Z_NO_FLUSH
  have prefixRun : splitHeaderPrefix (.tab h.nextBlk) (.ref (.blk ob) oo) (.ref (.blk ib) io) n
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after) := by
    simp only [C.run] at init bindings refill
    unfold splitHeaderPrefix
    simp only [bind_app,init,bindings,first,refill,second]
    rfl
  obtain ⟨canonical,_z0,_d0,canonicalRun,_local,frame,_live⟩ := fresh_utility_initialization fresh globals allocations
  have sameInit : canonical = initialized := (Prod.mk.inj (Except.ok.inj (canonicalRun.symm.trans init))).2
  subst canonical
  have inputLive : h.live ib := by simp [Heap.live,inputBytes]
  have oldKey : ib < h.nextBlk := fresh.lt inputLive
  have oldSlot := frame.2.2.2.2.2 ib inputLive (by simp)
  have getI : initialized.bytes ib = some ia := oldSlot.1.trans inputBytes
  have actualBinding : C.run (zwr (some (.tab h.nextBlk)) (fun s =>
      {s with next_out := .ref (.blk ob) oo,avail_out := 1,next_in := .ref (.blk ib) io,avail_in := n})) initialized =
      .ok ((),(ZStreamRef.tab h.nextBlk).put initialized bound) := by
    simp only [C.run,zwr_eq,start.representation.live.hz,bound]
  have readyEq := (Prod.mk.inj (Except.ok.inj (bindings.symm.trans actualBinding))).2
  have notPending : ib ≠ h.nextBlk+5 := by omega
  have getAfter : after.bytes ib = some ia := by
    simpa only [after,secondHeaderHeap,pendingDataHeap,pendingCopyHeap,oneHeaderHeap,setD_bytes,ZStreamRef.put_bytes,
      upd_ne _ _ _ _ separate,upd_ne _ _ _ _ notPending,readyEq,ZStreamRef.put_bytes] using getI
  exact ⟨after,_,_,prefixRun,state,chains,fields,controls,symbols,pending,busy,last,source,input,out,outZero,getAfter⟩

/-- The caller replaces all four offer fields after its two header calls. -/
def splitHeaderThenData (r : ZStreamRef) (ob oo : Nat) (source : BPtr) (n : UInt32) : M Int32 := do
  let _ ← splitHeaderPrefix r (.ref (.blk ob) oo) source n
  zwr (some r) (fun s => {s with next_out := .ref (.blk ob) (oo+2),avail_out := 1,next_in := source,avail_in := n})
  deflate (some r) Z_NO_FLUSH

/-- The exact observed heap immediately after the caller's data rebuffer. -/
def splitHeaderOffer (r : ZStreamRef) (ob oo : Nat) (source : BPtr) (n : UInt32) : M Unit := do
  let _ ← splitHeaderPrefix r (.ref (.blk ob) oo) source n
  zwr (some r) (fun s => {s with next_out := .ref (.blk ob) (oo+2),avail_out := 1,next_in := source,avail_in := n})

/-- One same actual Fresh history reaches and completes the first literal
request. This raw-input, separate-output branch requires only original
caller facts; initialized state, chain, symbol and control facts are all
constructed internally. The public utility goal remains unchanged. -/
theorem fresh_split_header_literal {h : Heap} {ob oo ib io : Nat} {ia : Array UInt8}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (writable : Writable h (.ref (.blk ob) oo) 3) (inputBytes : h.bytes ib = some ia)
    (sourceBound : io+263 ≤ ia.size) (separate : ib ≠ ob) :
    ∃ before after offered final result,
      splitHeaderOffer (.tab h.nextBlk) ob oo (.ref (.blk ib) io) 263
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok ((),before) ∧
      (ZStreamRef.tab h.nextBlk).get before = some offered ∧
      deflate (some (.tab h.nextBlk)) Z_NO_FLUSH before = .ok (Z_OK,after) ∧
      splitHeaderThenData (.tab h.nextBlk) ob oo (.ref (.blk ib) io) 263
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after) ∧
      LocalState after h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) final result ∧
      StreamAccounting offered final 263 0 ∧
      offered.next_in = .ref (.blk ib) io ∧ offered.avail_in = 263 ∧
      offered.next_out = .ref (.blk ob) (oo+2) ∧ offered.avail_out = 1 ∧ final.avail_in = 0 ∧
      HeapChains after result 2 ∧ SymbolBoundary after (h.nextBlk+1) result [⟨0,ia[io]!.toNat⟩] ∧
      result.strstart = 2 ∧ result.lookahead = 261 := by
  have writableTwo : Writable h (.ref (.blk ob) oo) 2 := by
    rcases writable with bad | ⟨ref,off,bytes,pointer,get,rw,room⟩
    · exact Or.inl ⟨bad.1,by omega⟩
    · exact Or.inr ⟨ref,off,bytes,pointer,get,rw,by omega⟩
  obtain ⟨header,z,d,prefixRun,state,chains,fields,controls,symbols,pending,busy,last,
      _source,_input,_out,_outZero,getInput⟩ :=
    fresh_header_source_ready (io := io) (n := 263) fresh globals allocations writableTwo inputBytes separate
  let offered := {z with next_out := .ref (.blk ob) (oo+2),avail_out := 1,next_in := .ref (.blk ib) io,avail_in := 263}
  let ready := (ZStreamRef.tab h.nextBlk).put header offered
  obtain ⟨setup,stateR,chainsR,fieldsR,controlsR,symbolsR,_frame⟩ :=
    local_data_rebuffer state chains fields controls symbols (.ref (.blk ob) (oo+2)) (.ref (.blk ib) io) 1 263
  obtain ⟨w,p,q,b,blocks⟩ := stateR.inv.blocks
  obtain ⟨wa,getWindow,windowSize⟩ := blocks.wa
  have windowIdentity : w = h.nextBlk+2 := BRef.blk.inj (Ptr.ref.inj (blocks.win.symm.trans controlsR.2.2.2.2.2.1)).1
  subst w
  have windowSize : wa.size = 65536 := by
    rw [fieldsR.2.2.2.2.1] at windowSize
    exact windowSize
  obtain ⟨d0,pb,buffer,trees⟩ := stateR.trees
  have same : d0 = d := Option.some.inj (trees.base.dstate.symm.trans stateR.live.hs)
  subst d0
  have space : d.sym_next.toNat+3 < d.sym_end.toNat := by
    have lo := trees.base.lit_lo
    have end_ := trees.base.sym_end
    rw [controlsR.1]
    change 0+3 < d.sym_end.toNat
    omega
  have oldKey : ib < h.nextBlk := fresh.lt (by simp [Heap.live,inputBytes])
  have separateWindow : BRef.blk (h.nextBlk+2) ≠ BRef.blk ib := by intro same;cases same;omega
  have getSource : Space.get ready (BRef.blk ib) = some ia := by
    change ready.bytes ib = some ia
    simpa only [ready,ZStreamRef.put_bytes] using getInput
  obtain ⟨after,result,actual,stateA,chainsA,symbolsA,account,empty,ss,la⟩ :=
    local_literal_no_flush stateR fieldsR chainsR symbolsR space busy pending
      (by change (Ptr.ref (BRef.blk ob) (oo+2) : BPtr) ≠ .null;intro bad;cases bad)
      (by change (1 : UInt32) ≠ 0;decide)
      (by rw [last];decide) (by rw [last];decide) controlsR.2.2.2.2.1 controlsR.2.2.2.1
      controlsR.2.2.2.2.2.1 getWindow blocks.wro windowSize rfl getSource
      (by simpa only [show (263 : UInt32).toNat = 263 from by decide +kernel] using sourceBound) rfl
      (Or.inl separateWindow)
  have offerRun : splitHeaderOffer (.tab h.nextBlk) ob oo (.ref (.blk ib) io) 263
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok ((),ready) := by
    simp only [C.run] at setup
    unfold splitHeaderOffer
    simp only [bind_app,prefixRun,setup]
    rfl
  refine ⟨ready,after,offered,_,result,offerRun,stateR.live.hz,actual,?_,stateA,account,rfl,rfl,rfl,rfl,empty,chainsA,symbolsA,ss,la⟩
  unfold splitHeaderThenData
  simp only [C.run] at setup
  simp only [bind_app,prefixRun,setup,actual]


/-- The same real Fresh and split-header history completes a 262-byte
first data request; no internal invariant is assumed by the caller. -/
theorem fresh_split_header_threshold {h : Heap} {ob oo ib io : Nat} {ia : Array UInt8}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (writable : Writable h (.ref (.blk ob) oo) 3) (inputBytes : h.bytes ib = some ia)
    (sourceBound : io+262 ≤ ia.size) (separate : ib ≠ ob) :
    ∃ before after offered final result,
      splitHeaderOffer (.tab h.nextBlk) ob oo (.ref (.blk ib) io) 262
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok ((),before) ∧
      (ZStreamRef.tab h.nextBlk).get before = some offered ∧
      deflate (some (.tab h.nextBlk)) Z_NO_FLUSH before = .ok (Z_OK,after) ∧
      splitHeaderThenData (.tab h.nextBlk) ob oo (.ref (.blk ib) io) 262
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,after) ∧
      LocalState after h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) final result ∧
      StreamAccounting offered final 262 0 ∧
      offered.next_in = .ref (.blk ib) io ∧ offered.avail_in = 262 ∧
      offered.next_out = .ref (.blk ob) (oo+2) ∧ offered.avail_out = 1 ∧ final.avail_in = 0 ∧
      HeapChains after result 1 ∧ result.strstart = 1 ∧ result.lookahead = 261 := by
  have writableTwo : Writable h (.ref (.blk ob) oo) 2 := by
    rcases writable with bad | ⟨ref,off,bytes,pointer,get,rw,room⟩
    · exact Or.inl ⟨bad.1,by omega⟩
    · exact Or.inr ⟨ref,off,bytes,pointer,get,rw,by omega⟩
  obtain ⟨header,z,d,prefixRun,state,chains,fields,controls,symbols,pending,busy,last,
      _source,_input,_out,_outZero,getInput⟩ :=
    fresh_header_source_ready (io := io) (n := 262) fresh globals allocations writableTwo inputBytes separate
  let offered := {z with next_out := .ref (.blk ob) (oo+2),avail_out := 1,next_in := .ref (.blk ib) io,avail_in := 262}
  let ready := (ZStreamRef.tab h.nextBlk).put header offered
  obtain ⟨setup,stateR,chainsR,fieldsR,controlsR,symbolsR,_frame⟩ :=
    local_data_rebuffer state chains fields controls symbols (.ref (.blk ob) (oo+2)) (.ref (.blk ib) io) 1 262
  obtain ⟨w,p,q,b,blocks⟩ := stateR.inv.blocks
  obtain ⟨wa,getWindow,windowSize⟩ := blocks.wa
  have windowIdentity : w = h.nextBlk+2 := BRef.blk.inj (Ptr.ref.inj (blocks.win.symm.trans controlsR.2.2.2.2.2.1)).1
  subst w
  have windowSize : wa.size = 65536 := by
    rw [fieldsR.2.2.2.2.1] at windowSize
    exact windowSize
  have oldKey : ib < h.nextBlk := fresh.lt (by simp [Heap.live,inputBytes])
  have separateWindow : BRef.blk (h.nextBlk+2) ≠ BRef.blk ib := by intro same;cases same;omega
  have getSource : Space.get ready (BRef.blk ib) = some ia := by
    change ready.bytes ib = some ia
    simpa only [ready,ZStreamRef.put_bytes] using getInput
  obtain ⟨after,result,actual,stateA,chainsA,account,empty,ss,la,_credit,_shape,_frame,_live,_nalloc,_next⟩ :=
    ZlibF.Spec.Public.Proofs.CompressLocalThreshold.local_threshold_no_flush stateR fieldsR chainsR busy pending
      (by change (Ptr.ref (BRef.blk ob) (oo+2) : BPtr) ≠ .null;intro bad;cases bad)
      (by change (1 : UInt32) ≠ 0;decide)
      (by rw [last];decide) (by rw [last];decide) controlsR.2.2.2.2.1 controlsR.2.2.2.1
      controlsR.2.2.2.2.2.1 getWindow blocks.wro windowSize rfl getSource
      (by simpa only [show (262 : UInt32).toNat = 262 from by decide +kernel] using sourceBound) rfl
      (Or.inl separateWindow)
  have offerRun : splitHeaderOffer (.tab h.nextBlk) ob oo (.ref (.blk ib) io) 262
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok ((),ready) := by
    simp only [C.run] at setup
    unfold splitHeaderOffer
    simp only [bind_app,prefixRun,setup]
    rfl
  refine ⟨ready,after,offered,_,result,offerRun,stateR.live.hz,actual,?_,stateA,account,rfl,rfl,rfl,rfl,empty,chainsA,ss,la⟩
  unfold splitHeaderThenData
  simp only [C.run] at setup
  simp only [bind_app,prefixRun,setup,actual]


end ZlibF.Spec.Public.Proofs.CompressLocalDataHistory
