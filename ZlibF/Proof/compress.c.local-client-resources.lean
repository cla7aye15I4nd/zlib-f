import ZlibF.Proof.«compress.c.local-request-resources»
import ZlibF.Proof.«compress.c.local-history-ledger»

/-! # Complete typed resource ledger of the same Fresh client data history -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalClientResources
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalHeader ZlibF.Spec.Public.Proofs.CompressLocalData
open ZlibF.Spec.Public.Proofs.CompressLocalSymbols ZlibF.Spec.Public.Proofs.CompressLocalPendingData
open ZlibF.Spec.Public.Proofs.CompressLocalDataHistory ZlibF.Spec.Public.Proofs.CompressLocalHistoryLedger
open ZlibF.Spec.Public.Proofs.CompressLocalRequestResources
open Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Normalizing one whole byte object preserves equality of each typed
slot. This does not assert a write interval or the separate Store goal. -/
theorem slot_normalize_byte {h after : Heap} {x : Nat} (slot : SlotSame h after x)
    (b : Nat) (original : Array UInt8) :
    SlotSame (Zlib.Trees.Proofs.Out.setB h b original) (Zlib.Trees.Proofs.Out.setB after b original) x := by
  refine ⟨?_,slot.2⟩
  by_cases same : x = b
  · subst x
    simp [Zlib.Trees.Proofs.Out.setB]
  · simpa only [Zlib.Trees.Proofs.Out.setB,upd_ne _ _ _ _ same] using slot.1

/-- Actual initialization, two real header requests, rebuffer and the
complete first 263-byte NO_FLUSH call. Every internal state fact is built
from this history. Old cross-table caller collisions remain permitted.
The frame normalizes the whole output object and is not a slice Store. -/
theorem fresh_literal_resources {h : Heap} {ob oo ib io : Nat} {ia : Array UInt8}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (writable : Writable h (.ref (.blk ob) oo) 3) (inputBytes : h.bytes ib = some ia)
    (sourceBound : io+263 ≤ ia.size) (separate : ib ≠ ob) :
    ∃ before after offered final result original,
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
      result.strstart = 2 ∧ result.lookahead = 261 ∧ h.bytes ob = some original ∧
      result.window = .ref (.blk (h.nextBlk+2)) 0 ∧
      result.prev = .ref (.blk (h.nextBlk+3)) 0 ∧
      result.head = .ref (.blk (h.nextBlk+4)) 0 ∧
      result.pending_buf = .ref (.blk (h.nextBlk+5)) 0 ∧
      Frame h (Zlib.Trees.Proofs.Out.setB after ob original) (fun _ => False) ∧
      after.nextBlk = h.nextBlk+6 ∧ after.nalloc = h.nalloc+5 ∧
      LiveChange h after (fun x => h.nextBlk ≤ x ∧ x < h.nextBlk+6) (fun _ => False) := by
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
  obtain ⟨after,result,actual,stateA,chainsA,symbolsA,account,empty,ss,la,kw,kp,kh,kb,shapeA,frameA,_liveA,allocA,nextA⟩ :=
    literal_no_flush_resources stateR fieldsR chainsR symbolsR space busy pending
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
  obtain ⟨sameHeader,zh,dh,original,headerRun,_stateH,_controlsH,getOriginal,headerFrame,headerNext,headerAlloc,headerLive⟩ :=
    fresh_split_header_resource (source := .ref (.blk ib) io) (n := 263) fresh globals allocations writableTwo (by intro _ bad;cases bad)
  have same : sameHeader = header := (Prod.mk.inj (Except.ok.inj (headerRun.symm.trans prefixRun))).2
  subst sameHeader
  have shapeSetup : Shape header ready := shape_put state.live.hz offered
  have frameSetup : Frame header ready (fun x => StreamRoot (.tab h.nextBlk) x ∨ DeflateOwned (h.nextBlk+1) d x) :=
    full_frame_weaken _frame (fun _ root => Or.inl root)
  have shapeData := shapeSetup.trans shapeA
  have frameData := full_frame_trans_shape frameSetup frameA shapeSetup
  have counts : after.nextBlk = h.nextBlk+6 ∧ after.nalloc = h.nalloc+5 := by
    exact ⟨nextA.trans (by simpa only [ZStreamRef.put_nextBlk] using headerNext),allocA.trans (by simpa only [ZStreamRef.put_nalloc] using headerAlloc)⟩
  have frameAll : Frame h (Zlib.Trees.Proofs.Out.setB after ob original) (fun _ => False) := by
    refine ⟨headerFrame.1.trans frameData.1,headerFrame.2.1.trans frameData.2.1,
      headerFrame.2.2.1.trans frameData.2.2.1,?_,?_,?_⟩
    · change h.nextBlk ≤ after.nextBlk
      rw [counts.1];omega
    · change h.nalloc ≤ after.nalloc
      rw [counts.2];omega
    · intro x oldLive _outside
      have old : x < h.nextBlk := fresh.lt oldLive
      have headerAlive : header.live x := (headerLive x).mpr (Or.inl ⟨oldLive,by simp⟩)
      have outside : ¬(StreamRoot (.tab h.nextBlk) x ∨ DeflateOwned (h.nextBlk+1) d x) := by
        intro member
        simp only [StreamRoot,DeflateOwned,controls.2.2.2.2.2.1,controls.2.2.2.2.2.2.1,
          controls.2.2.2.2.2.2.2.1,controls.2.2.2.2.2.2.2.2,Ptr.ref.injEq,BRef.blk.injEq,WRef.blk.injEq,and_true] at member
        omega
      have row := frameData.2.2.2.2.2 x headerAlive outside
      have firstRow : SlotSame h (Zlib.Trees.Proofs.Out.setB header ob original) x := headerFrame.2.2.2.2.2 x oldLive (by simp)
      exact firstRow.trans (slot_normalize_byte row ob original)
  have liveAll : LiveChange h after (fun x => h.nextBlk ≤ x ∧ x < h.nextBlk+6) (fun _ => False) := by
    intro x
    exact (shapeData.live x).trans (headerLive x)
  refine ⟨ready,after,offered,_,result,original,offerRun,stateR.live.hz,actual,?_,stateA,account,rfl,rfl,rfl,rfl,empty,chainsA,symbolsA,ss,la,
    getOriginal,kw.trans controls.2.2.2.2.2.1,kp.trans controls.2.2.2.2.2.2.1,
    kh.trans controls.2.2.2.2.2.2.2.1,kb.trans controls.2.2.2.2.2.2.2.2,frameAll,counts.1,counts.2,liveAll⟩
  unfold splitHeaderThenData
  simp only [C.run] at setup
  simp only [bind_app,prefixRun,setup,actual]


end ZlibF.Spec.Public.Proofs.CompressLocalClientResources
