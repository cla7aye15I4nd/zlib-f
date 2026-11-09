import ZlibF.Proof.«compress.c.local-two-literal-client»
import ZlibF.Proof.«compress.c.local-client-cleanup»

/-! # Actual End/free after the same candidate-capable Fresh history -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalTwoLiteralCleanup
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHeader
open ZlibF.Spec.Public.Proofs.CompressLocalDataHistory ZlibF.Spec.Public.Proofs.CompressLocalHistoryLedger
open ZlibF.Spec.Public.Proofs.CompressLocalClientResources ZlibF.Spec.Public.Proofs.CompressLocalPrivateCleanup
open ZlibF.Spec.Public.Proofs.CompressLocalClientCleanup ZlibF.Spec.Public.Proofs.CompressLocalTwoLiteralClient
open Zlib.Deflate.Proofs.DefaultInit
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000

/-- An ordinary client releases the stream after this NO_FLUSH prefix.
This is an interrupted compression history, not successful FINISH and not
an alternative translation of the compress utility wrapper. -/
def twoLiteralDataAndRelease (r : ZStreamRef) (ob oo : Nat) (source : BPtr) : M Int32 := do
  let _ ← splitHeaderThenData r ob oo source 264
  let rc ← deflateEnd (some r)
  freeZStream (some r)
  pure rc

/-- Every private object in the same actual Fresh init/header/data history
is released by actual End/free. Old caller typed collisions are admitted.
The normalized whole-output frame is not a slice Store theorem. -/
theorem fresh_two_literal_and_release {h : Heap} {ob oo ib io : Nat} {ia : Array UInt8}
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (allocations : ∀ j, j < 5 → h.allocOk (h.nalloc+j) = true)
    (writable : Writable h (.ref (.blk ob) oo) 3) (inputBytes : h.bytes ib = some ia)
    (sourceBound : io+264 ≤ ia.size) (separate : ib ≠ ob) :
    ∃ mid after offered final result original,
      splitHeaderThenData (.tab h.nextBlk) ob oo (.ref (.blk ib) io) 264
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = .ok (Z_OK,mid) ∧
      LocalState mid h.nextBlk (.tab h.nextBlk) (h.nextBlk+1) final result ∧
      StreamAccounting offered final 264 0 ∧
      SymbolBoundary mid (h.nextBlk+1) result [⟨0,ia[io]!.toNat⟩,⟨0,ia[io+1]!.toNat⟩] ∧
      C.run (do let rc ← deflateEnd (some (.tab h.nextBlk));freeZStream (some (.tab h.nextBlk));pure rc) mid =
        .ok ((if result.status == BUSY_STATE then Z_DATA_ERROR else Z_OK),after) ∧
      twoLiteralDataAndRelease (.tab h.nextBlk) ob oo (.ref (.blk ib) io)
        (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) =
        .ok ((if result.status == BUSY_STATE then Z_DATA_ERROR else Z_OK),after) ∧
      h.bytes ob = some original ∧ Frame h (Zlib.Trees.Proofs.Out.setB after ob original) (fun _ => False) ∧
      after.nalloc = h.nalloc+5 ∧ after.nextBlk = h.nextBlk+6 ∧
      (∀ x, after.live x ↔ h.live x) ∧ Fresh after := by
  obtain ⟨before,mid,offered,final,result,original,offer,getOffer,_last,data,state,account,
      _in,_ai,_out,_ao,_empty,_chains,symbols,_ss,_la,getOriginal,window,prev,head,pending,
      frameData,nextData,allocData,liveData⟩ :=
    fresh_two_literal_resources fresh globals allocations writable inputBytes sourceBound separate
  have writableTwo : Writable h (.ref (.blk ob) oo) 2 := by
    rcases writable with bad | ⟨ref,off,bytes,pointer,get,rw,room⟩
    · exact Or.inl ⟨bad.1,by omega⟩
    · exact Or.inr ⟨ref,off,bytes,pointer,get,rw,by omega⟩
  have metadata := observed_offer_metadata fresh globals allocations writableTwo
    (by intro _ bad;cases bad) offer getOffer
  have freeSame : final.zfree = offered.zfree := account.2.2.2.2.2.2.2.2.1
  have allocator : final.zfree = .fn "zcfree" := freeSame.trans metadata.1.2
  obtain ⟨cleanup,liveCleanup,frameCleanup,freshCleanup,allocCleanup,nextCleanup⟩ :=
    private_cleanup state allocator window prev head pending
  let after := ZlibF.Spec.Public.Proofs.CompressTail.releaseLocal
    (endHeap mid (.tab h.nextBlk) (h.nextBlk+1) final result) h.nextBlk
  have frameAll : Frame h (Zlib.Trees.Proofs.Out.setB after ob original) (fun _ => False) := by
    refine ⟨frameData.1.trans frameCleanup.1,frameData.2.1.trans frameCleanup.2.1,
      frameData.2.2.1.trans frameCleanup.2.2.1,?_,?_,?_⟩
    · change h.nextBlk ≤ after.nextBlk
      rw [nextCleanup,nextData];omega
    · change h.nalloc ≤ after.nalloc
      rw [allocCleanup,allocData];omega
    · intro x oldLive _outside
      have low := fresh.lt oldLive
      have outside : ¬(h.nextBlk ≤ x ∧ x < h.nextBlk+6) := by omega
      have midLive := (liveData x).mpr (Or.inl ⟨oldLive,by simp⟩)
      have row : SlotSame mid after x := frameCleanup.2.2.2.2.2 x midLive outside
      have first : SlotSame h (Zlib.Trees.Proofs.Out.setB mid ob original) x := frameData.2.2.2.2.2 x oldLive (by simp)
      exact first.trans (slot_normalize_byte row ob original)
  have liveAll : ∀ x, after.live x ↔ h.live x := by
    intro x
    have clean : after.live x ↔ mid.live x ∧ ¬(h.nextBlk ≤ x ∧ x < h.nextBlk+6) := by
      simpa only [LiveChange,or_false] using liveCleanup x
    have dataLive := liveData x
    constructor
    · intro alive
      have kept := clean.mp alive
      rcases dataLive.mp kept.1 with old | created
      · exact old.1
      · exact False.elim (kept.2 created)
    · intro alive
      have low := fresh.lt alive
      exact clean.mpr ⟨dataLive.mpr (Or.inl ⟨alive,by simp⟩),by omega⟩
  refine ⟨mid,after,offered,final,result,original,data,state,account,symbols,cleanup,?_,getOriginal,
    frameAll,allocCleanup.trans allocData,nextCleanup.trans nextData,liveAll,freshCleanup⟩
  unfold twoLiteralDataAndRelease
  change (splitHeaderThenData (.tab h.nextBlk) ob oo (.ref (.blk ib) io) 264 >>= fun _ =>
    do let rc ← deflateEnd (some (.tab h.nextBlk));freeZStream (some (.tab h.nextBlk));pure rc)
      (ZlibF.Spec.Public.Proofs.CompressCaller.localHeap h) = _
  rw [bind_app,data]
  exact cleanup

end ZlibF.Spec.Public.Proofs.CompressLocalTwoLiteralCleanup
