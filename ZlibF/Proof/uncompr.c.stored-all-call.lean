import ZlibF.Proof.«uncompr.c.stored-all-body»
import ZlibF.Proof.«inflate.c.local-public-return»

namespace Zlib.Uncompr.Proof.StoredAllCall
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Actual public inflate, including its automatic header array and free,
completes an entire single stored zlib wire. The local representation is
the one produced by actual initialization; no global heap Uniq or callee
contract is assumed. This whole-input family has any payload and
an exact-size output buffer; it does not replace the general utility goal. -/
theorem inflate_stored_end {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs sb db : Nat}
    {z : ZStream} {s : InflateState} (invariant : LocalStateJ h cutoff r zs z s)
    (allocator : DefAlloc z) (buffers : StreamBuffers h r)
    (payload : List UInt8) (small : payload.length<65536)
    (sourcePtr : z.next_in=.ref (.blk sb) 0) (source : h.bytes sb=some (StoredWire.wire payload).toArray)
    (inputCount : z.avail_in=UInt32.ofNat (StoredWire.wire payload).length)
    (mode : s.mode=HEAD) (last : s.last=0) (wrap : s.wrap=5) (header : s.head=none)
    (wbits : s.wbits=15) (window : s.wsize=0) (bits : s.bits=0) (hold : s.hold=0)
    (room : z.avail_out=UInt32.ofNat payload.length) (put : z.next_out=.ref (.blk db) 0)
    (output : Array UInt8) (get : h.bytes db=some output) (size : output.size=payload.length)
    (write : h.ro db=false) (separate : Separate z.next_in z.avail_in.toNat z.next_out z.avail_out.toNat) :
    ∃after,C.run (inflate (some r) Z_NO_FLUSH) h=.ok (Z_STREAM_END,after) ∧
      after.bytes db=some payload.toArray := by
  have sourceOld : sb≠h.nextBlk := by
    intro eq
    have dead := (fresh_dead invariant.good.fresh (Nat.le_refl _)).1
    rw [←eq,source] at dead
    cases dead
  have outputOld : db≠h.nextBlk := by
    intro eq
    have dead := (fresh_dead invariant.good.fresh (Nat.le_refl _)).1
    rw [←eq,get] at dead
    cases dead
  have sourceA : (syncAlloc h).bytes sb=some (StoredWire.wire payload).toArray :=
    (syncAlloc_bytes_ne h sourceOld).trans source
  have outputA : (syncAlloc h).bytes db=some output := (syncAlloc_bytes_ne h outputOld).trans get
  have writeA : (syncAlloc h).ro db=false := by simpa [syncAlloc,upd_ne _ _ _ _ outputOld] using write
  let c : Ctx := ⟨some r,some (.tab zs),syncBuf h,Z_NO_FLUSH⟩
  have allocated := default_state_syncAlloc invariant
  have E : Env c (syncAlloc h) r zs z s := ⟨rfl,rfl,allocated.good.live.hz,allocated.good.live.hs⟩
  have wireSmall : (StoredWire.wire payload).length<4294967296 := by
    simp only [StoredWire.wire,List.length_append,List.length_cons,List.length_nil,le16,be32]
    omega
  have count : z.avail_in.toNat=(StoredWire.wire payload).length := by
    rw [inputCount]
    exact UInt32.toNat_ofNat_of_lt' wireSmall
  have input : BitInv (syncAlloc h) (StoredInflateBody.loaded z s) (StoredWire.wire payload) := by
    refine ⟨count,Or.inr ⟨.blk sb,(StoredWire.wire payload).toArray,0,sourcePtr,sourceA,?_,?_⟩,?_⟩
    · simp
    · simp
    · change s.hold.toNat<2^s.bits.toNat
      rw [hold,bits]
      decide
  obtain ⟨mid,actualBody,payloadGet⟩ := StoredAllBody.body_end E payload small input
    mode last wrap header wbits window bits hold rfl room put output outputA size writeA separate
  have nonnull : z.next_out≠.null := by rw [put];simp
  have inputValid : z.next_in=.null→z.avail_in=0 := by rw [sourcePtr];intro impossible;cases impossible
  obtain ⟨rc,mid',stream,state,bytes,bodyRun,current,finalAllocator,localGet,localSize,localRo⟩ :=
    inflate_default_view_local_state_return E allocated allocator
      (streamBuffers_syncAlloc invariant.good.fresh buffers) nonnull inputValid
      (syncAlloc_bytes_buf h) (by simp only [syncJunk,Array.size_ofFn]) (syncAlloc_ro_buf h)
  have same := Prod.mk.inj (Except.ok.inj (bodyRun.symm.trans actualBody))
  obtain ⟨rcEq,heapEq⟩ := same
  subst rc
  subst mid

  refine ⟨freeWin mid' (syncBuf h),?_,?_⟩
  · unfold C.run inflate
    rw [bind_app,allocLocalB_run h invariant.good.fresh]
    simp only []
    rw [bind_app]
    have accepted : (z.next_out==.null || (z.next_in==.null && z.avail_in != 0))=false := by
      simp [put,sourcePtr]
    simp only [bind_app,stateCheck_live allocated.good.live,bne_self_eq_false,Bool.false_eq_true,ite_false,
      ldZStream_ok allocated.good.live.hz,accepted,allocated.good.live.zst,castI]
    rw [bind_app] at actualBody
    unfold runX at actualBody
    dsimp only [c] at actualBody
    erw [actualBody]
    simp only []
    change (do freeB (syncBuf h);pure Z_STREAM_END) mid'=.ok (Z_STREAM_END,freeWin mid' (syncBuf h))
    rw [bind_app]
    dsimp only [syncBuf]
    rw [freeBuf_run localGet localRo]
    rfl
  · simpa only [syncBuf,freeWin,upd_ne _ _ _ _ outputOld] using payloadGet

#print axioms inflate_stored_end
end Zlib.Uncompr.Proof.StoredAllCall
