import ZlibF.Proof.«compress.c.local-content-loop»

/-! # The cumulative real loop reaches the actual sliding checkpoint -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalContentLoopSlide
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalContent ZlibF.Spec.Public.Proofs.CompressLocalContentBodyStep
open ZlibF.Spec.Public.Proofs.CompressLocalContentLoop ZlibF.Spec.Public.Proofs.CompressLocalSlideContent
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A refill is inside the current actual body. Reaching its ready result
therefore retains exactly the remaining source-loop fuel and locals. -/
theorem loop_go_fill_ready {h filled : Heap} {ds : Nat} {d result : DeflateState}
    (state : h.dstates ds=some d) (stateA : filled.dstates ds=some result)
    (short : d.lookahead.toNat<262) (ready : 262≤result.lookahead.toNat)
    (fill : fill_window (some (.tab ds)) h=.ok ((),filled))
    (flush : Int32) (st : LoopS) (running : st.ret=none) (unbroken : st.brk=false) (remaining : Nat) :
    cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) remaining st h=
      cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) remaining st filled := by
  have body := slow_body_fill_ready state stateA short ready fill flush st
  cases remaining with
  | zero => rfl
  | succ remaining =>
    simp only [cwhile.go]
    simp only [forever,pure_app,bind_app,running,unbroken,Option.isSome_none,Bool.false_or,Bool.not_false,
      ite_true,body]

/-- Starting at the real full first-window position, a short-lookahead
ordinary-loop checkpoint necessarily takes the actual slide. Its position,
insert=0 and wrap conditions are derived through the same body history.
The alternative checkpoint is the last-symbol-slot branch, still separate.
The input snapshot refers to original caller bytes and is preserved by the
cumulative typed/byte frame before the actual slide and resumed read. -/
theorem local_window_loop_slide_checkpoint {h : Heap} {r : ZStreamRef} {cutoff ds origin base ib io : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {ia : Array UInt8}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (output : z.avail_out≠0) (initialStart : d.strstart=0) (window : d.w_size=32768)
    (fullWindow : fillEnd d=65536) (wrap : d.wrap=1)
    (pointer : z.next_in=.ref (.blk ib) io) (snapshot : h.bytes ib=some ia)
    (sourceBound : io+z.avail_in.toNat≤ia.size) (nonempty : z.avail_in≠0)
    (outside : ¬DeflateOwned ds d ib)
    (incoming : ∀ j, j<z.avail_in.toNat → bfn ia (io+j)=input (origin+fillEnd d+j))
    (flush : Int32) :
    ∃ n final after result ys,
      ActualOrdinaryPrefix ds flush n {} h final after ∧
      LocalContent after cutoff r ds z result input origin base ys ∧
      n≤d.lookahead.toNat ∧ xs<+:ys ∧ OrdinaryCheckpoint result ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc=h.nalloc ∧ after.nextBlk=h.nextBlk ∧
      cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h=
        cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) (fuel-n) final after ∧
      (result.lookahead.toNat<262 → ∃ used filled next continued,
        fill_window (some (.tab ds)) after=.ok ((),filled) ∧
        LocalContent filled cutoff r ds next continued input (origin+32768) base ys ∧
        StreamAccounting z next used 0 ∧ continued.strstart.toNat=result.strstart.toNat-32768 ∧
        fillEnd continued=fillEnd result-32768+used ∧
        (262≤continued.lookahead.toNat → cwhile forever (deflate_slow_body (some (.tab ds)) flush) {} h=
          cwhile.go forever (deflate_slow_body (some (.tab ds)) flush) (fuel-n) final filled)) := by
  obtain ⟨n,final,after,result,ys,trace,content,count,start,endpoint,record,symbols,bytes,ret,brk,checkpoint,
      shape,frame,_live,alloc,ids,continuation,_meaning⟩ := local_content_ordinary_checkpoint boundary output flush
  refine ⟨n,final,after,result,ys,trace,content,count,symbols,checkpoint,shape,frame,alloc,ids,continuation,?_⟩
  intro short
  have ws : result.w_size=32768 := (congrArg (·.w_size) record).trans window
  have endpointA : result.strstart.toNat+result.lookahead.toNat=65536 := endpoint.trans fullWindow
  have taken : result.strstart≥result.w_size+(result.w_size-MIN_LOOKAHEAD_u) := by
    rw [ws,GE.ge,UInt32.le_iff_toNat_le]
    change 65274≤result.strstart.toNat
    omega
  have firstLook : 262≤d.lookahead.toNat := by
    have originalEnd := fullWindow
    change d.strstart.toNat+d.lookahead.toNat=65536 at originalEnd
    rw [initialStart] at originalEnd
    change 0+d.lookahead.toNat=65536 at originalEnd
    omega
  have insert0 : result.insert=0 := (congrArg (·.insert) record).trans (boundary.ready (by omega))
  have wrapA : result.wrap=1 := (congrArg (·.wrap) record).trans wrap
  have outsideA : ¬DeflateOwned ds result ib := by rw [record_owned record ds];exact outside
  have source : Space.get after (BRef.blk ib)=some ia := (bytes.bytes ib outside).trans snapshot
  have separation : ∀ w, result.window=.ref (.blk w) 0 → BRef.blk w≠BRef.blk ib := by
    intro w win same
    have ids : w=ib := BRef.blk.inj same
    subst w
    exact outsideA (Or.inr (Or.inl win))
  obtain ⟨used,filled,next,continued,fill,contentF,account,_shape,_frame,startF,endF,_slow⟩ :=
    local_slide_resume_content content short taken insert0 wrapA pointer source sourceBound nonempty separation
      (by intro j hj;rw [incoming j hj,endpoint])
  rw [ws] at contentF startF endF
  refine ⟨used,filled,next,continued,fill,contentF,account,startF,endF,?_⟩
  intro ready
  rw [continuation]
  exact loop_go_fill_ready content.state.live.hs contentF.state.live.hs short ready fill flush final ret brk (fuel-n)

end ZlibF.Spec.Public.Proofs.CompressLocalContentLoopSlide
