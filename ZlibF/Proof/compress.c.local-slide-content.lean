import ZlibF.Proof.«compress.c.local-resume-caller»
import ZlibF.Proof.«compress.c.local-slide»
import ZlibF.Proof.«deflate.c.engine.fill-slide-pending»

/-! # Actual sliding moves the origin of the same logical input -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalSlideContent
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit ZlibF.Spec.Public.Proofs.CompressLocalHash
open ZlibF.Spec.Public.Proofs.CompressLocalContent ZlibF.Spec.Public.Proofs.CompressLocalResumeContent
open ZlibF.Spec.Public.Proofs.CompressLocalSlide ZlibF.Spec.Public.Proofs.CompressLocalLiteral
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The actual slide_hash results retain precisely the surviving hash
positions and valid window suffix, without global typed-key uniqueness. -/
theorem local_slide_chains {h : Heap} {r : ZStreamRef} {cutoff ds w p q top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {pa qa pa' qa' : Array UInt16}
    (state : LocalState h cutoff r ds z d) (env : HashEnv h d w q p wa qa pa)
    (chains : HashChains (wfn qa) (wfn pa) (bfn wa) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat top (fillEnd d))
    (range : fillEnd d≤d.window_size.toNat)
    (taken : d.strstart≥d.w_size+(d.w_size-MIN_LOOKAHEAD_u))
    (head : ∀ i, wfn qa' i=if i<d.hash_size.toNat then slideVal d.w_size (wfn qa i) else wfn qa i)
    (prev : ∀ i, wfn pa' i=if i<d.w_size.toNat then slideVal d.w_size (wfn pa i) else wfn pa i) :
    HeapChains (slideHeap h ds w p q d wa pa' qa') (slideState d) (top-d.w_size.toNat) := by
  have counts := local_fill_slide_counts state env.win env.wbytes range taken
  have sizes := local_slide_window_sizes state
  have slid := chains_slide (h2 := wfn qa') (p2 := wfn pa') (w' := bfn (slideWindow d wa))
    chains state.inv.wsize (by omega)
    (fun i bound => by rw [head i,if_pos bound])
    (fun i bound => by rw [prev i,if_pos bound])
    (local_slide_window_view state env.win env.wbytes range taken)
  refine ⟨w,p,q,slideWindow d wa,pa',qa',env.win,env.prevp,env.headp,?_,?_,?_,?_⟩
  · simp [slideHeap]
  · simp [slideHeap,setW]
  · simp [slideHeap,setW,upd_ne _ _ _ _ env.hne]
  · change HashChains (wfn qa') (wfn pa') (bfn (slideWindow d wa)) d.hash_size d.hash_shift d.hash_mask
      d.w_size.toNat (top-d.w_size.toNat) (fillEnd (slideState d))
    rw [counts.2.2.2.2.2.1]
    exact slid

/-- The complete real sliding prefix constructs the shifted content
boundary. Its logical input and accumulated symbols remain unchanged;
only the physical window origin moves forward by w_size bytes. -/
theorem local_slide_content {h : Heap} {r : ZStreamRef} {cutoff ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (taken : d.strstart≥d.w_size+(d.w_size-MIN_LOOKAHEAD_u)) :
    ∃ w p q wa pa qa pa' qa',
      HashEnv h d w q p wa qa pa ∧ pa'.size=pa.size ∧ qa'.size=qa.size ∧
      fillSlide (some (.tab ds)) d d.w_size (fillMore d) h=
        .ok ((),slideHeap h ds w p q d wa pa' qa') ∧
      LocalContent (slideHeap h ds w p q d wa pa' qa') cutoff r ds z (slideState d)
        input (origin+d.w_size.toNat) base xs ∧
      Shape h (slideHeap h ds w p q d wa pa' qa') ∧
      Frame h (slideHeap h ds w p q d wa pa' qa') (fun k => k=ds ∨ k=w ∨ k=p ∨ k=q) ∧
      (slideState d).strstart.toNat=d.strstart.toNat-d.w_size.toNat ∧
      fillEnd (slideState d)=fillEnd d-d.w_size.toNat := by
  obtain ⟨w,p,q,wa,pa,qa,env,chains⟩ := local_heap_chains_environment boundary.state boundary.chains
  obtain ⟨w0,wa0,win,get,view,form⟩ := boundary.data
  have sameW : w0=w := BRef.blk.inj (Ptr.ref.inj (win.symm.trans env.win)).1
  subst w0
  have sameA : wa0=wa := Option.some.inj (get.symm.trans env.wbytes)
  subst wa0
  have symbols := boundary.symbols
  obtain ⟨b,buf,trees,ledger,balance⟩ := symbols
  have credit := deferred_credit_bounds d
  obtain ⟨qa',pa',run,sizeH,sizeP,head,prev⟩ := local_fill_slide_run boundary.state env trees.base ledger
    boundary.state.inv.sym.2.2.1 balance credit.1 credit.2 boundary.range taken
  let hs := slideHeap h ds w p q d wa pa' qa'
  let slid := slideState d
  have stateS : LocalState hs cutoff r ds z slid := local_slide_state boundary.state env sizeP sizeH
  have geometry := local_fill_slide_counts boundary.state env.win env.wbytes boundary.range taken
  have start : slid.strstart.toNat=d.strstart.toNat-d.w_size.toNat := geometry.2.2.2.2.1
  have endpoint : fillEnd slid=fillEnd d-d.w_size.toNat := geometry.2.2.2.2.2.1
  have insertCount : slid.insert.toNat=min d.insert.toNat slid.strstart.toNat := slide_insert_count d
  have frontierEq : slid.strstart.toNat-slid.insert.toNat=
      (d.strstart.toNat-d.insert.toNat)-d.w_size.toNat := by
    have available := boundary.insert_le
    omega
  have rangeS : fillEnd slid≤slid.window_size.toNat := by
    change fillEnd (slideState d)≤d.window_size.toNat
    have wsz := boundary.state.inv.wsz
    omega
  have chainsS := local_slide_chains boundary.state env chains boundary.range taken head prev
  obtain ⟨fw,fp,fq,fwa,fpa,fqa,fenv,fchains⟩ := local_heap_chains_environment boundary.state boundary.frontier
  have fwId : fw=w := BRef.blk.inj (Ptr.ref.inj (fenv.win.symm.trans env.win)).1
  have fpId : fp=p := WRef.blk.inj (Ptr.ref.inj (fenv.prevp.symm.trans env.prevp)).1
  have fqId : fq=q := WRef.blk.inj (Ptr.ref.inj (fenv.headp.symm.trans env.headp)).1
  subst fw fp fq
  have fwaId : fwa=wa := Option.some.inj (fenv.wbytes.symm.trans env.wbytes)
  have fpaId : fpa=pa := Option.some.inj (fenv.pwords.symm.trans env.pwords)
  have fqaId : fqa=qa := Option.some.inj (fenv.hwords.symm.trans env.hwords)
  subst fwa fpa fqa
  have frontierS : HeapChains hs slid (slid.strstart.toNat-slid.insert.toNat) := by
    rw [frontierEq]
    exact local_slide_chains boundary.state env fchains boundary.range taken head prev
  have history : LazyHistory input (origin+d.w_size.toNat) slid :=
    logical_history_slide boundary.history geometry.1
  have symbolS : SymbolBoundary hs ds slid xs := by
    obtain ⟨wb,pp,qq,bb,blocks⟩ := boundary.state.inv.blocks
    have wid : wb=w := BRef.blk.inj (Ptr.ref.inj (blocks.win.symm.trans env.win)).1
    have bid : bb=b := BRef.blk.inj (Ptr.ref.inj (blocks.pbuf.symm.trans trees.base.pbuf)).1
    subst wb bb
    have buffer : hs.bytes b=some buf := by
      simpa [hs,slideHeap,upd_ne _ _ _ _ blocks.wb.symm] using trees.base.bytes
    have balanceS : BlockBalance slid xs (deferredCredit slid) := by
      apply balance_slide balance (by omega) rfl
      exact (local_block_start_slide_run boundary.state trees.base ledger boundary.state.inv.sym.2.2.1
        balance credit.1 credit.2 boundary.range).2
    exact local_symbol_boundary_of_ledger stateS trees.base.pbuf buffer (slide_ledger ledger) balanceS
  have viewS : ∀ i, i<fillEnd slid → bfn (slideWindow d wa) i=input (origin+d.w_size.toNat+i) := by
    intro i hi
    have original : i+d.w_size.toNat<fillEnd d := by omega
    rw [local_slide_window_view boundary.state env.win env.wbytes boundary.range taken i original,view _ original]
    congr 1
    omega
  have formS : 3≤slid.lookahead.toNat →
      InsHForm slid.hash_shift slid.hash_mask (bfn (slideWindow d wa)) slid.strstart.toNat slid.ins_h := by
    intro large
    change 3≤d.lookahead.toNat at large
    change InsHForm d.hash_shift d.hash_mask (bfn (slideWindow d wa)) slid.strstart.toNat d.ins_h
    apply form_congr (form large)
    · rw [local_slide_window_view boundary.state env.win env.wbytes boundary.range taken _ (by dsimp only [fillEnd];omega)]
      congr 1
      omega
    · rw [local_slide_window_view boundary.state env.win env.wbytes boundary.range taken _ (by dsimp only [fillEnd];omega)]
      congr 1
      omega
  have contentS : LocalContent hs cutoff r ds z slid input (origin+d.w_size.toNat) base xs := by
    refine ⟨stateS,?_,rangeS,history,?_,symbolS,⟨w,slideWindow d wa,env.win,by simp [hs,slideHeap],viewS,formS⟩,
      ?_,frontierS,?_,boundary.trace,?_⟩
    · change HeapChains hs slid slid.strstart.toNat
      rw [start]
      exact chainsS
    · intro _
      change 1≤slid.strstart.toNat
      omega
    · omega
    · intro large
      have zero := boundary.ready large
      simp [slid,slideState,slideBeforeHash,zero,UInt32.lt_iff_toNat_lt]
    · change base+represented xs+pendingCredit d=origin+d.w_size.toNat+slid.strstart.toNat
      have old := boundary.accounted
      omega
  obtain ⟨shape,frame⟩ := local_slide_heap_storage (pa' := pa') (qa' := qa') boundary.state env
  exact ⟨w,p,q,wa,pa,qa,pa',qa',env,sizeP,sizeH,run,contentS,shape,frame,start,endpoint⟩

/-- A complete actual taken-slide refill retains the same original input,
including bytes copied after the slide. This internal continuation uses
an established content boundary, not an assumed callee contract. Reaching
this slide threshold from arbitrary Fresh client histories remains a
separate loop-fold obligation. -/
theorem local_slide_resume_content {h : Heap} {r : ZStreamRef} {cutoff ds origin base io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia : Array UInt8}
    {input : Nat → UInt8} {xs : List Symbol}
    (boundary : LocalContent h cutoff r ds z d input origin base xs)
    (short : d.lookahead.toNat<262)
    (taken : d.strstart≥d.w_size+(d.w_size-MIN_LOOKAHEAD_u))
    (insert : d.insert=0) (wrap : d.wrap=1)
    (pointer : z.next_in=.ref ref io) (incoming : Space.get h ref=some ia)
    (inputBound : io+z.avail_in.toNat≤ia.size) (nonempty : z.avail_in≠0)
    (separate : ∀ w, d.window=.ref (.blk w) 0 → BRef.blk w≠ref)
    (incomingView : ∀ j, j<z.avail_in.toNat → bfn ia (io+j)=input (origin+fillEnd d+j)) :
    ∃ used after next result,
      fill_window (some (.tab ds)) h=.ok ((),after) ∧
      LocalContent after cutoff r ds next result input (origin+d.w_size.toNat) base xs ∧
      StreamAccounting z next used 0 ∧ Shape h after ∧
      Frame h after (fun k => StreamRoot r k ∨ k=ds ∨ DeflateOwned ds d k) ∧
      result.strstart.toNat=d.strstart.toNat-d.w_size.toNat ∧
      fillEnd result=fillEnd d-d.w_size.toNat+used ∧
      (262≤result.lookahead.toNat → ∀ flush, deflate_slow (some (.tab ds)) flush h=
        deflate_slow (some (.tab ds)) flush after) := by
  obtain ⟨w,p,q,wa,pa,qa,pa',qa',env,sizeP,sizeH,prefixRun,contentS,shapeS,frameS,startS,endS⟩ :=
    local_slide_content boundary taken
  let hs := slideHeap h ds w p q d wa pa' qa'
  let slid := slideState d
  let moved := slideWindow d wa
  have getS : hs.bytes w=some moved := by simp [hs,moved,slideHeap]
  have separation := separate w env.win
  have inputS : Space.get hs ref=some ia := (local_slide_input_frame boundary.state separation).trans incoming
  have geometry := local_fill_slide_counts boundary.state env.win env.wbytes boundary.range taken
  have insertS : slid.insert=0 := by simp [slid,slideState,slideBeforeHash,insert]
  have incomingS : ∀ j, j<z.avail_in.toNat →
      bfn ia (io+j)=input ((origin+d.w_size.toNat)+fillEnd slid+j) := by
    intro j hj
    rw [incomingView j hj]
    congr 1
    have endpointMoved : fillEnd slid=fillEnd d-d.w_size.toNat := endS
    have enoughOld : d.w_size.toNat≤fillEnd d := by
      have room := geometry.1
      dsimp only [fillEnd]
      omega
    omega
  obtain ⟨run,contentA,account,frameA,shapeA,endpoint⟩ := local_resume_content contentS env.win getS
    short geometry.2.2.2.2.2.2.2.2 insertS wrap pointer inputS inputBound nonempty (Or.inl separation) incomingS
  have actual := (local_fill_window_slide_transfer boundary.state env sizeP sizeH boundary.range taken prefixRun).trans run
  obtain ⟨wb,pp,qq,pb,blocks⟩ := boundary.state.inv.blocks
  have wi : wb=w := BRef.blk.inj (Ptr.ref.inj (blocks.win.symm.trans env.win)).1
  have pi : pp=p := WRef.blk.inj (Ptr.ref.inj (blocks.prev.symm.trans env.prevp)).1
  have qi : qq=q := WRef.blk.inj (Ptr.ref.inj (blocks.head.symm.trans env.headp)).1
  subst wb pp qq
  have ownsW : DeflateOwned ds d w := Or.inr (Or.inl env.win)
  have ownsP : DeflateOwned ds d p := Or.inr (Or.inr (Or.inl env.prevp))
  have ownsQ : DeflateOwned ds d q := Or.inr (Or.inr (Or.inr (Or.inl env.headp)))
  have frameS' := full_frame_weaken frameS (large := fun k => StreamRoot r k ∨ k=ds ∨ DeflateOwned ds d k)
    (by intro k member;rcases member with same | same | same | same
        · exact Or.inr (Or.inl same)
        · subst k;exact Or.inr (Or.inr ownsW)
        · subst k;exact Or.inr (Or.inr ownsP)
        · subst k;exact Or.inr (Or.inr ownsQ))
  have frameA' := full_frame_weaken frameA (large := fun k => StreamRoot r k ∨ k=ds ∨ DeflateOwned ds d k)
    (by intro k member;rcases member with root | same | same
        · exact Or.inl root
        · exact Or.inr (Or.inl same)
        · subst k;exact Or.inr (Or.inr ownsW))
  have startA : (resumedFillState slid (rbLen z.avail_in (fillMore slid))
      (copyRange moved ia (fillEnd slid) io (rbLen z.avail_in (fillMore slid)).toNat)).strstart=slid.strstart := by
    obtain ⟨key,high,record⟩ := resumed_fill_record slid (rbLen z.avail_in (fillMore slid))
      (copyRange moved ia (fillEnd slid) io (rbLen z.avail_in (fillMore slid)).toNat)
    rw [record]
  refine ⟨(rbLen z.avail_in (fillMore slid)).toNat,_,_,_,actual,contentA,account,shapeS.trans shapeA,
    full_frame_trans_shape frameS' frameA' shapeS,?_,?_,?_⟩
  · rw [startA];exact startS
  · rw [endpoint];exact congrArg (·+(rbLen z.avail_in (fillMore slid)).toNat) endS
  · intro enough flush
    exact CompressLocalResumeCaller.slow_call_prepend_resume boundary.state.live.hs
      (by rw [UInt32.lt_iff_toNat_lt];exact short) actual contentA.state.live.hs
      (by rw [UInt32.lt_iff_toNat_lt];exact Nat.not_lt.mpr enough) flush

end ZlibF.Spec.Public.Proofs.CompressLocalSlideContent
