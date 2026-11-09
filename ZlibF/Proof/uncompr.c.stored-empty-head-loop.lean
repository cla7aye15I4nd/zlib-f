import ZlibF.Proof.«uncompr.c.stored-head-loop»

namespace Zlib.Uncompr.Proof.StoredEmptyHeadLoop
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec ZlibF.Spec.Public
open StoredPhysicalPrefix
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The zero-length stored block takes the real COPY-done branch without
memcpy. Actual HEAD, LEN/NLEN and Adler parsing still consume all 11 bytes. -/
theorem head_loop {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (input : BitInv h l (StoredWire.wire [])) (mode : s.mode=HEAD)
    (last : s.last=0) (wrap : s.wrap=5) (header : s.head=none) (wbits : s.wbits=15)
    (bits : l.bits=0) (hold : l.hold=0) (flush : c.flush=Z_NO_FLUSH)
    (left : l.left=0) (out : l.out_=0) (put : l.put=.ref (.blk db) 0)
    (get : h.bytes db=some #[]) :
    ∃final after stream state,
      runX (xwhile (pure true) (inflate_dispatch c)) l h=.ok ((.error Ex.leave,final),after) ∧
      Env c after r zs stream state ∧ state.mode=DONE ∧ after.bytes db=some #[] ∧
      final.ret=Z_STREAM_END ∧ final.next=inputAdvance l.next 11 ∧
      final.have_=0 ∧ final.put=.ref (.blk db) 0 ∧ final.left=0 ∧
      final.out_=0 ∧ final.bits=0 ∧ final.hold=0 ∧
      stream.total_out=z.total_out+(UInt32.ofNat ([]:List UInt8).length).toUInt64 ∧
      state.total=s.total+(UInt32.ofNat ([]:List UInt8).length).toUInt64 ∧
      state.check=(adler32 []).toUInt64 ∧ state.wsize=s.wsize ∧ state.last=1 := by
  obtain ⟨hh,lh,ht,lt,ready,P⟩ := physical_prefix E l [] (by decide) input mode last wrap header wbits bits hold flush
  let sp := preparedState s []
  let hp := setI ht zs sp
  let zp := {z with adler:=1}
  let s3 := {sp with mode:=TYPE}
  let s4 := {sp with mode:=CHECK}
  let l3 := {ready with copy:=0}
  have E3 : Env c (setI ht zs s3) r zs zp s3 :=
    ⟨E.strm,E.st,by simpa only [ZStreamRef.get_setI] using P.env.hz,by simp⟩
  have E4 : Env c (setI ht zs s4) r zs zp s4 :=
    ⟨E.strm,E.st,by simpa only [ZStreamRef.get_setI] using P.env.hz,by simp⟩
  have packet4 : BitInv (setI ht zs s4) l3 (be32 (adler32 []).toNat) := by
    have B := P.input.decode_update zs s4
    simp only [setI_setI] at B
    exact ⟨B.have_eq,B.next,B.hold_lt⟩
  have get4 : (setI ht zs s4).bytes db=some #[] := by
    change Space.get (setI ht zs s4) (BRef.blk db)=_
    rw [byte_view_get_setI,←byte_view_get_setI ht zs sp,P.views]
    exact get
  obtain ⟨pulled,pull,nextPull,havePull,checked⟩ := StoredCheckStream.trailer_check_done E4 l3 [] (by decide)
    get4 (P.put.trans put) (P.left.trans left) (P.out.trans out) packet4 P.bits P.hold wrap rfl rfl rfl
  let stream := {zp with
    total_out:=zp.total_out+(UInt32.ofNat ([]:List UInt8).length).toUInt64
    adler:=(adler32 []).toUInt64}
  let state := {s4 with
    total:=s4.total+(UInt32.ofNat ([]:List UInt8).length).toUInt64
    check:=(adler32 []).toUInt64,mode:=DONE}
  let after := setI (r.put (setI ht zs s4) stream) zs state
  let final := {pulled with out_:=0,hold:=0,bits:=0,ret:=Z_STREAM_END}
  have step2 : runX (inflate_dispatch c) lt ht=.ok ((.ok (),l3),setI ht zs s3) := by
    rw [P.stored]
    simpa only [setI_setI] using inflate_COPY_done P.env ready rfl
  have step3 : runX (inflate_dispatch c) l3 (setI ht zs s3)=.ok ((.ok (),l3),setI ht zs s4) := by
    unfold inflate_dispatch
    rw [runX_bind,runX_rdS E3]
    change runX (inflate_TYPE c) l3 (setI ht zs s3)=_
    rw [inflate_TYPE_go c l3 _ (by simp [flush,Z_NO_FLUSH,Z_BLOCK,Z_TREES])]
    have step := inflate_TYPEDO_last E3 l3 (by change (1:Int32)≠0;decide)
    have b : l3.bits=0 := P.bits
    have v : l3.hold=0 := P.hold
    have aligned : bytebits l3=l3 := by
      unfold bytebits
      simp only [b,v]
      change {l3 with hold:=0,bits:=0}=l3
      rw [←b,←v]
    simpa only [aligned,setI_setI] using step
  have stop : runX (inflate_dispatch c) l3 (setI ht zs s4)=.ok ((.error Ex.leave,final),after) := by
    unfold inflate_dispatch
    rw [runX_bind,runX_rdS E4]
    exact checked
  let locals := fun j : Nat => if j=0 then l else if j=1 then lh else if j=2 then lt else l3
  let heaps := fun j : Nat => if j=0 then h else if j=1 then hh else if j=2 then ht
    else if j=3 then setI ht zs s3 else setI ht zs s4
  have steps : ∀j,j<4→runX (inflate_dispatch c) (locals j) (heaps j)=.ok ((.ok (),locals (j+1)),heaps (j+1)) := by
    intro j bound
    have cases : j=0∨j=1∨j=2∨j=3 := by omega
    rcases cases with rfl|rfl|rfl|rfl
    · exact P.head
    · exact P.tag
    · exact step2
    · exact step3
  have loop := xwhile_run_chain (inflate_dispatch c) locals heaps 4 (by decide) Ex.leave final after steps stop
  have pulledShape : pulled.put=l3.put ∧ pulled.left=l3.left := by
    obtain ⟨a,b,u,actual,ub,B,sequence,count,shape,rest⟩ := NEEDBITS_run_complete packet4 32 (by decide)
    have same : b=pulled := congrArg (fun q => q.1.2) (Except.ok.inj (actual.symm.trans pull))
    subst b
    exact ⟨by rw [shape],by rw [shape]⟩
  refine ⟨final,after,stream,state,loop,?_,rfl,?_,rfl,?_,havePull,
    pulledShape.1.trans (P.put.trans put),pulledShape.2.trans (P.left.trans left),rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact ⟨E.strm,E.st,by simp only [after,ZStreamRef.get_setI,ZStreamRef.get_put_same E4.hz],by simp [after]⟩
  · change Space.get after (BRef.blk db)=_
    rw [show after=setI (r.put (setI ht zs s4) stream) zs state from rfl,
      byte_view_get_setI,byte_view_get_stream_put]
    exact get4
  · change pulled.next=inputAdvance l.next 11
    rw [nextPull]
    change inputAdvance ready.next 4=_
    rw [P.cursor,inputAdvance_add]

#print axioms head_loop
end Zlib.Uncompr.Proof.StoredEmptyHeadLoop
