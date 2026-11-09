import ZlibF.Proof.«uncompr.c.stored-physical-prefix»
import ZlibF.Proof.«uncompr.c.stored-copy-loop»

namespace Zlib.Uncompr.Proof.StoredHeadLoop
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec ZlibF.Spec.Public
open StoredPhysicalPrefix
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The actual mode loop consumes a complete single stored-block zlib wire
for every nonempty payload below the format's 16-bit length limit. It
starts at real HEAD, parses all headers, copies the actual bytes and
checks the physical trailer before returning STREAM_END. This is the
codec mode loop; the utility refill/finish shell is a separate layer. -/
theorem head_loop {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (payload : List UInt8) (small : payload.length<65536) (nonempty : payload≠[])
    (input : BitInv h l (StoredWire.wire payload)) (mode : s.mode=HEAD)
    (last : s.last=0) (wrap : s.wrap=5) (header : s.head=none) (wbits : s.wbits=15)
    (bits : l.bits=0) (hold : l.hold=0) (flush : c.flush=Z_NO_FLUSH)
    (left : l.left=UInt32.ofNat payload.length) (out : l.out_=UInt32.ofNat payload.length)
    (put : l.put=.ref (.blk db) 0) (output : Array UInt8) (get : h.bytes db=some output)
    (size : output.size=payload.length) (write : h.ro db=false)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat) :
    ∃final after stream state,
      runX (xwhile (pure true) (inflate_dispatch c)) l h=.ok ((.error Ex.leave,final),after) ∧
      Env c after r zs stream state ∧ state.mode=DONE ∧ after.bytes db=some payload.toArray ∧
      final.ret=Z_STREAM_END ∧ final.next=inputAdvance l.next (payload.length+11) ∧
      final.have_=0 ∧ final.put=.ref (.blk db) payload.length ∧ final.left=0 ∧
      final.out_=0 ∧ final.bits=0 ∧ final.hold=0 ∧
      stream.total_out=z.total_out+(UInt32.ofNat payload.length).toUInt64 ∧
      state.total=s.total+(UInt32.ofNat payload.length).toUInt64 ∧
      state.check=(adler32 payload).toUInt64 ∧ state.wsize=s.wsize ∧ state.last=1 := by
  obtain ⟨hh,lh,ht,lt,ready,P⟩ := physical_prefix E l payload small input mode last wrap header wbits bits hold flush
  let sp := preparedState s payload
  let hp := setI ht zs sp
  let zp := {z with adler:=1}
  have copiedGet : hp.bytes db=some output := by
    change Space.get hp (BRef.blk db)=_
    rw [P.views]
    exact get
  have copiedRo : hp.ro db=false := by
    change Space.ro hp (BRef.blk db)=_
    rw [P.readonly]
    exact write
  have leftReady : ready.left=UInt32.ofNat payload.length := P.left.trans left
  have putReady : ready.put=.ref (.blk db) 0 := P.put.trans put
  have sep : Separate ready.next ready.have_.toNat ready.put ready.left.toNat := by
    have bound : 7≤l.have_.toNat := by
      rw [input.have_eq]
      simp only [StoredWire.wire,List.length_append,List.length_cons,List.length_nil,le16,be32]
      omega
    have advanced := inputAdvance_separate l.next l.put l.have_.toNat l.left.toNat 7 bound separate
    have count : l.have_.toNat-7=ready.have_.toNat := by
      rw [input.have_eq,P.input.have_eq]
      simp only [StoredWire.wire,List.length_append,List.length_cons,List.length_nil,le16,be32]
      omega
    rw [count,←P.cursor,←P.put,←P.left] at advanced
    exact advanced
  obtain ⟨l3,copy,packet,cursor,put3,left3,hold3,bits3,out3⟩ :=
    StoredCopyPayload.copy_payload P.env ready payload small nonempty P.input rfl leftReady putReady
      output copiedGet size copiedRo sep
  let base := Space.put hp (BRef.blk db) payload.toArray
  let s3 := {sp with length:=0}
  let s4 := {s3 with mode:=TYPE}
  let s5 := {s3 with mode:=CHECK}
  let l4 := {l3 with copy:=0}
  have baseZ : r.get base=some zp := by rw [byte_view_put_stream];exact P.env.hz
  have E3 : Env c (setI base zs s3) r zs zp s3 :=
    ⟨E.strm,E.st,by simpa only [ZStreamRef.get_setI] using baseZ,by simp⟩
  have E4 : Env c (setI base zs s4) r zs zp s4 :=
    ⟨E.strm,E.st,by simpa only [ZStreamRef.get_setI] using baseZ,by simp⟩
  have E5 : Env c (setI base zs s5) r zs zp s5 :=
    ⟨E.strm,E.st,by simpa only [ZStreamRef.get_setI] using baseZ,by simp⟩
  have packet5 : BitInv (setI base zs s5) l4 (be32 (adler32 payload).toNat) := by
    have B := packet.decode_update zs s5
    simp only [setI_setI] at B
    exact ⟨B.have_eq,B.next,B.hold_lt⟩
  have get5 : (setI base zs s5).bytes db=some payload.toArray := by
    change Space.get (setI base zs s5) (BRef.blk db)=_
    rw [byte_view_get_setI]
    exact byte_view_get_put copiedGet copiedRo payload.toArray
  obtain ⟨pulled,pull,nextPull,havePull,checked⟩ :=
    StoredCheckStream.trailer_check_done E5 l4 payload small get5 put3 left3 ((out3.trans P.out).trans out)
      packet5 (bits3.trans P.bits) (hold3.trans P.hold) wrap rfl rfl rfl
  let stream := {zp with
    total_out:=zp.total_out+(UInt32.ofNat payload.length).toUInt64
    adler:=(adler32 payload).toUInt64}
  let state := {s5 with
    total:=s5.total+(UInt32.ofNat payload.length).toUInt64
    check:=(adler32 payload).toUInt64
    mode:=DONE}
  let after := setI (r.put (setI base zs s5) stream) zs state
  let final := {pulled with out_:=0,hold:=0,bits:=0,ret:=Z_STREAM_END}
  have step2 : runX (inflate_dispatch c) lt ht=.ok ((.ok (),l3),setI base zs s3) :=
    P.stored.trans copy
  have step3 : runX (inflate_dispatch c) l3 (setI base zs s3)=.ok ((.ok (),l4),setI base zs s4) := by
    unfold inflate_dispatch
    rw [runX_bind,runX_rdS E3]
    change runX (inflate_COPY c) l3 (setI base zs s3)=_
    simpa only [setI_setI] using inflate_COPY_done E3 l3 rfl
  have step4 : runX (inflate_dispatch c) l4 (setI base zs s4)=.ok ((.ok (),l4),setI base zs s5) := by
    unfold inflate_dispatch
    rw [runX_bind,runX_rdS E4]
    change runX (inflate_TYPE c) l4 (setI base zs s4)=_
    rw [inflate_TYPE_go c l4 _ (by simp [flush,Z_NO_FLUSH,Z_BLOCK,Z_TREES])]
    have step := inflate_TYPEDO_last E4 l4 (by change (1:Int32)≠0;decide)
    have b : l4.bits=0 := bits3.trans P.bits
    have v : l4.hold=0 := hold3.trans P.hold
    have aligned : bytebits l4=l4 := by
      unfold bytebits
      simp only [b,v]
      change {l4 with hold:=0,bits:=0}=l4
      rw [←b,←v]
    simpa only [aligned,setI_setI] using step
  have stop : runX (inflate_dispatch c) l4 (setI base zs s5)=.ok ((.error Ex.leave,final),after) := by
    unfold inflate_dispatch
    rw [runX_bind,runX_rdS E5]
    exact checked
  let locals := fun j : Nat => if j=0 then l else if j=1 then lh else if j=2 then lt else if j=3 then l3 else l4
  let heaps := fun j : Nat => if j=0 then h else if j=1 then hh else if j=2 then ht
    else if j=3 then setI base zs s3 else if j=4 then setI base zs s4 else setI base zs s5
  have steps : ∀j,j<5→runX (inflate_dispatch c) (locals j) (heaps j)=.ok ((.ok (),locals (j+1)),heaps (j+1)) := by
    intro j bound
    have cases : j=0∨j=1∨j=2∨j=3∨j=4 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl
    · exact P.head
    · exact P.tag
    · exact step2
    · exact step3
    · exact step4
  have loop := xwhile_run_chain (inflate_dispatch c) locals heaps 5 (by decide) Ex.leave final after steps stop
  have readyShape : pulled.put=l4.put ∧ pulled.left=l4.left := by
    obtain ⟨a,b,u,actual,ub,B,sequence,count,shape,rest⟩ := NEEDBITS_run_complete packet5 32 (by decide)
    have same : b=pulled := congrArg (fun q => q.1.2) (Except.ok.inj (actual.symm.trans pull))
    subst b
    exact ⟨by rw [shape],by rw [shape]⟩
  refine ⟨final,after,stream,state,loop,?_,rfl,?_,rfl,?_,havePull,
    readyShape.1.trans put3,readyShape.2.trans left3,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact ⟨E.strm,E.st,by simp only [after,ZStreamRef.get_setI,ZStreamRef.get_put_same E5.hz],by simp [after]⟩
  · change Space.get after (BRef.blk db)=_
    rw [show after=setI (r.put (setI base zs s5) stream) zs state from rfl,
      byte_view_get_setI,byte_view_get_stream_put]
    exact get5
  · change pulled.next=inputAdvance l.next (payload.length+11)
    rw [nextPull]
    change inputAdvance l3.next 4=_
    rw [cursor,P.cursor,inputAdvance_add,inputAdvance_add]
    congr 1
    omega

#print axioms head_loop
end Zlib.Uncompr.Proof.StoredHeadLoop
