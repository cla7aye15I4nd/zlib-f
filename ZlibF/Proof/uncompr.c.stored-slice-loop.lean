import ZlibF.Proof.«uncompr.c.stored-slice-copy»
import ZlibF.Proof.«inflate.c.stored-call»
import ZlibF.Proof.«uncompr.c.stored-slice-frame»

namespace Zlib.Uncompr.Proof.StoredSliceLoop
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public ZlibF.Spec
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Actual final stored COPY and physical CHECK terminate with any
capacity at least the nonempty payload length. Remaining output is kept,
only payload bytes are copied and credited, and both array sides remain.
This is an internal COPY-entry result, not a whole utility theorem. -/
theorem copy_loop {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (payload : List UInt8) (small : payload.length < 65536) (nonempty : payload ≠ [])
    (input : BitInv h l (payload ++ be32 (adler32 payload).toNat))
    (mode : s.mode = COPY) (last : s.last ≠ 0) (flush : c.flush = Z_NO_FLUSH)
    (capacity : UInt32) (enough : payload.length≤capacity.toNat)
    (length : s.length=UInt32.ofNat payload.length) (left : l.left=capacity)
    (oo : Nat) (put : l.put=.ref (.blk db) oo) (out : l.out_=capacity)
    (bits : l.bits = 0) (hold : l.hold = 0)
    (output : Array UInt8) (get : h.bytes db = some output)
    (room : oo+capacity.toNat≤output.size) (write : h.ro db=false)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (wrap : s.wrap = 5) (flags : s.flags = 0) (check : s.check = 1) (adler : z.adler = 1) :
    ∃ final after stream state,
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave,final),after) ∧
      Env c after r zs stream state ∧ state.mode = DONE ∧
      after.bytes db=some (StoredSliceCopy.patched output oo payload) ∧
      final.ret = Z_STREAM_END ∧ final.next = inputAdvance l.next (payload.length+4) ∧
      final.have_ = 0 ∧ final.put=.ref (.blk db) (oo+payload.length) ∧
      final.left=capacity-UInt32.ofNat payload.length ∧ final.out_=capacity-UInt32.ofNat payload.length ∧ final.bits = 0 ∧ final.hold = 0 ∧
      stream.total_out = z.total_out + (UInt32.ofNat payload.length).toUInt64 ∧
      state.total = s.total + (UInt32.ofNat payload.length).toUInt64 ∧
      state.check=(adler32 payload).toUInt64 ∧ state.wsize=s.wsize ∧ state.last=s.last ∧
      (StoredSliceCopy.patched output oo payload).size=output.size ∧
      (∀i,i<oo ∨ oo+payload.length≤i → (StoredSliceCopy.patched output oo payload)[i]?=output[i]?) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b=zs) [⟨l.put,payload.length⟩] ∧
      Shape h after ∧ Space.ro after (BRef.blk db)=false := by
  let base := Space.put h (BRef.blk db) (StoredSliceCopy.patched output oo payload)
  let s1 := {s with length := 0}
  let s2 := {s1 with mode := TYPE}
  let s3 := {s1 with mode := CHECK}
  have baseZ : r.get base = some z := by rw [byte_view_put_stream];exact E.hz
  have E1 : Env c (setI base zs s1) r zs z s1 :=
    ⟨E.strm,E.st,by simpa only [ZStreamRef.get_setI] using baseZ,by simp⟩
  have E2 : Env c (setI base zs s2) r zs z s2 :=
    ⟨E.strm,E.st,by simpa only [ZStreamRef.get_setI] using baseZ,by simp⟩
  have E3 : Env c (setI base zs s3) r zs z s3 :=
    ⟨E.strm,E.st,by simpa only [ZStreamRef.get_setI] using baseZ,by simp⟩
  obtain ⟨l1,copy,packet,cursor,put1,left1,hold1,bits1,out1,copiedSize,copiedSlice,copiedOutside⟩ :=
    StoredSliceCopy.copy_slice E l payload small nonempty input capacity enough length left oo put output get room write separate
  let l2 := {l1 with copy := 0}
  have packet2 : BitInv (setI base zs s3) l2 (be32 (adler32 payload).toNat) := by
    have B := packet.decode_update zs s3
    simp only [setI_setI] at B
    exact ⟨B.have_eq,B.next,B.hold_lt⟩
  have get3 : (setI base zs s3).bytes db=some (StoredSliceCopy.patched output oo payload) := by
    change Space.get (setI base zs s3) (BRef.blk db) = _
    rw [byte_view_get_setI]
    exact byte_view_get_put get write (StoredSliceCopy.patched output oo payload)
  have produced : l2.out_-l2.left=UInt32.ofNat payload.length := by
    change l1.out_-l1.left=_
    rw [out1,out,left1]
    exact u32_used_of_remaining capacity (UInt32.ofNat payload.length)
      (by rw [UInt32.toNat_ofNat_of_lt' (by change payload.length<4294967296;omega)];exact enough)
  have outputFit : oo+payload.length≤(StoredSliceCopy.patched output oo payload).size := by rw [copiedSize];omega
  obtain ⟨ready,pull,nextReady,haveReady,checked⟩ :=
    StoredSliceCheckStream.trailer_check_done E3 l2 payload small (StoredSliceCopy.patched output oo payload) oo
      get3 outputFit copiedSlice.symm put1 produced packet2 (bits1.trans bits) (hold1.trans hold) wrap flags check adler
  let stream := {z with
    total_out := z.total_out+(UInt32.ofNat payload.length).toUInt64
    adler := (adler32 payload).toUInt64}
  let state := {s3 with
    total := s3.total+(UInt32.ofNat payload.length).toUInt64
    check := (adler32 payload).toUInt64,mode := DONE}
  let after := setI (r.put (setI base zs s3) stream) zs state
  let final := {ready with out_ := l2.left,hold := 0,bits := 0,ret := Z_STREAM_END}
  have step0 : runX (inflate_dispatch c) l h = .ok ((.ok (),l1),setI base zs s1) := by
    unfold inflate_dispatch
    rw [runX_bind,runX_rdS E]
    simp only [mode]
    exact copy
  have step1 : runX (inflate_dispatch c) l1 (setI base zs s1) =
      .ok ((.ok (),l2),setI base zs s2) := by
    unfold inflate_dispatch
    rw [runX_bind,runX_rdS E1]
    simp only [show s1.mode = COPY from mode]
    change runX (inflate_COPY c) l1 (setI base zs s1) = _
    simpa only [setI_setI] using inflate_COPY_done E1 l1 rfl
  have step2 : runX (inflate_dispatch c) l2 (setI base zs s2) =
      .ok ((.ok (),l2),setI base zs s3) := by
    unfold inflate_dispatch
    rw [runX_bind,runX_rdS E2]
    change runX (inflate_TYPE c) l2 (setI base zs s2) = _
    rw [inflate_TYPE_go c l2 _ (by simp [flush,Z_NO_FLUSH,Z_BLOCK,Z_TREES])]
    have step := inflate_TYPEDO_last E2 l2 last
    have bits2 : l2.bits = 0 := bits1.trans bits
    have hold2 : l2.hold = 0 := hold1.trans hold
    have aligned : bytebits l2 = l2 := by
      unfold bytebits
      simp only [bits2,hold2]
      change {l2 with hold := 0,bits := 0} = l2
      rw [←hold2,←bits2]
    simpa only [aligned,setI_setI] using step
  have stop : runX (inflate_dispatch c) l2 (setI base zs s3) =
      .ok ((.error Ex.leave,final),after) := by
    unfold inflate_dispatch
    rw [runX_bind,runX_rdS E3]
    exact checked
  let locals := fun j : Nat => if j=0 then l else if j=1 then l1 else l2
  let heaps := fun j : Nat => if j=0 then h else if j=1 then setI base zs s1
    else if j=2 then setI base zs s2 else setI base zs s3
  have steps : ∀j,j<3→runX (inflate_dispatch c) (locals j) (heaps j) =
      .ok ((.ok (),locals (j+1)),heaps (j+1)) := by
    intro j bound
    have cases : j=0∨j=1∨j=2 := by omega
    rcases cases with rfl|rfl|rfl
    · exact step0
    · exact step1
    · exact step2
  have loop := xwhile_run_chain (inflate_dispatch c) locals heaps 3 (by decide) Ex.leave final after steps stop
  have readyShape : ready.put = l2.put ∧ ready.left = l2.left := by
    obtain ⟨a,b,u,actual,ub,B,streamEq,count,shape,rest⟩ := NEEDBITS_run_complete packet2 32 (by decide)
    have same : b=ready := congrArg (fun q => q.1.2) (Except.ok.inj (actual.symm.trans pull))
    subst b
    exact ⟨by rw [shape],by rw [shape]⟩
  let changed := fun b => StreamRoot r b ∨ b=zs
  let regions : List Region := [⟨.ref (.blk db) oo,payload.length⟩]
  have patchFrame : BufferFrame h base changed regions :=
    StoredSliceFrame.write_buffer_frame get copiedSize copiedOutside changed
  have baseState : base.istates zs=some s := by rw [byte_view_put_istates];exact E.hs
  have metadata := (fastWriteback_heap_frame baseZ baseState stream state regions).1
  have metaFrame : BufferFrame base after changed regions := by
    simpa only [after,ZStreamRef.put_setI,setI_setI] using metadata
  have baseRo : Space.ro base (BRef.blk db)=false := write
  have afterRo : Space.ro after (BRef.blk db)=false := by
    rw [show after=setI (r.put (setI base zs s3) stream) zs state from rfl,
      byte_view_ro_setI,byte_view_ro_stream_put,byte_view_ro_setI]
    exact baseRo
  have frame := Zlib.Inflate.Proofs.BufferFrame.singleton_trans patchFrame metaFrame (byte_view_put_shape get write (StoredSliceCopy.patched output oo payload))
    get baseRo afterRo
  refine ⟨final,after,stream,state,loop,?_,rfl,?_,rfl,?_,haveReady,
    readyShape.1.trans put1,readyShape.2.trans left1,left1,rfl,rfl,rfl,rfl,rfl,rfl,rfl,copiedSize,copiedOutside,?frame,?shape,afterRo⟩
  · exact ⟨E.strm,E.st,by simp only [after,ZStreamRef.get_setI,ZStreamRef.get_put_same E3.hz],by simp [after]⟩
  · change Space.get after (BRef.blk db) = _
    rw [show after = setI (r.put (setI base zs s3) stream) zs state from rfl,
      byte_view_get_setI,byte_view_get_stream_put]
    exact get3
  · change ready.next = inputAdvance l.next (payload.length+4)
    rw [nextReady]
    change inputAdvance l1.next 4 = _
    rw [cursor,inputAdvance_add]
  case frame =>
    rw [put]
    exact frame
  case shape =>
    have first := byte_view_put_shape (dest:=BRef.blk db) get write (StoredSliceCopy.patched output oo payload)
    have second := shape_put baseZ stream
    have third := shape_setI (by simpa using baseState : (r.put base stream).istates zs=some s) state
    simpa only [after,ZStreamRef.put_setI,setI_setI] using first.trans (second.trans third)

#print axioms copy_loop
end Zlib.Uncompr.Proof.StoredSliceLoop
