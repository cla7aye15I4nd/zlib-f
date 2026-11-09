import ZlibF.Proof.«uncompr.c.stored-copy-payload»
import ZlibF.Proof.«inflate.c.stored-call»

namespace Zlib.Uncompr.Proof.StoredCopyLoop
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public ZlibF.Spec
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Starting at the final stored COPY, the actual dispatch loop copies an
arbitrary nonempty payload and consumes its physical Adler trailer. This
is a terminating loop execution, not a continuation contract. Header and
caller entry are separate producers of this internal cutpoint. -/
theorem copy_loop {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (payload : List UInt8) (small : payload.length < 65536) (nonempty : payload ≠ [])
    (input : BitInv h l (payload ++ be32 (adler32 payload).toNat))
    (mode : s.mode = COPY) (last : s.last ≠ 0) (flush : c.flush = Z_NO_FLUSH)
    (length : s.length = UInt32.ofNat payload.length) (left : l.left = UInt32.ofNat payload.length)
    (put : l.put = .ref (.blk db) 0) (out : l.out_ = UInt32.ofNat payload.length)
    (bits : l.bits = 0) (hold : l.hold = 0)
    (output : Array UInt8) (get : h.bytes db = some output)
    (size : output.size = payload.length) (write : h.ro db = false)
    (separate : Separate l.next l.have_.toNat l.put l.left.toNat)
    (wrap : s.wrap = 5) (flags : s.flags = 0) (check : s.check = 1) (adler : z.adler = 1) :
    ∃ final after stream state,
      runX (xwhile (pure true) (inflate_dispatch c)) l h = .ok ((.error Ex.leave,final),after) ∧
      Env c after r zs stream state ∧ state.mode = DONE ∧
      after.bytes db = some payload.toArray ∧
      final.ret = Z_STREAM_END ∧ final.next = inputAdvance l.next (payload.length+4) ∧
      final.have_ = 0 ∧ final.put = .ref (.blk db) payload.length ∧
      final.left = 0 ∧ final.out_ = 0 ∧ final.bits = 0 ∧ final.hold = 0 ∧
      stream.total_out = z.total_out + (UInt32.ofNat payload.length).toUInt64 ∧
      state.total = s.total + (UInt32.ofNat payload.length).toUInt64 ∧
      state.check = (adler32 payload).toUInt64 := by
  let base := Space.put h (BRef.blk db) payload.toArray
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
  obtain ⟨l1,copy,packet,cursor,put1,left1,hold1,bits1,out1⟩ :=
    StoredCopyPayload.copy_payload E l payload small nonempty input length left put output get size write separate
  let l2 := {l1 with copy := 0}
  have packet2 : BitInv (setI base zs s3) l2 (be32 (adler32 payload).toNat) := by
    have B := packet.decode_update zs s3
    simp only [setI_setI] at B
    exact ⟨B.have_eq,B.next,B.hold_lt⟩
  have get3 : (setI base zs s3).bytes db = some payload.toArray := by
    change Space.get (setI base zs s3) (BRef.blk db) = _
    rw [byte_view_get_setI]
    exact byte_view_get_put get write payload.toArray
  obtain ⟨ready,pull,nextReady,haveReady,checked⟩ :=
    StoredCheckStream.trailer_check_done E3 l2 payload small get3 put1 left1 (out1.trans out)
      packet2 (bits1.trans bits) (hold1.trans hold) wrap flags check adler
  let stream := {z with
    total_out := z.total_out+(UInt32.ofNat payload.length).toUInt64
    adler := (adler32 payload).toUInt64}
  let state := {s3 with
    total := s3.total+(UInt32.ofNat payload.length).toUInt64
    check := (adler32 payload).toUInt64,mode := DONE}
  let after := setI (r.put (setI base zs s3) stream) zs state
  let final := {ready with out_ := 0,hold := 0,bits := 0,ret := Z_STREAM_END}
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
  refine ⟨final,after,stream,state,loop,?_,rfl,?_,rfl,?_,haveReady,
    readyShape.1.trans put1,readyShape.2.trans left1,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · exact ⟨E.strm,E.st,by simp only [after,ZStreamRef.get_setI,ZStreamRef.get_put_same E3.hz],by simp [after]⟩
  · change Space.get after (BRef.blk db) = _
    rw [show after = setI (r.put (setI base zs s3) stream) zs state from rfl,
      byte_view_get_setI,byte_view_get_stream_put]
    exact get3
  · change ready.next = inputAdvance l.next (payload.length+4)
    rw [nextReady]
    change inputAdvance l1.next 4 = _
    rw [cursor,inputAdvance_add]

#print axioms copy_loop
end Zlib.Uncompr.Proof.StoredCopyLoop
