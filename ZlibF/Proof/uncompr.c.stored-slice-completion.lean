import ZlibF.Proof.«uncompr.c.stored-slice-loop»
import ZlibF.Proof.«uncompr.c.stored-slice-leave»

namespace Zlib.Uncompr.Proof.StoredSliceCompletion
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public ZlibF.Spec
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The actual COPY loop, physical CHECK/Adler and actual terminal leave
complete with unused output capacity intact. The same executed heaps carry
one exact payload interval frame, unchanged prefix/suffix and exact n-byte
output credit. No allocation occurs on this no-window internal suffix;
whole init/public utility success retains its separate allocator premise.
This is an internal nonempty COPY-entry checkpoint, not a whole caller claim. -/
theorem copy_and_leave {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
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
    (window : s.wsize=0) (wrap : s.wrap = 5) (flags : s.flags = 0) (check : s.check = 1) (adler : z.adler = 1) :
    ∃ final mid after stream state,
      runX (xwhile (pure true) (inflate_dispatch c)) l h=.ok ((.error Ex.leave,final),mid) ∧
      inflate_leave c final mid=.ok (Z_STREAM_END,after) ∧
      Env c after r zs stream state ∧ state.mode=DONE ∧
      stream.avail_in=0 ∧ stream.avail_out=capacity-UInt32.ofNat payload.length ∧
      stream.avail_out.toNat+payload.length=capacity.toNat ∧
      (payload.length<capacity.toNat → stream.avail_out≠0) ∧
      stream.next_out=.ref (.blk db) (oo+payload.length) ∧
      stream.total_out=z.total_out+(UInt32.ofNat payload.length).toUInt64 ∧
      state.total=s.total+(UInt32.ofNat payload.length).toUInt64 ∧
      after.bytes db=some (StoredSliceCopy.patched output oo payload) ∧
      (∀i,i<oo ∨ oo+payload.length≤i → (StoredSliceCopy.patched output oo payload)[i]?=output[i]?) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ b=zs) [⟨l.put,payload.length⟩] := by
  obtain ⟨final,mid,stream0,state0,loop,current,done,outputGet,ret,next,have_,putFinal,leftFinal,outFinal,
      bits0,hold0,streamCount,stateCount,checksum,wsize,last0,size0,outside,frame,shape,writeMid⟩ :=
    StoredSliceLoop.copy_loop E l payload small nonempty input mode last flush capacity enough length left oo put out
      bits hold output get room write separate wrap flags check adler
  have credited : final.out_=final.left := outFinal.trans leftFinal.symm
  have terminal := StoredSliceLeave.leave_done_remaining current final done (wsize.trans window)
    (by rw [last0];exact last) bits0 hold0 ret credited
  let stream := {stream0 with
    next_out:=final.put,avail_out:=final.left,next_in:=final.next,avail_in:=final.have_
    total_in:=stream0.total_in+(final.in_-final.have_).toUInt64,data_type:=64}
  let state := {state0 with hold:=0,bits:=0}
  let after := setI (r.put mid stream) zs state
  have env : Env c after r zs stream state :=
    ⟨E.strm,E.st,by simp only [after,ZStreamRef.get_setI,ZStreamRef.get_put_same current.hz],by simp [after]⟩
  have remaining : stream.avail_out.toNat+payload.length=capacity.toNat := by
    change final.left.toNat+payload.length=capacity.toNat
    rw [leftFinal,UInt32.toNat_sub_of_le _ _ (by
      apply UInt32.le_iff_toNat_le.mpr
      rw [UInt32.toNat_ofNat_of_lt' (by change payload.length<4294967296;omega)]
      exact enough),UInt32.toNat_ofNat_of_lt' (by change payload.length<4294967296;omega)]
    omega
  have positive : payload.length<capacity.toNat→stream.avail_out≠0 := by
    intro strict zero
    have nil := congrArg UInt32.toNat zero
    change stream.avail_out.toNat=0 at nil
    omega
  have writeAfter : Space.ro after (BRef.blk db)=false := by
    rw [show after=setI (r.put mid stream) zs state from rfl,byte_view_ro_setI,byte_view_ro_stream_put]
    exact writeMid
  have metadata := (fastWriteback_heap_frame current.hz current.hs stream state [⟨l.put,payload.length⟩]).1
  have frame0 := frame
  rw [put] at frame0 metadata
  have frameAfter0 := Zlib.Inflate.Proofs.BufferFrame.singleton_trans frame0 metadata shape get writeMid writeAfter
  have frameAfter : BufferFrame h after (fun b => StreamRoot r b ∨ b=zs) [⟨l.put,payload.length⟩] := by
    rw [put]
    exact frameAfter0
  refine ⟨final,mid,after,stream,state,loop,terminal,env,done,have_,leftFinal,remaining,positive,putFinal,
    streamCount,stateCount,?_,outside,frameAfter⟩
  change Space.get after (BRef.blk db)=_
  rw [show after=setI (r.put mid stream) zs state from rfl,byte_view_get_setI,byte_view_get_stream_put]
  exact outputGet

#print axioms copy_and_leave
end Zlib.Uncompr.Proof.StoredSliceCompletion
