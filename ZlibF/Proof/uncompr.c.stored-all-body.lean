import ZlibF.Proof.«uncompr.c.stored-empty-head-loop»
import ZlibF.Proof.«uncompr.c.stored-inflate-body»

namespace Zlib.Uncompr.Proof.StoredAllBody
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec ZlibF.Spec.Public
open StoredInflateBody (loaded)
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Empty and nonempty payloads use their proved actual branch executions. -/
theorem head_loop {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (payload : List UInt8) (small : payload.length<65536)
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
  by_cases empty : payload=[]
  · subst payload
    have arrayEmpty : output=#[] := Array.eq_empty_of_size_eq_zero size
    subst output
    exact StoredEmptyHeadLoop.head_loop E l input mode last wrap header wbits bits hold flush left out put get
  · exact StoredHeadLoop.head_loop E l payload small empty input mode last wrap header wbits bits hold flush
      left out put output get size write separate

/-- The actual LOAD, complete mode loop and actual terminal leave return
STREAM_END and the exact payload. The surrounding public temporary-array
allocation and free are deliberately left to the existing public shell. -/
theorem body_end {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (payload : List UInt8) (small : payload.length<65536)
    (input : BitInv h (loaded z s) (StoredWire.wire payload)) (mode : s.mode=HEAD)
    (last : s.last=0) (wrap : s.wrap=5) (header : s.head=none) (wbits : s.wbits=15)
    (window : s.wsize=0) (bits : s.bits=0) (hold : s.hold=0) (flush : c.flush=Z_NO_FLUSH)
    (room : z.avail_out=UInt32.ofNat payload.length) (put : z.next_out=.ref (.blk db) 0)
    (output : Array UInt8) (get : h.bytes db=some output) (size : output.size=payload.length)
    (write : h.ro db=false) (separate : Separate z.next_in z.avail_in.toNat z.next_out z.avail_out.toNat) :
    ∃after,
      (do
        let (result,regs) ← runX (inflate_run c) IL.init
        match result with
        | .error (.ret value) => pure value
        | _ => inflate_leave c regs) h=.ok (Z_STREAM_END,after) ∧
      after.bytes db=some payload.toArray := by
  obtain ⟨final,mid,stream,state,loop,current,done,outputExact,ret,next,have_,outPtr,left,out,bits0,hold0,
      streamCount,stateCount,checksum,wsize,finalLast⟩ :=
    head_loop E (loaded z s) payload small input mode last wrap header wbits bits hold flush
      room room put output get size write separate
  have actualRun : runX (inflate_run c) IL.init h=.ok ((.error Ex.leave,final),mid) := by
    unfold inflate_run
    rw [runX_bind,runX_rdS E]
    simp only [mode]
    change runX (do
      LOAD c.strm c.st
      modify fun l => {l with in_:=l.have_,out_:=l.left,ret:=Z_OK}
      xwhile (pure true) (inflate_dispatch c)) IL.init h=_
    rw [runX_bind,LOAD_run E]
    simp only []
    rw [runX_bind,runX_modify]
    exact loop
  have terminal := StoredTerminalLeave.leave_done current final done (wsize.trans window)
    (by rw [finalLast];decide) bits0 hold0 ret out left
  let after := setI (r.put mid {stream with
    next_out:=final.put,avail_out:=0,next_in:=final.next,avail_in:=final.have_
    total_in:=stream.total_in+(final.in_-final.have_).toUInt64,data_type:=64}) zs
      {state with hold:=0,bits:=0}
  refine ⟨after,?_,?_⟩
  · rw [bind_app,actualRun]
    exact terminal
  · change Space.get (setI (r.put mid _) zs _) (BRef.blk db)=some payload.toArray
    rw [byte_view_get_setI,byte_view_get_stream_put]
    exact outputExact

#print axioms head_loop
#print axioms body_end
end Zlib.Uncompr.Proof.StoredAllBody
