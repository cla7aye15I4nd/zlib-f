import ZlibF.Proof.«inflate.c.stored-call»

namespace Zlib.Uncompr.Proof.StoredTerminalLeave
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxRecDepth 100000

/-- CHECK has already credited every output byte. The actual terminal
leave therefore allocates no window and does not credit output or update
its checksum twice. Input totals and public cursors are written exactly. -/
theorem leave_done {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (mode : s.mode=DONE) (window : s.wsize=0) (last : s.last≠0)
    (bits : l.bits=0) (hold : l.hold=0) (ret : l.ret=Z_STREAM_END)
    (out : l.out_=0) (left : l.left=0) :
    inflate_leave c l h=.ok (Z_STREAM_END,
      setI (r.put h {z with
        next_out:=l.put,avail_out:=0,next_in:=l.next,avail_in:=l.have_
        total_in:=z.total_in+(l.in_-l.have_).toUInt64
        data_type:=64}) zs {s with hold:=0,bits:=0}) := by
  unfold inflate_leave
  rw [E.strm,E.st]
  isimp [E.hz,E.hs,mode,window,last,bits,hold,ret,out,left,DONE,CHECK,BAD,TYPE,LEN_,COPY_,Z_STREAM_END,Z_OK,
    ZStreamRef.get_put_same E.hz,ZStreamRef.put_put,ZStreamRef.put_setI,setI_setI,chkI32,u2i]

#print axioms leave_done
end Zlib.Uncompr.Proof.StoredTerminalLeave
