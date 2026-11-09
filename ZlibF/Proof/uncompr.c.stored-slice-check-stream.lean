import ZlibF.Proof.«uncompr.c.stored-slice-check»
import ZlibF.Proof.«uncompr.c.stored-trailer-pull»

namespace Zlib.Uncompr.Proof.StoredSliceCheckStream
open C Zlib.Gzguts Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public ZlibF.Spec
set_option autoImplicit false
set_option maxRecDepth 8192

private theorem need_ready {h : Heap} {l : IL} (bits : l.bits = 32) (have_ : l.have_ = 0)
    (held : l.hold.toNat < 2^32) : runX (NEEDBITS 32) l h = .ok ((.ok (),l),h) := by
  have B : BitInv h l [] := ⟨by simp [have_],Or.inl rfl,by simpa [bits] using held⟩
  obtain ⟨result,regs,used,run,_bound,_inv,_stream,_count,_shape,_max,noPull,_enough,leave,kinds⟩ :=
    NEEDBITS_run_complete B 32 (by decide)
  have same := noPull (by simp [bits])
  subst regs
  have ok : result = .ok () := kinds.resolve_right (by
    intro bad
    have impossible := (leave bad).2.2
    simp [bits] at impossible)
  simpa only [ok] using run

private theorem check_need_transport {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l ready : IL)
    (wrap : s.wrap = 5)
    (pull : runX (NEEDBITS 32) l h = .ok ((.ok (),ready),h))
    (stop : runX (NEEDBITS 32) ready h = .ok ((.ok (),ready),h)) :
    runX (inflate_CHECK c) l h = runX (inflate_CHECK c) ready h := by
  unfold inflate_CHECK
  rw [runX_bind,runX_ldS E,runX_bind,runX_ldS E]
  simp only [show (s.wrap != 0) = true by simp [wrap],ite_true]
  rw [runX_bind,pull,runX_bind,stop]

/-- Starting before any trailer byte has been pulled, real CHECK consumes
the four RFC Adler bytes, calls the actual Adler update on the completed
payload and reaches the real DONE/STREAM_END exit. The input and output
relations are physical relations on this same heap, not callee contracts. -/
theorem trailer_check_done {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (l : IL) (payload : List UInt8) (small : payload.length < 65536)
    (array : Array UInt8) (off : Nat) (get : h.bytes db=some array)
    (room : off+payload.length≤array.size)
    (slice : payload=(array.toList.drop off).take payload.length)
    (put : l.put=.ref (.blk db) (off+payload.length))
    (delta : l.out_-l.left=UInt32.ofNat payload.length)
    (input : BitInv h l (be32 (ZlibF.Spec.adler32 payload).toNat))
    (bits : l.bits = 0) (hold : l.hold = 0)
    (wrap : s.wrap = 5) (flags : s.flags = 0) (check : s.check = 1) (adler : z.adler = 1) :
    ∃ regs,
      runX (NEEDBITS 32) l h = .ok ((.ok (),regs),h) ∧
      regs.next = inputAdvance l.next 4 ∧ regs.have_ = 0 ∧
      runX (inflate_CHECK c) l h =
        .ok ((.error Ex.leave,{regs with out_ := l.left,hold := 0,bits := 0,ret := Z_STREAM_END}),
          setI (r.put h { z with
            total_out := z.total_out + (UInt32.ofNat payload.length).toUInt64
            adler := (ZlibF.Spec.adler32 payload).toUInt64 }) zs
            { s with
              total := s.total + (UInt32.ofNat payload.length).toUInt64
              check := (ZlibF.Spec.adler32 payload).toUInt64
              mode := DONE }) := by
  obtain ⟨regs,pull,bits32,have0,held,word,cursor,shape⟩ :=
    StoredTrailerPull.trailer_pull (ZlibF.Spec.adler32 payload) input bits hold
  have ptr : regs.put = l.put := by rw [shape]
  have remaining : regs.left = l.left := by rw [shape]
  have output : regs.out_ = l.out_ := by rw [shape]
  have word0 : ZSWAP32 regs.hold=adlerValue 1 payload := by
    rw [StoredWire.initial_adler]
    exact word
  have produced : regs.out_-regs.left=UInt32.ofNat payload.length := by rw [output,remaining];exact delta
  have done := StoredSliceCheck.check_slice_done E regs payload small array off get room slice (ptr.trans put)
    produced bits32 have0 held wrap flags check adler word0
  refine ⟨regs,pull,cursor,have0,?_⟩
  rw [check_need_transport E l regs wrap pull (need_ready bits32 have0 held)]
  simpa only [StoredWire.initial_adler,remaining] using done

#print axioms trailer_check_done
end Zlib.Uncompr.Proof.StoredSliceCheckStream
