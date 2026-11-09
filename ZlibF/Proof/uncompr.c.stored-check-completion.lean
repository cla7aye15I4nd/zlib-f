import ZlibF.Math.UncompressStoredChecksum
import ZlibF.Proof.«inflate.c.checksum-view»
import ZlibF.Proof.«inflate.c.main.check»
import ZlibF.Proof.«inflate.c.bits-complete»

namespace Zlib.Uncompr.Proof.StoredCheckCompletion
open C Zlib.Gzguts Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

private theorem held32_ready (h : Heap) (l : IL) (bits : l.bits = 32) (have_ : l.have_ = 0)
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

/-- The real CHECK suffix over an arbitrary completed stored payload runs
its actual Adler callee and reaches the actual DONE/STREAM_END exit. The
held-word premise is an internal bit-cursor fact; the caller-side producer
from the encoded trailer is a separate, still required step. -/
theorem check_done {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (l : IL) (payload : List UInt8) (small : payload.length < 65536)
    (get : h.bytes db = some payload.toArray)
    (put : l.put = .ref (.blk db) payload.length)
    (left : l.left = 0) (out : l.out_ = UInt32.ofNat payload.length)
    (bits : l.bits = 32) (have_ : l.have_ = 0) (held : l.hold.toNat < 2^32)
    (wrap : s.wrap = 5) (flags : s.flags = 0) (check : s.check = 1) (adler : z.adler = 1)
    (word : ZSWAP32 l.hold = adlerValue 1 payload) :
    runX (inflate_CHECK c) l h =
      .ok ((.error Ex.leave,{l with out_ := 0,hold := 0,bits := 0,ret := Z_STREAM_END}),
        setI (r.put h { z with
          total_out := z.total_out + (UInt32.ofNat payload.length).toUInt64
          adler := adlerValue 1 payload }) zs
          { s with
            total := s.total + (UInt32.ofNat payload.length).toUInt64
            check := adlerValue 1 payload
            mode := DONE }) := by
  have pull := held32_ready h l bits have_ held
  have nBound : payload.length < 2^32 := by omega
  have nNat : (UInt32.ofNat payload.length).toNat = payload.length := by
    rw [UInt32.toNat_ofNat',Nat.mod_eq_of_lt nBound]
  have modInt : (payload.length:Int) % 4294967296 = (payload.length:Int) :=
    Int.emod_eq_of_lt (by omega) (by omega)
  let n := UInt32.ofNat payload.length
  let h1 := setI (r.put h {z with total_out := z.total_out + n.toUInt64}) zs
    {s with total := s.total + n.toUInt64}
  have get1 : Space.get h1 (BRef.blk db) = some payload.toArray := by simpa [h1] using get
  have state1 : h1.istates zs = some {s with total := s.total + n.toUInt64} := by simp [h1]
  have ptr : l.put.add (-(n.toNat:Int)) h1 = .ok (.ref (.blk db) 0,h1) := by
    rw [put]
    change OkOn h1 ((.ref (.blk db) payload.length : BPtr).add (-(n.toNat:Int))) (.ref (.blk db) 0)
    simpa [n,nNat] using (Ptr.sub_nat_ok get1 (Nat.le_refl payload.length)
      (show payload.length ≤ payload.toArray.size by simp))
  have checksum : UPDATE_CHECK c.st 1 (.ref (.blk db) 0) n h1 = .ok (adlerValue 1 payload,h1) := by
    rw [E.st]
    have actual := UPDATE_CHECK_zlib_view state1 (by simpa using flags) get1
      (show 0+n.toNat ≤ payload.toArray.size by simp [n,nNat]) 1
    simpa [n,nNat] using actual
  by_cases empty : payload = []
  · subst payload
    have value : adlerValue 1 [] = 1 := by rfl
    unfold inflate_CHECK
    rw [E.st]
    simp [runX_bind,runX_lift,ldI_eq,E.hs,wrap,pull,E.strm,runX_modify,runX_get,
      wrZ_eq,wrI_eq,E.hz,E.st,check,flags,left,out,word,nNat,modInt,
      (show (5:Int32) &&& 4 ≠ 0 by decide),value,adler,setMode,runX_INITBITS,
      inflate_LENGTH,inflate_DONE,runX_throw,setI_setI,ZStreamRef.put_put,ZStreamRef.get_setI,ZStreamRef.get_put_same,ZStreamRef.put_setI]
  · have nNonzero : n ≠ 0 := by
      intro zero
      have length0 : payload.length = 0 := by
        have eq := congrArg UInt32.toNat zero
        change (UInt32.ofNat payload.length).toNat = 0 at eq
        rw [nNat] at eq
        exact eq
      exact empty (List.length_eq_zero_iff.mp length0)
    have ptr2 := ptr
    have checksum2 := checksum
    simp only [h1,n,E.st,wrap,flags,check,nNat] at ptr2 checksum2
    unfold inflate_CHECK
    rw [E.st]
    simp [runX_bind,runX_lift,ldI_eq,E.hs,wrap,pull,E.strm,runX_modify,runX_get,
      wrZ_eq,wrI_eq,E.hz,E.st,check,flags,left,out,word,nNat,modInt,
      (show (5:Int32) &&& 4 ≠ 0 by decide),ptr2,checksum2,nNonzero,n,setMode,runX_INITBITS,
      inflate_LENGTH,inflate_DONE,runX_throw,setI_setI,ZStreamRef.put_put,ZStreamRef.get_setI,ZStreamRef.get_put_same,ZStreamRef.put_setI]

/-- The same real checksum suffix with the independent RFC Adler value.
The physical trailer-word producer and earlier COPY path remain required. -/
theorem check_done_rfc {c : Ctx} {h : Heap} {r : ZStreamRef} {zs db : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s)
    (l : IL) (payload : List UInt8) (small : payload.length < 65536)
    (get : h.bytes db = some payload.toArray)
    (put : l.put = .ref (.blk db) payload.length)
    (left : l.left = 0) (out : l.out_ = UInt32.ofNat payload.length)
    (bits : l.bits = 32) (have_ : l.have_ = 0) (held : l.hold.toNat < 2^32)
    (wrap : s.wrap = 5) (flags : s.flags = 0) (check : s.check = 1) (adler : z.adler = 1)
    (word : ZSWAP32 l.hold = (ZlibF.Spec.adler32 payload).toUInt64) :
    runX (inflate_CHECK c) l h =
      .ok ((.error Ex.leave,{l with out_ := 0,hold := 0,bits := 0,ret := Z_STREAM_END}),
        setI (r.put h { z with
          total_out := z.total_out + (UInt32.ofNat payload.length).toUInt64
          adler := (ZlibF.Spec.adler32 payload).toUInt64 }) zs
          { s with
            total := s.total + (UInt32.ofNat payload.length).toUInt64
            check := (ZlibF.Spec.adler32 payload).toUInt64
            mode := DONE }) := by
  have word0 : ZSWAP32 l.hold = adlerValue 1 payload := by
    rw [StoredWire.initial_adler]
    exact word
  simpa only [StoredWire.initial_adler] using check_done E l payload small get put left out bits have_ held
    wrap flags check adler word0

#print axioms check_done
#print axioms check_done_rfc
end Zlib.Uncompr.Proof.StoredCheckCompletion
