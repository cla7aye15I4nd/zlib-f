import ZlibF.Proof.«uncompr.c.stored-returned-call»
import ZlibF.Proof.«uncompr.c.local-loop-iteration»

namespace Zlib.Uncompr.Proof.StoredReturnedCallerLoop
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec ZlibF.Spec.Public
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers
set_option autoImplicit false
set_option maxRecDepth 100000

private theorem chunk_nat (n : Nat) (small : n<4294967295) :
    chunk (UInt64.ofNat n)=UInt32.ofNat n ∧ (chunk (UInt64.ofNat n)).toUInt64=UInt64.ofNat n := by
  have n64 : (UInt64.ofNat n).toNat=n := UInt64.toNat_ofNat_of_lt' (by change n<18446744073709551616;omega)
  have n32 : (UInt32.ofNat n).toNat=n := UInt32.toNat_ofNat_of_lt' (by change n<4294967296;omega)
  have value : (chunk (UInt64.ofNat n)).toNat=n := by rw [chunk_toNat,n64];omega
  exact ⟨UInt32.toNat_inj.mp (value.trans n32.symm),UInt64.toNat_inj.mp (by rw [UInt32.toNat_toUInt64,value,n64])⟩

/-- The real utility loop refills its empty public buffers with the entire
single stored wire, invokes actual public inflate and stops after that
one iteration with END. The remaining outer chunk counters are exactly
zero. This theorem executes cdoWhile, not an abstract codec scheduler. -/
theorem loop_end_fields {h : Heap} {cutoff b zs sb db : Nat} {z : ZStream} {s : InflateState}
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (payload : List UInt8) (small : payload.length<65536)
    (sourcePtr : z.next_in=.ref (.blk sb) 0) (source : h.bytes sb=some (StoredWire.wire payload).toArray)
    (inputRange : CallerRange h (.tab b) z.next_in (StoredWire.wire payload).length false)
    (outputRange : CallerRange h (.tab b) z.next_out payload.length true)
    (mode : s.mode=HEAD) (last : s.last=0) (wrap : s.wrap=5) (header : s.head=none)
    (wbits : s.wbits=15) (window : s.wsize=0) (bits : s.bits=0) (hold : s.hold=0)
    (emptyIn : z.avail_in=0) (emptyOut : z.avail_out=0) (put : z.next_out=.ref (.blk db) 0)
    (output : Array UInt8) (get : h.bytes db=some output) (size : output.size=payload.length)
    (write : h.ro db=false)
    (separate : Separate z.next_in (StoredWire.wire payload).length z.next_out payload.length) :
    ∃after returned,
      C.run (cdoWhile (loopBody (some (.tab b))) loopCondition
        {err:=Z_OK,len:=UInt64.ofNat (StoredWire.wire payload).length,left:=UInt64.ofNat payload.length}) h=
        .ok ({err:=Z_STREAM_END,len:=0,left:=0},after) ∧ after.bytes db=some payload.toArray ∧ after.streams b=some returned ∧ returned.avail_in=0 ∧ returned.avail_out=0 := by
  let l : UncLoop := {err:=Z_OK,len:=UInt64.ofNat (StoredWire.wire payload).length,left:=UInt64.ofNat payload.length}
  have wireSmall : (StoredWire.wire payload).length<4294967295 := by
    simp only [StoredWire.wire,List.length_append,List.length_cons,List.length_nil,le16,be32]
    omega
  have inputChunk := chunk_nat (StoredWire.wire payload).length wireSmall
  have outputChunk := chunk_nat payload.length (by omega)
  have counts : refilledLocals z l={err:=Z_OK,len:=0,left:=0} := by
    unfold refilledLocals
    simp only [emptyIn,emptyOut,beq_self_eq_true,ite_true,l,inputChunk.2,outputChunk.2,UInt64.sub_self]
  have inCount : (refilledStream z l).avail_in=UInt32.ofNat (StoredWire.wire payload).length := by
    simpa only [refilledStream,emptyIn,beq_self_eq_true,ite_true,l] using inputChunk.1
  have outCount : (refilledStream z l).avail_out=UInt32.ofNat payload.length := by
    simpa only [refilledStream,emptyOut,beq_self_eq_true,ite_true,l] using outputChunk.1
  have filled := LocalLoop.refilledLocalStateJ h cutoff b zs z l s invariant
  have ranges := refilled_stream_buffers h b z l invariant.good.live.hz
    (by simpa only [l,emptyIn,UInt32.toNat_zero,Nat.add_zero,
      UInt64.toNat_ofNat_of_lt' (by change (StoredWire.wire payload).length<18446744073709551616;omega)] using inputRange)
    (by simpa only [l,emptyOut,UInt32.toNat_zero,Nat.add_zero,
      UInt64.toNat_ofNat_of_lt' (by change payload.length<18446744073709551616;omega)] using outputRange)
    (by simpa only [l,emptyIn,emptyOut,UInt32.toNat_zero,Nat.add_zero,
      UInt64.toNat_ofNat_of_lt' (by change payload.length<18446744073709551616;omega),
      UInt64.toNat_ofNat_of_lt' (by change (StoredWire.wire payload).length<18446744073709551616;omega)] using separate)
  have sepFilled : Separate (refilledStream z l).next_in (refilledStream z l).avail_in.toNat
      (refilledStream z l).next_out (refilledStream z l).avail_out.toNat := by
    rw [inCount,outCount,UInt32.toNat_ofNat_of_lt' (by change (StoredWire.wire payload).length<4294967296;omega),
      UInt32.toNat_ofNat_of_lt' (by change payload.length<4294967296;omega)]
    exact separate
  obtain ⟨after,returned,inflateRun,payloadGet,returnedGet,inZero,outZero⟩ := StoredReturnedCall.inflate_stored_end_fields filled allocator ranges payload small
    sourcePtr source inCount mode last wrap header wbits window bits hold outCount put output get size write sepFilled
  have body : C.run (loopBody (some (.tab b)) l) h=.ok ({err:=Z_STREAM_END,len:=0,left:=0},after) := by
    have actual := loopBody_run h b z l invariant.good.live.hz
    change inflate (some (.tab b)) Z_NO_FLUSH (refilledHeap h b z l)=.ok (Z_STREAM_END,after) at inflateRun
    simp only [refilledHeap] at inflateRun
    rw [inflateRun,counts] at actual
    exact actual
  have loop : C.run (cdoWhile (loopBody (some (.tab b))) loopCondition l) h=
      .ok ({err:=Z_STREAM_END,len:=0,left:=0},after) := by
    change cdoWhile.go (loopBody (some (.tab b))) loopCondition fuel l h=_
    have fuelSucc : fuel=(fuel-1)+1 := by decide
    rw [fuelSucc,cdoWhile.go]
    have raw : loopBody (some (.tab b)) l h=.ok ({err:=Z_STREAM_END,len:=0,left:=0},after) := body
    simp only [bind_app,raw]
    rfl

  exact ⟨after,returned,loop,payloadGet,returnedGet,inZero,outZero⟩

#print axioms loop_end_fields
end Zlib.Uncompr.Proof.StoredReturnedCallerLoop
