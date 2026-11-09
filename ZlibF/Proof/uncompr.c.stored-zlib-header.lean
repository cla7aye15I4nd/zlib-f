import ZlibF.Proof.«uncompr.c.stored-prefix-pull»
import ZlibF.Proof.«inflate.c.header-default»

namespace Zlib.Uncompr.Proof.StoredZlibHeader
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The physical zlib header 78 01 is consumed and accepted by actual HEAD.
The suffix is arbitrary and stays readable on the same resulting heap. -/
theorem head_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (tail : List UInt8) (input : BitInv h l ([0x78,0x01]++tail))
    (bits : l.bits = 0) (hold : l.hold = 0)
    (wrap : s.wrap = 5) (header : s.head = none) (wbits : s.wbits = 15) :
    ∃ ready : IL,
      runX (inflate_HEAD c) l h =
        .ok ((.ok (),{ready with hold := 0,bits := 0,len := 15}),
          setI (r.put h {z with adler := 1}) zs
            {s with dmax := 32768,flags := 0,check := 1,mode := TYPE}) ∧
      BitInv (setI (r.put h {z with adler := 1}) zs
        {s with dmax := 32768,flags := 0,check := 1,mode := TYPE})
        {ready with hold := 0,bits := 0,len := 15} tail ∧
      ready.next = inputAdvance l.next 2 ∧
      ready = {l with next := ready.next,have_ := ready.have_,hold := ready.hold,bits := ready.bits} := by
  obtain ⟨ready,pull,packet,count,sequence,cursor,shape⟩ :=
    StoredPrefixPull.prefix_pull [0x78,0x01] tail (by decide) input bits hold
  change runX (NEEDBITS 16) l h = _ at pull
  have readyBits : ready.bits = 16 := UInt32.toNat_inj.mp count
  have held : ready.hold = 376 := by
    apply UInt64.toNat_inj.mp
    exact StoredEndian.held_bits_unique 16 _ 376 (by have b := packet.hold_lt; rw [readyBits] at b;exact b)
      (by decide) (sequence.trans (by decide))
  have accept := headDefaultCheck_accept E ready
    (by unfold headHeaderRejected;rw [wrap,held];decide)
    (by unfold headMethodRejected;rw [held];decide)
    (by unfold headWindowRegs;rw [held];dsimp only;decide) wbits
  have actual : runX (inflate_HEAD c) l h = runX (headDefaultCheck c s ready) ready h := by
    unfold inflate_HEAD
    rw [runX_bind,runX_rdS E]
    simp only [wrap,show ((5:Int32)==0)=false from rfl,Bool.false_eq_true,ite_false]
    rw [runX_bind,pull]
    simp only []
    rw [runX_bind,runX_get]
    simp only []
    rw [runX_bind,runX_ldS E]
    simp only [wrap,show (((5:Int32)&&&2)!=0)=false from rfl,Bool.false_and,
      Bool.false_eq_true,ite_false,header,show ((none:GzHeaderPtr)!=none)=false from rfl]
    unfold headDefaultCheck
    simp only [wrap,Bool.false_eq_true,ite_false]
  have result : runX (inflate_HEAD c) l h =
      .ok ((.ok (),{ready with hold := 0,bits := 0,len := 15}),
        setI (r.put h {z with adler := 1}) zs
          {s with dmax := 32768,flags := 0,check := 1,mode := TYPE}) := by
    rw [actual]
    have regsEq : headWindowRegs ready = {ready with hold := 23,bits := ready.bits-4,len := 15} := by
      unfold headWindowRegs
      rw [held]
      dsimp only
      rw [show (376:UInt64) >>> (4:UInt32).toUInt64 = 23 by decide]
      rw [show (((23:UInt64).toUInt32 &&& ((1:UInt32) <<< 4-1))+8)=15 by decide]
    have stateEq : headDefaultState s ready = {s with dmax := 32768,flags := 0,check := 1,mode := TYPE} := by
      unfold headDefaultState headDefaultMode
      rw [regsEq]
      dsimp only
      rw [show (((23:UInt64)&&&512)!=0)=false by decide]
      simp only [Bool.false_eq_true,ite_false]
      rw [show (1:UInt32) <<< 15 = 32768 by decide]
    rw [regsEq,stateEq] at accept
    exact accept
  refine ⟨ready,result,?_,cursor,shape⟩
  refine ⟨packet.have_eq,?_,?_⟩
  · rcases packet.next with empty | ⟨ref,array,off,ptr,get,room,content⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref,array,off,ptr,by simpa only [byte_view_get_setI,byte_view_get_stream_put] using get,room,content⟩
  · change (0:UInt64).toNat < 2^(0:UInt32).toNat
    decide

#print axioms head_run
end Zlib.Uncompr.Proof.StoredZlibHeader
