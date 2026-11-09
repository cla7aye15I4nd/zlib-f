import ZlibF.Proof.«uncompr.c.stored-prefix-pull»
import ZlibF.Proof.«inflate.c.main.type»
import ZlibF.Proof.«inflate.c.byte-views»

namespace Zlib.Uncompr.Proof.StoredTag
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs
set_option autoImplicit false
set_option maxRecDepth 100000

private theorem tag_need {h : Heap} {l : IL} (tail : List UInt8)
    (input : BitInv h l (1::tail)) (bits : l.bits=0) (hold : l.hold=0) :
    ∃ ready,runX (NEEDBITS 3) l h = .ok ((.ok (),ready),h) ∧
      BitInv h ready tail ∧ ready.bits=8 ∧ ready.hold=1 ∧
      ready.next=inputAdvance l.next 1 ∧
      ready={l with next:=ready.next,have_:=ready.have_,hold:=ready.hold,bits:=ready.bits} := by
  obtain ⟨result,ready,used,actual,bound,packet,sequence,count,shape,maxBits,_noPull,
      enough,leave,kinds,cursor⟩ := NEEDBITS_run_cursor input 3 (by decide)
  have countBits : ready.bits.toNat=8*used := by simpa only [bits,UInt32.toNat_zero,Nat.zero_add] using count
  have ok : result=.ok () := kinds.resolve_right (by
    intro bad
    obtain ⟨all,_empty,short⟩ := leave bad
    change ready.bits.toNat<3 at short
    rw [countBits,all,List.length_cons] at short
    omega)
  have pulledOne : used=1 := by
    have lower := enough ok
    change 3≤ready.bits.toNat at lower
    rw [countBits] at lower
    rw [bits] at maxBits
    change ready.bits.toNat≤max 0 10 at maxBits
    rw [countBits] at maxBits
    omega
  have readyBits : ready.bits=8 := UInt32.toNat_inj.mp (by change ready.bits.toNat=8;rw [countBits,pulledOne])
  have dropped : (1::tail).drop used=tail := by rw [pulledOne];rfl
  have held : ready.hold=1 := by
    have value : natBits 8 ready.hold.toNat = natBits 8 1 := by
      unfold stream at sequence
      rw [dropped,bits,hold,readyBits] at sequence
      change natBits 8 ready.hold.toNat ++ bytesBits tail = natBits 8 1 ++ bytesBits tail at sequence
      exact List.append_cancel_right sequence
    apply UInt64.toNat_inj.mp
    exact StoredEndian.held_bits_unique 8 _ 1 (by have b:=packet.hold_lt;rw [readyBits] at b;exact b)
      (by decide) value
  exact ⟨ready,by simpa only [ok] using actual,by simpa only [dropped] using packet,
    readyBits,held,by simpa only [pulledOne] using cursor,shape⟩

/-- Actual TYPE reads the final stored-block tag byte 01 and selects STORED.
Its five padding bits are still held; the physical suffix remains readable. -/
theorem type_run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (tail : List UInt8) (input : BitInv h l (1::tail))
    (bits : l.bits=0) (hold : l.hold=0) (last : s.last=0) (flush : c.flush=Z_NO_FLUSH) :
    ∃ ready : IL,
      runX (inflate_TYPE c) l h = .ok ((.ok (),{ready with hold:=0,bits:=5}),
        setI h zs {s with last:=1,mode:=STORED}) ∧
      BitInv (setI h zs {s with last:=1,mode:=STORED}) {ready with hold:=0,bits:=5} tail ∧
      ready.next=inputAdvance l.next 1 ∧
      ready={l with next:=ready.next,have_:=ready.have_,hold:=ready.hold,bits:=ready.bits} := by
  obtain ⟨ready,pull,packet,readyBits,held,cursor,shape⟩ := tag_need tail input bits hold
  let state := {s with last:=1}
  have env : Env c (setI h zs state) r zs z state :=
    ⟨E.strm,E.st,by simpa using E.hz,by simp⟩
  have tailRun := typedoTail_stored env {ready with hold:=0,bits:=7} (by change (0:UInt64).toNat%4=0;decide)
  have actual : runX (inflate_TYPE c) l h = .ok ((.ok (),{ready with hold:=0,bits:=5}),
      setI h zs {s with last:=1,mode:=STORED}) := by
    rw [inflate_TYPE_go c l h (by simp [flush,Z_NO_FLUSH,Z_BLOCK,Z_TREES]),inflate_TYPEDO_head E l ready last pull]
    rw [held,readyBits]
    have lastBit : u2i ((1:UInt64).toUInt32 &&& ((1:UInt32) <<< 1-1))=1 := by decide
    rw [lastBit]
    change runX (typedoTail c) {ready with hold:=0,bits:=7} (setI h zs state)=_
    simpa only [setI_setI,show (0:UInt64) >>> 2=0 by decide,show (7:UInt32)-2=5 by decide] using tailRun
  refine ⟨ready,actual,⟨packet.have_eq,?_,?_⟩,cursor,shape⟩
  · rcases packet.next with empty | ⟨ref,array,off,ptr,get,room,content⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref,array,off,ptr,by simpa only [byte_view_get_setI] using get,room,content⟩
  · change (0:UInt64).toNat<2^(5:UInt32).toNat
    decide

#print axioms type_run
end Zlib.Uncompr.Proof.StoredTag
