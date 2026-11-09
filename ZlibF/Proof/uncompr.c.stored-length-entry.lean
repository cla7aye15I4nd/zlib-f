import ZlibF.Math.InflateStoredLength
import ZlibF.Proof.«uncompr.c.stored-prefix-pull»
import ZlibF.Proof.«inflate.c.stored-views»

namespace Zlib.Uncompr.Proof.StoredLengthEntry
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec
set_option autoImplicit false
set_option maxRecDepth 100000

/-- Actual STORED aligns the five padding bits and reads the physical LEN
and NLEN bytes. It accepts their complement and enters actual COPY with
the decoded length. The equation includes the real fall-through COPY. -/
theorem stored_entry {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (E : Env c h r zs z s) (l : IL)
    (n : Nat) (small : n<65536) (tail : List UInt8)
    (input : BitInv h l ((le16 n++le16 (65535-n))++tail))
    (bits : l.bits=5) (hold : l.hold=0) (flush : c.flush=Z_NO_FLUSH) :
    ∃ ready : IL,
      runX (inflate_STORED c) l h =
        runX (inflate_COPY c) {ready with hold:=0,bits:=0}
          (setI h zs {s with length:=UInt32.ofNat n,mode:=COPY}) ∧
      BitInv (setI h zs {s with length:=UInt32.ofNat n,mode:=COPY})
        {ready with hold:=0,bits:=0} tail ∧
      ready.next=inputAdvance l.next 4 ∧
      ready={l with next:=ready.next,have_:=ready.have_,hold:=ready.hold,bits:=ready.bits} := by
  let aligned := {l with hold:=0,bits:=0}
  have byteAligned : bytebits l=aligned := by
    unfold bytebits
    rw [bits,hold]
    simp only [show (5:UInt32)&&&7=5 by decide,show (5:UInt32)-5=0 by decide,
      show (0:UInt64) >>> (5:UInt32).toUInt64=0 by decide]
    rfl
  have packet : BitInv h aligned ((le16 n++le16 (65535-n))++tail) :=
    ⟨input.have_eq,input.next,by change (0:UInt64).toNat<2^(0:UInt32).toNat;decide⟩
  obtain ⟨ready,pull,remaining,count,sequence,cursor,shape⟩ :=
    StoredPrefixPull.prefix_pull (le16 n++le16 (65535-n)) tail (by simp [le16]) packet rfl rfl
  have readyBits : ready.bits=32 := UInt32.toNat_inj.mp count
  have held : ready.hold=StoredLength.word n := by
    apply UInt64.toNat_inj.mp
    exact StoredEndian.held_bits_unique 32 _ _ (by have b:=remaining.hold_lt;rw [readyBits] at b;exact b)
      (by rw [show (StoredLength.word n).toNat=n+(65535-n)*65536 from
          UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (StoredLength.word_small n small) (by decide))]
          exact StoredLength.word_small n small)
      (sequence.trans (StoredLength.word_bits n small).symm)
  have pull32 : runX (NEEDBITS 32) (bytebits l) h=.ok ((.ok (),ready),h) := by
    rw [byteAligned]
    exact pull
  have complement : ¬ ((ready.hold &&& (0xffff:UInt64)) != ((ready.hold >>> 16) ^^^ (0xffff:UInt64)))=true := by
    rw [held,StoredLength.word_complement n small]
    simp
  have env : Env c (setI h zs {s with length:=UInt32.ofNat n,mode:=COPY_}) r zs z
      {s with length:=UInt32.ofNat n,mode:=COPY_} :=
    ⟨E.strm,E.st,by simpa using E.hz,by simp⟩
  have actual : runX (inflate_STORED c) l h =
      runX (inflate_COPY c) {ready with hold:=0,bits:=0}
        (setI h zs {s with length:=UInt32.ofNat n,mode:=COPY}) := by
    rw [inflate_STORED_ok E l ready pull32 complement]
    rw [held,StoredLength.word_length n small]
    simp only [flush,show (Z_NO_FLUSH==Z_TREES)=false from rfl,Bool.false_eq_true,ite_false]
    rw [inflate_COPY__eq env]
    simp only [setI_setI]
  refine ⟨ready,actual,⟨remaining.have_eq,?_,?_⟩,cursor,?_⟩
  · rcases remaining.next with empty | ⟨ref,array,off,ptr,get,room,content⟩
    · exact Or.inl empty
    · exact Or.inr ⟨ref,array,off,ptr,by simpa only [byte_view_get_setI] using get,room,content⟩
  · change (0:UInt64).toNat<2^(0:UInt32).toNat
    decide
  · rw [shape]

#print axioms stored_entry
end Zlib.Uncompr.Proof.StoredLengthEntry
