import ZlibF.Proof.«inflate.c.header-source-resume-actual»
import ZlibF.Proof.«inflate.c.whole-head-call-exhaustive»
namespace Zlib.Inflate.Proofs.DynamicRejects
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch Zlib.Inflate.Proofs.ActualHeader
open ZlibF.Math.InflateHuffmanBodyContext ZlibF.Math.HeaderConsumedReplay
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Independent rejection of a credited dynamic-header word. All future
bits remain free, including a replacement for unread caller memory. -/
def NoHeaderExtension (word : List Bool) : Prop :=
  ∀ future L D rest, ¬ Header 2 (word ++ future) L D rest

theorem invalid_counts_no_header
    {input r1 r2 rest : List Bool} {hlit hdist hclen : Nat}
    (first : readBits 5 input = some (hlit,r1)) (second : readBits 5 r1 = some (hdist,r2))
    (third : readBits 4 r2 = some (hclen,rest))
    (invalid : ¬ DynamicCountsOK hlit hdist) :
    ∃ word, input = word ++ rest ∧ NoHeaderExtension word := by
  obtain ⟨w1, source1, replay1⟩ := readBits_consumed_word first
  obtain ⟨w2, source2, replay2⟩ := readBits_consumed_word second
  obtain ⟨w3, source3, replay3⟩ := readBits_consumed_word third
  refine ⟨w1++w2++w3, ?_, ?_⟩
  · rw [source1,source2,source3]; simp only [List.append_assoc]
  · intro future L D final header
    cases header with
    | dynamic a b d counts _ _ _ _ _ _ =>
      rw [List.append_assoc, List.append_assoc, replay1] at a
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj a)
      rw [replay2] at b
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj b)
      exact invalid counts

structure CountBadSource (c : Ctx) (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream)
    (s : InflateState) (l pulled : IL) (bs : List UInt8) (used : Nat) where
  message : Nat
  word : List Bool
  actual : runX (inflate_TABLE c) l h = .ok ((.ok (), tableRegs pulled),
    tcBadHeap h r zs z (tableCounts s pulled.hold) message)
  source : natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used) =
    word ++ natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat
  rejected : NoHeaderExtension word

/-- Actual count overflow supplies the real BAD run and a fixed consumed
word that forbids a valid Header before every possible unread suffix. -/
theorem actual_count_rejection
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l pulled : IL} {bs : List UInt8} {used : Nat}
    (E : Env c h r zs z s) (B : BitInv h l bs)
    (pull : runX (NEEDBITS 14) l h = .ok ((.ok (),pulled),h))
    (bound : used ≤ bs.length) (bits : BitInv h pulled (bs.drop used))
    (same : stream pulled (bs.drop used) = stream l bs)
    (invalid : (tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) :
    Nonempty (CountBadSource c h r zs z s l pulled bs used) := by
  obtain ⟨outcome0,pulled0,used0,pull0,bound0,B0,_source0,_wait0,full0⟩ := inflate_TABLE_run E.strm E.st E.hz E.hs B
  rw [pull] at pull0
  cases pull0
  have sameUsed : used0=used := by
    have a:=B0.have_eq; have b:=bits.have_eq
    simp only [List.length_drop] at a b
    omega
  subst used0
  obtain ⟨enough,_afterBits,_drop,actual,_accepted⟩ := full0 rfl
  obtain ⟨i,_literal,run⟩ := actual invalid
  obtain ⟨hlit,hdist,hclen,r1,r2,first,second,third,lit,dist,_code⟩ := tableCounts_read_fields s bits enough
  have forbidden : ¬DynamicCountsOK hlit hdist := by
    intro counts
    change hlit+257≤286 ∧ hdist+1≤30 at counts
    rcases invalid with invalid | invalid
    · have bad := UInt32.lt_iff_toNat_lt.mp invalid
      rw [lit] at bad
      change 286 < hlit+257 at bad
      omega
    · have bad := UInt32.lt_iff_toNat_lt.mp invalid
      rw [dist] at bad
      change 30 < hdist+1 at bad
      omega
  obtain ⟨word,wordSource,noHeader⟩ := invalid_counts_no_header first second third forbidden
  refine ⟨⟨i,word,run,?_,noHeader⟩⟩
  apply (List.append_left_inj (bytesBits (bs.drop used))).mp
  have split : bytesBits bs = bytesBits (bs.take used) ++ bytesBits (bs.drop used) := by
    rw [←bytesBits_append,List.take_append_drop]
  have combined := same.symm.trans wordSource
  simpa only [stream,split,List.append_assoc] using combined

#print axioms invalid_counts_no_header
#print axioms actual_count_rejection
end Zlib.Inflate.Proofs.DynamicRejects
