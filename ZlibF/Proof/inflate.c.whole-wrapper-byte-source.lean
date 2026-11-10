import ZlibF.Proof.«inflate.c.whole-epoch-call-cut»
import ZlibF.Proof.«inflate.c.functional-trailer-wire»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WholeEpoch Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false
set_option maxHeartbeats 1800000

/-- Exact source observation for the real wrapper word pull. Already
credited words remain fixed and only newly pulled bytes enter held bits. -/
structure ByteWordRead (h : Heap) (l : IL) (bs input : List UInt8) (committed : List Bool) (width : UInt32) where
  outcome : Except Ex Unit
  regs : IL
  used : Nat
  actual : runX (NEEDBITS width) l h = .ok ((outcome, regs), h)
  bound : used ≤ bs.length
  inv : BitInv h regs (bs.drop used)
  cursor : regs.next = inputAdvance l.next used
  shape : TcRegShape l regs
  heldSource : natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used) = natBits regs.bits.toNat regs.hold.toNat
  credited : CausalInput.Credited (input ++ bs.take used) committed regs.bits regs.hold
  kinds : outcome = .ok () ∨ outcome = .error Ex.leave
  normal : outcome = .ok () → regs.bits.toNat = width.toNat
  wait : outcome = .error Ex.leave → used = bs.length ∧ regs.have_ = 0 ∧ regs.bits.toNat < width.toNat

/-- The finite 16/32-bit wrapper reader is source-produced on arbitrary
current buffers, including cumulative prior partial reads. -/
theorem byte_word_read
    {h : Heap} {l : IL} {bs input : List UInt8} {committed : List Bool} {width : UInt32}
    (B : BitInv h l bs) (before : CausalInput.Credited input committed l.bits l.hold)
    (wordAligned : committed.length % 8 = 0)
    (widthBound : width.toNat ≤ 32) (widthAligned : width.toNat % 8 = 0)
    (short : l.bits.toNat < width.toNat) :
    Nonempty (ByteWordRead h l bs input committed width) := by
  obtain ⟨outcome, regs, used, actual, bound, inv, source, count, shape, upper, _identity, normal, waiting, kinds, cursor⟩ :=
    NEEDBITS_run_cursor B width (by omega)
  have heldSource : natBits l.bits.toNat l.hold.toNat ++ bytesBits (bs.take used) = natBits regs.bits.toNat regs.hold.toNat := by
    apply (List.append_left_inj (bytesBits (bs.drop used))).mp
    have split : bytesBits bs = bytesBits (bs.take used) ++ bytesBits (bs.drop used) := by rw [← bytesBits_append, List.take_append_drop]
    simpa only [stream, split, List.append_assoc] using source.symm
  have credit := before.append (word := []) (by simpa only [List.nil_append] using heldSource)
  have lengths := congrArg List.length before
  change (bytesBits input).length = (committed ++ natBits l.bits.toNat l.hold.toNat).length at lengths
  simp only [bytesBits_length, List.length_append, natBits_length] at lengths
  have aligned : l.bits.toNat % 8 = 0 := by omega
  have regAligned : regs.bits.toNat % 8 = 0 := by omega
  refine ⟨⟨outcome, regs, used, actual, bound, inv, cursor, shape, heldSource, ?_, kinds, ?_, waiting⟩⟩
  · simpa only [List.append_nil] using credit
  · intro accepted
    have full := normal accepted
    omega

/-- Bit-level byte encoding is injective. This is used only to identify
actual cumulative wrapper bytes from the independently recorded word. -/
theorem bytes_bits_injective {first second : List UInt8} (same : bytesBits first = bytesBits second) : first = second := by
  induction first generalizing second with
  | nil =>
    have lengths := congrArg List.length same
    simp only [bytesBits_length, List.length_nil] at lengths
    have empty : second = [] := List.length_eq_zero_iff.mp (by omega)
    exact empty.symm
  | cons byte rest ih =>
    cases second with
    | nil =>
      have lengths := congrArg List.length same
      simp only [bytesBits_length, List.length_cons, List.length_nil] at lengths
      omega
    | cons other tail =>
      have left := wrapper_readBits_byte byte (bytesBits rest)
      have right := wrapper_readBits_byte other (bytesBits tail)
      change readBits 8 (bytesBits (byte :: rest)) = some (byte.toNat, bytesBits rest) at left
      change readBits 8 (bytesBits (other :: tail)) = some (other.toNat, bytesBits tail) at right
      rw [same] at left
      obtain ⟨byteEq, tailEq⟩ := Prod.mk.inj (Option.some.inj (left.symm.trans right))
      have byteSame : byte = other := UInt8.toNat_inj.mp byteEq
      subst other
      exact congrArg (List.cons byte) (ih tailEq)

#print axioms byte_word_read
#print axioms bytes_bits_injective
end Zlib.Inflate.Proofs.WholeWrapper
