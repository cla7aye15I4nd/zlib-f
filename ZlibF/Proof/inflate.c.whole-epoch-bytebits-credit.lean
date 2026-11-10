import ZlibF.Proof.«inflate.c.whole-epoch-trailer-finished»

namespace Zlib.Inflate.Proofs.WholeEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs
set_option autoImplicit false

/-- The actual BYTEBITS register update commits exactly the discarded
held padding, and retains the exact input bytes already pulled. -/
theorem CompletedBody.bytebits_credit
    {h : Heap} {l : IL} {bs : List UInt8} {log : DataLog} {wire : List Bool}
    (body : CompletedBody log wire) (buffer : BitInv h l bs)
    (credit : CausalInput.Credited log.input wire l.bits l.hold) :
    ∃ padding : List Bool, padding.length = l.bits.toNat % 8 ∧
      CausalInput.Credited log.input (wire ++ padding) (bytebits l).bits (bytebits l).hold ∧
      ∃ trailer : Trailer log (wire ++ padding), trailer.checksumWord = [] := by
  let padding := (natBits l.bits.toNat l.hold.toNat).take (l.bits.toNat % 8)
  have within : l.bits.toNat % 8 ≤ (natBits l.bits.toNat l.hold.toNat).length := by
    rw [natBits_length]
    exact Nat.mod_le _ _
  have padLength : padding.length = l.bits.toNat % 8 := by
    simp only [padding, List.length_take, Nat.min_eq_left within]
  obtain ⟨_nextBuffer, dropped, aligned⟩ := BYTEBITS_inv buffer
  have held : natBits (bytebits l).bits.toNat (bytebits l).hold.toNat =
      (natBits l.bits.toNat l.hold.toNat).drop (l.bits.toNat % 8) := by
    dsimp only [stream] at dropped
    rw [List.drop_append_of_le_length within] at dropped
    exact List.append_cancel_right dropped
  have split : natBits l.bits.toNat l.hold.toNat =
      padding ++ natBits (bytebits l).bits.toNat (bytebits l).hold.toNat := by
    rw [held]
    exact (List.take_append_drop _ _).symm
  have finalCredit : CausalInput.Credited log.input (wire ++ padding) (bytebits l).bits (bytebits l).hold := by
    change bytesBits log.input = (wire ++ padding) ++ natBits (bytebits l).bits.toNat (bytebits l).hold.toNat
    change bytesBits log.input = wire ++ natBits l.bits.toNat l.hold.toNat at credit
    rw [credit, split, List.append_assoc]
  have padAlign : (body.bodyWord.length + padding.length) % 8 = 0 := by
    have count := congrArg List.length finalCredit
    change (bytesBits log.input).length =
      ((wire ++ padding) ++ natBits (bytebits l).bits.toNat (bytebits l).hold.toNat).length at count
    have wireCount := congrArg List.length body.anchor
    simp only [List.length_append, bytesBits_length] at wireCount
    simp only [List.length_append, bytesBits_length, natBits_length] at count
    omega
  have short : padding.length < 8 := by
    rw [padLength]
    exact Nat.mod_lt _ (by decide)
  let trailer : Trailer log (wire ++ padding) := {
    wrapper := body.wrapper
    bodyWord := body.bodyWord
    blocks := body.blocks
    padding := padding
    shortPadding := short
    aligned := padAlign
    checksumWord := []
    checksumPrefix := ⟨bytesBits (be32 (adler32 log.output).toNat), rfl⟩
    anchor := by
      simpa only [List.append_nil] using congrArg (fun word => word ++ padding) body.anchor
  }
  exact ⟨padding, padLength, finalCredit, trailer, rfl⟩

#print axioms CompletedBody.bytebits_credit
end Zlib.Inflate.Proofs.WholeEpoch
