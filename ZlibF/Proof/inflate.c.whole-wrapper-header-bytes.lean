import ZlibF.Proof.«inflate.c.whole-wrapper-header-guards»
namespace Zlib.Inflate.Proofs.WholeWrapper
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inflate.Proofs.WrapperGlue
set_option autoImplicit false
set_option maxHeartbeats 1800000

private theorem list_two_bytes {bytes : List UInt8} (size : bytes.length = 2) :
    ∃ cmf flg, bytes = [cmf, flg] := by
  cases bytes with
  | nil => simp at size
  | cons cmf tail =>
    cases tail with
    | nil => simp at size
    | cons flg tail =>
      have empty : tail = [] := List.length_eq_zero_iff.mp (by simpa using size)
      subst tail
      exact ⟨cmf, flg, rfl⟩

/-- Identify the actual two accumulated bytes, whether supplied in one
call or assembled across several partial HEAD reads. -/
theorem actual_header_bytes
    {h : Heap} {l : IL} {bs input : List UInt8}
    (event : ByteWordRead h l bs input [] 16) (normal : event.outcome = .ok ()) :
    ∃ cmf flg, input ++ bs.take event.used = [cmf, flg] ∧
      event.regs.hold.toNat = cmf.toNat + 256 * flg.toNat ∧
      natBits event.regs.bits.toNat event.regs.hold.toNat = bytesBits [cmf, flg] := by
  have width : event.regs.bits.toNat = 16 := event.normal normal
  have credited := event.credited
  change bytesBits (input ++ bs.take event.used) = [] ++ natBits event.regs.bits.toNat event.regs.hold.toNat at credited
  simp only [List.nil_append] at credited
  have lengths := congrArg List.length credited
  simp only [bytesBits_length, natBits_length, width] at lengths
  obtain ⟨cmf, flg, bytes⟩ := list_two_bytes (by omega : (input ++ bs.take event.used).length = 2)
  rw [bytes] at credited
  have holdBound : event.regs.hold.toNat < 65536 := by
    have bound := event.inv.hold_lt
    simpa only [width, Nat.reducePow] using bound
  have first := wrapper_readBits_byte cmf (bytesBits [flg])
  have second := wrapper_readBits_byte flg []
  have joined := wrapper_readBits_join first second
  have byteRead : readBits 16 (bytesBits [cmf, flg]) = some (cmf.toNat + 256 * flg.toNat, []) := by
    simpa only [bytesBits_cons, bytesBits_nil, List.append_nil, Nat.reducePow, Nat.reduceAdd] using joined
  have heldRead := readBits_held_stream event.regs [] 16 (by omega)
  have dropped : (stream event.regs []).drop 16 = [] := by
    simp only [stream, bytesBits_nil, List.append_nil, width]
    exact List.drop_eq_nil_of_le (by rw [natBits_length]; omega)
  rw [dropped] at heldRead
  simp only [stream, bytesBits_nil, List.append_nil] at heldRead
  rw [← credited] at heldRead
  have value := congrArg Prod.fst (Option.some.inj (heldRead.symm.trans byteRead))
  change event.regs.hold.toNat % 65536 = cmf.toNat + 256 * flg.toNat at value
  rw [Nat.mod_eq_of_lt holdBound] at value
  exact ⟨cmf, flg, bytes, value, credited.symm⟩

#print axioms actual_header_bytes
end Zlib.Inflate.Proofs.WholeWrapper
