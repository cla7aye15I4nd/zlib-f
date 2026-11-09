import ZlibF.Proof.«inflate.c.code-length-selected»
import ZlibF.Math.InflateHeldBits

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec Zlib.Inffast.Proofs
set_option autoImplicit false

/-- A completed actual CODES lookup with an ordinary cell decodes the
independent alphabet on the original unconsumed bit stream. The held word
may be shorter than the root width; zero padding never becomes consumed input. -/
theorem lookup1_codes_symbol {c : Ctx} {h after : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {alphabet : List Nat}
    {l regs : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Proofs.CodeLengthMeaning ca offset s.lenbits.toNat alphabet)
    (B : BitInv h l bs)
    (run : runX (lookup1 c false) l h = .ok ((.ok (), regs), after))
    (ordinary : regs.here.op = 0) :
    ∃ symbol, symbol < 19 ∧ regs.here.val.toNat = symbol ∧
      regs.here.bits.toNat = alphabet.getD symbol 0 ∧
      decodeSym alphabet (stream l bs) =
        some (symbol, (stream l bs).drop regs.here.bits.toNat) := by
  obtain ⟨result, actualRegs, used, actual, _one, _bound, inv, sameStream, _shape,
    _bits, _lower, _upper, _kinds, enough, _empty, _cursor, _count⟩ :=
    lookup1_codes_run_cursor hc hs pointer get meaning.safe B
  rw [actual] at run
  cases run
  obtain ⟨_heap, selected⟩ := lookup1_codes_selected hc hs pointer get meaning.safe B actual
  have inside : offset + regs.hold.toNat % 2 ^ s.lenbits.toNat < ca.size := by
    have index := Nat.mod_lt regs.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
    have capacity := meaning.safe.2.2.1
    omega
  have cell : ca[offset + regs.hold.toNat % 2 ^ s.lenbits.toNat]? = some regs.here := by
    rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside,
      Option.getD_some]
  obtain ⟨suffix, query⟩ := ZlibF.Math.InflateHeldBits.padded_query inv.hold_lt
    (show s.lenbits.toNat ≤ 15 by have := meaning.safe.2.1; omega)
  have fitted : regs.here.bits.toNat ≤
      (bitsOfNat regs.hold.toNat regs.bits.toNat).length := by
    rw [bitsOfNat_length]
    exact enough rfl
  obtain ⟨symbol, small, value, width, decoded⟩ := meaning.sound _ _ _ _ query cell ordinary fitted
  have extended := ZlibF.Spec.Proofs.ext_acceptable meaning.acceptable _ symbol _
    (bytesBits (bs.drop used)) decoded
  have streamEq : bitsOfNat regs.hold.toNat regs.bits.toNat ++ bytesBits (bs.drop used) =
      stream l bs := by
    simpa only [stream, natBits_testBit, bitsOfNat] using sameStream
  have residual : (bitsOfNat regs.hold.toNat regs.bits.toNat).drop regs.here.bits.toNat ++
      bytesBits (bs.drop used) = (stream l bs).drop regs.here.bits.toNat := by
    rw [← streamEq, List.drop_append_of_le_length fitted]
  rw [streamEq, residual] at extended
  exact ⟨symbol, small, value, width, extended⟩

#print axioms lookup1_codes_symbol
end Zlib.Inflate.Proofs
