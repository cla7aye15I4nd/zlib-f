import ZlibF.Proof.«inflate.c.codelens-step»
import ZlibF.Proof.«inflate.c.code-length-query-meaning»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inftrees.Proofs (lensOf)
set_option autoImplicit false

/-- A literal store appends exactly its decoded length to the initialized
length prefix. The old header alphabet is not read from the overwritten lens. -/
theorem clWrite_lens_prefix {s : InflateState} {value : UInt16}
    (bound : s.«have».toNat < 320) (inside : s.«have».toNat < s.lens.size) :
    lensOf (fun k => ((clWrite s value).lens.getD k 0).toNat) (clWrite s value).«have».toNat =
      lensOf (fun k => (s.lens.getD k 0).toNat) s.«have».toNat ++ [value.toNat] := by
  have count : (clWrite s value).«have».toNat = s.«have».toNat + 1 := by
    change (s.«have» + 1).toNat = _
    rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)]
  rw [count, lensOf, List.range_succ, List.map_append, List.map_singleton]
  have stored : ((clWrite s value).lens.getD s.«have».toNat 0).toNat = value.toNat := by
    simp [clWrite, inside]
  rw [stored]
  congr 1
  apply List.map_congr_left
  intro k member
  have smaller : k < s.«have».toNat := List.mem_range.mp member
  change ((s.lens.set! s.«have».toNat value).getD k 0).toNat = (s.lens.getD k 0).toNat
  rw [Zlib.Inftrees.Proofs.getD_set!, ite_eq_right (by omega)]

/-- A literal iteration of the actual CODELENS reader stores precisely the
independently decoded length, preserving the exact remaining input stream. -/
theorem clReadBody_literal_symbol {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {alphabet : List Nat}
    {l lookup : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Proofs.CodeLengthMeaning ca offset s.lenbits.toNat alphabet)
    (size : s.lens.size = 320) (inside : s.«have».toNat < 320)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs)
    (actualLookup : runX (lookup1 c false) l h = .ok ((.ok (), lookup), h))
    (ordinary : lookup.here.op = 0) (literal : lookup.here.val.toNat < 16) :
    ∃ used, used ≤ 1 ∧ used ≤ bs.length ∧
      let final := { lookup with hold := lookup.hold >>> lookup.here.bits.toUInt32.toUInt64, bits := lookup.bits - lookup.here.bits.toUInt32 }
      runX (clReadBody c) l h = .ok ((.ok false, final), setI h zs (clWrite s lookup.here.val)) ∧
      BitInv (setI h zs (clWrite s lookup.here.val)) final (bs.drop used) ∧
      stream final (bs.drop used) = (stream l bs).drop lookup.here.bits.toNat ∧
      decodeSym alphabet (stream l bs) = some (lookup.here.val.toNat, stream final (bs.drop used)) ∧
      lensOf (fun k => ((clWrite s lookup.here.val).lens.getD k 0).toNat)
          (clWrite s lookup.here.val).«have».toNat =
        lensOf (fun k => (s.lens.getD k 0).toNat) s.«have».toNat ++ [lookup.here.val.toNat] := by
  obtain ⟨result, regs, used, run, one, usedBound, inv, sameStream, _shape,
    _bits, _lower, upper, _kinds, enough, _empty, _cursor, _count⟩ :=
    lookup1_codes_run_cursor hc hs pointer get meaning.safe B
  rw [actualLookup] at run
  cases run
  have width : lookup.here.bits.toNat ≤ 7 := by have := meaning.safe.2.1; omega
  obtain ⟨afterRun, afterInv, afterStream, _count, _initialized⟩ :=
    clAfterLookup_literal_run hc hs size inside literal width (enough rfl) inv initialized
  obtain ⟨symbol, _small, value, _width, decoded⟩ :=
    lookup1_codes_symbol hc hs pointer get meaning B actualLookup ordinary
  refine ⟨used, one, usedBound, ?_, afterInv, ?_, ?_, clWrite_lens_prefix inside (by omega)⟩
  · rw [clReadBody_eq, runX_bind, actualLookup]
    simp only [runX_bind, runX_get]
    exact afterRun
  · rw [afterStream, sameStream]
  · rw [afterStream, sameStream]
    rw [value]
    exact decoded

#print axioms clReadBody_literal_symbol
#print axioms clWrite_lens_prefix
end Zlib.Inflate.Proofs
