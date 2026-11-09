import ZlibF.Proof.«inflate.c.lookup-codes»
import ZlibF.Proof.«inftrees.c.code-length-contents»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- The actual terminating CODES lookup selects the entry indexed by its
returned held word. The general loop rule supplies this observation; the
original specialized rule still supplies its sharper one-byte bound. -/
theorem lookup1_codes_selected {c : Ctx} {h after : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l regs : IL} {bs : List UInt8}
    {result : Except Ex Unit}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (safe : Zlib.Inftrees.Spec.CodeLengthTableSafe ca offset s.lenbits.toNat)
    (B : BitInv h l bs)
    (run : runX (lookup1 c false) l h = .ok ((result, regs), after)) :
    after = h ∧ regs.here = codeLookupValue ca offset s.lenbits.toNat regs := by
  have bound : ∀ current : IL,
      ((codeLookupValue ca offset s.lenbits.toNat current).bits.toUInt32).toNat ≤ 15 := by
    intro current
    rw [UInt8.toNat_toUInt32]
    have cell := safe.2.2.2 (current.hold.toNat % 2 ^ s.lenbits.toNat)
      (Nat.mod_lt _ (Nat.two_pow_pos _))
    have root := safe.2.1
    change (codeLookupValue ca offset s.lenbits.toNat current).bits.toNat ≤ 15
    have upper : (codeLookupValue ca offset s.lenbits.toNat current).bits.toNat ≤ s.lenbits.toNat := cell.2.1
    omega
  obtain ⟨outcome, final, used, actual, _two, _used, _inv, _stream, _shape,
    _count, _bound, selected, _width, _kinds, _enough, _empty, _cursor⟩ :=
    lookupLoop_run_cursor (body := codesLookupBody c)
      (codeLookupValue ca offset s.lenbits.toNat) (fun entry => entry.bits.toUInt32)
      (fun _ => rfl) bound (fun current _ => codesLookupBody_run current hc hs pointer get safe) B
  rw [← lookup1_codes_eq] at actual
  rw [actual] at run
  cases run
  exact ⟨rfl, selected⟩

/-- Concrete fields of the entry actually read by CODELENS. The empty
alphabet remains admitted and has its exact zero value, rather than an
invented immediate rejection based on its invalid opcode. -/
theorem lookup1_codes_contents {c : Ctx} {h after : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {alphabet : List Nat}
    {l regs : IL} {bs : List UInt8} {result : Except Ex Unit}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents ca offset s.lenbits.toNat alphabet)
    (B : BitInv h l bs)
    (run : runX (lookup1 c false) l h = .ok ((result, regs), after)) :
    after = h ∧
      ca[offset + regs.hold.toNat % 2 ^ s.lenbits.toNat]? = some regs.here ∧
      ((regs.here.op = 0 ∧ regs.here.val.toNat < 19) ∨
        (regs.here.op = 64 ∧ s.lenbits.toNat = 1 ∧ regs.here.bits = 1 ∧
          regs.here.val = 0 ∧ ∀ length ∈ alphabet, length = 0)) := by
  obtain ⟨heap, selected⟩ := lookup1_codes_selected hc hs pointer get contents.safe B run
  have index : regs.hold.toNat % 2 ^ s.lenbits.toNat < 2 ^ s.lenbits.toNat :=
    Nat.mod_lt _ (Nat.two_pow_pos _)
  have inside : offset + regs.hold.toNat % 2 ^ s.lenbits.toNat < ca.size := by
    have capacity := contents.safe.2.2.1
    omega
  have cell : ca[offset + regs.hold.toNat % 2 ^ s.lenbits.toNat]? = some regs.here := by
    rw [selected, codeLookupValue, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside,
      Option.getD_some]
  refine ⟨heap, cell, ?_⟩
  have fields := (contents.safe.2.2.2 _ index).2.2
  change (codeLookupValue ca offset s.lenbits.toNat regs).op = 0 ∧
      (codeLookupValue ca offset s.lenbits.toNat regs).val.toNat < 19 ∨
      (codeLookupValue ca offset s.lenbits.toNat regs).op = 64 at fields
  rw [← selected] at fields
  rcases fields with ordinary | invalid
  · exact Or.inl ordinary
  · obtain ⟨width, bits, value, allZero⟩ := contents.invalid_cell_fields index cell invalid
    exact Or.inr ⟨invalid, width, bits, value, allZero⟩

#print axioms lookup1_codes_selected
#print axioms lookup1_codes_contents
end Zlib.Inflate.Proofs
