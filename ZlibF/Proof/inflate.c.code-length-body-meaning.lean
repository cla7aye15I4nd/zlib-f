import ZlibF.Proof.«inflate.c.code-length-after-lookup-meaning»
import ZlibF.Proof.«inflate.c.codelens-loop»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- A continuing actual CODELENS iteration on an ordinary root implements
one independent length-parser step. Actual lookup establishes its symbol;
no decoded-symbol or called-program contract is an incoming hypothesis.
This is the nonempty-table branch of the constructor's content split. -/
theorem clReadBody_parser_step {c : Ctx} {l regs : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {alphabet : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (contents : Zlib.Inftrees.Proofs.CodeLengthContents s.codes 0 s.lenbits.toNat alphabet)
    (ordinaryRoot : ∀ index, index < 2 ^ s.lenbits.toNat →
      ∃ entry, s.codes[index]? = some entry ∧ entry.op = 0)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) (B : BitInv h l bs)
    (actual : runX (clReadBody c) l h = .ok ((.ok false, regs), after)) :
    ∃ used state, used ≤ bs.length ∧ after = setI h zs state ∧ BitInv after regs (bs.drop used) ∧
      LengthParserStep alphabet (s.nlen.toNat + s.ndist.toNat) s (stream l bs) state (stream regs (bs.drop used)) := by
  obtain ⟨pointer, _table, nlen, ndist, _have, initialized⟩ := stateInv mode
  have arrayGet := CodeRef.get_istate_codes hs
  obtain ⟨result, looked, used1, lookupRun, _one, usedBound1, inv, sameStream, _shape, _bits,
    _lower, width, _kinds, enough, _empty, _next, _count⟩ :=
    lookup1_codes_run_cursor hc hs pointer arrayGet contents.safe B
  rw [clReadBody_eq, runX_bind, lookupRun] at actual
  cases result with
  | error exit => cases actual
  | ok done =>
    cases done
    change runX (do let here := (← get : IL).here; clAfterLookup c here) looked h = .ok ((.ok false, regs), after) at actual
    simp only [runX_bind, runX_get] at actual
    obtain ⟨_heap, cell, _fields⟩ := lookup1_codes_contents hc hs pointer arrayGet contents B lookupRun
    have inside : looked.hold.toNat % 2 ^ s.lenbits.toNat < 2 ^ s.lenbits.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
    obtain ⟨entry, actualCell, op⟩ := ordinaryRoot _ inside
    have sameEntry : entry = looked.here := Option.some.inj (actualCell.symm.trans (by simpa only [Nat.zero_add] using cell))
    have ordinary : looked.here.op = 0 := by rw [← sameEntry]; exact op
    obtain ⟨symbol, small, value, _length, decoded⟩ :=
      lookup1_codes_symbol hc hs pointer arrayGet contents.toCodeLengthMeaning B lookupRun ordinary
    have decodedHere : decodeSym alphabet (stream looked (bs.drop used1)) =
        some (looked.here.val.toNat, (stream looked (bs.drop used1)).drop looked.here.bits.toNat) := by
      rw [sameStream, value]
      exact decoded
    obtain ⟨used2, state, usedBound2, heapEq, outputInv, step⟩ :=
      clAfterLookup_parser_step hr hc hz hs size nlen ndist more initialized inv looked.here
        (by have := contents.safe.2.1; omega) (enough rfl) (by rw [value]; exact small) decodedHere actual
    have totalBound : used1 + used2 ≤ bs.length := by
      simp only [List.length_drop] at usedBound2
      omega
    have remainder : (bs.drop used1).drop used2 = bs.drop (used1 + used2) := by
      simp only [List.drop_drop]
    rw [remainder] at outputInv step
    rw [sameStream] at step
    exact ⟨used1 + used2, state, totalBound, heapEq, outputInv, step⟩

#print axioms clReadBody_parser_step
end Zlib.Inflate.Proofs
