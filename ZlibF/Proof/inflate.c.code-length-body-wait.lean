import ZlibF.Proof.«inflate.c.code-length-wait-meaning»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- A waiting actual reading iteration retains its full real bit stream.
Lookup and repeat setup may pull bytes, but no code/extra bits were dropped.
This applies to the actual safe table, including its exceptional cells. -/
theorem clReadBody_wait_stream {c : Ctx} {l regs : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} {exit : Ex}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (mode : s.mode = CODELENS) (stateInv : CodeLengthInvariant zs s)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) (B : BitInv h l bs)
    (actual : runX (clReadBody c) l h = .ok ((.error exit, regs), h)) :
    ∃ used, used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧ stream regs (bs.drop used) = stream l bs := by
  obtain ⟨pointer, table, nlen, ndist, _have, initialized⟩ := stateInv mode
  have arrayGet := CodeRef.get_istate_codes hs
  obtain ⟨result, looked, used1, lookupRun, _one, usedBound1, inv, sameStream, _shape, _bits,
    _lower, width, _kinds, enough, _empty, _next, _count⟩ :=
    lookup1_codes_run_cursor hc hs pointer arrayGet table B
  rw [clReadBody_eq, runX_bind, lookupRun] at actual
  cases result with
  | error fault =>
    cases actual
    exact ⟨used1, usedBound1, inv, sameStream⟩
  | ok done =>
    cases done
    change runX (do let here := (← get : IL).here; clAfterLookup c here) looked h = .ok ((.error exit, regs), h) at actual
    simp only [runX_bind, runX_get] at actual
    obtain ⟨used2, usedBound2, outputInv, source⟩ := clAfterLookup_wait_stream hr hc hz hs size nlen ndist
      more initialized inv looked.here (by have := table.2.1; omega) (enough rfl) actual
    have totalBound : used1 + used2 ≤ bs.length := by
      simp only [List.length_drop] at usedBound2
      omega
    have remainder : (bs.drop used1).drop used2 = bs.drop (used1 + used2) := by simp only [List.drop_drop]
    rw [remainder] at outputInv source
    exact ⟨used1 + used2, totalBound, outputInv, source.trans sameStream⟩

#print axioms clReadBody_wait_stream
end Zlib.Inflate.Proofs
