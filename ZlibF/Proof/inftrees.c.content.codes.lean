import ZlibF.Proof.«inftrees.c.content»
import ZlibF.Spec.InflateTableSafety

/-!
# inftrees.c: the constructed code-length table is safe to decode

The code-length alphabet uses only a root table. Complete root coverage and
the actual retained writes establish the lookup facts. The accepted empty
alphabet has the two explicit invalid cells written by the real constructor.
-/

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Canon
set_option autoImplicit false

private theorem codes_here {e : Env} (type : e.c.type = CODES) {j : Nat}
    (index : j < e.m) :
    1 ≤ (e.here j).bits.toNat ∧ (e.here j).bits.toNat ≤ e.R ∧
      (e.here j).op = 0 ∧ (e.here j).val.toNat < 19 := by
  obtain ⟨maxBound, root, countBound, matchValue⟩ := e.h_codes type
  have symbol := ws_getD_lt index
  have count : e.n ≤ 19 := countBound
  let w := (wsAux e.f e.n 15).getD j 0
  have word : (UInt16.ofNat w).toNat = w := by
    rw [UInt16.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by change w < e.n at symbol; omega)
  have widened : (UInt16.ofNat w).toUInt32.toNat = w := by
    rw [UInt16.toNat_toUInt32, word]
  have test : (UInt16.ofNat w).toUInt32 + 1 < e.c.match_ := by
    rw [matchValue]
    apply UInt32.lt_iff_toNat_lt.mpr
    rw [u32_succ (by rw [widened]; change w < e.n at symbol; omega), widened]
    change w + 1 < 20
    change w < e.n at symbol
    omega
  have jList : j < Canon.nz e.ls := by
    change j < Canon.nz (lensOf e.f e.n)
    rw [Zlib.Inftrees.Proofs.nz_eq]
    exact index
  have lengthBounds := Canon.L_interval e.ls jList
  have lengthMax : Canon.L e.ls j ≤ e.R := by
    change Canon.L (lensOf e.f e.n) j ≤ e.R
    rw [L_eq e.f e.n index, root]
    have actualIndex : j < Tc e.f e.n 15 := index
    exact lenAt_mono (f := e.f) (n := e.n) (by omega)
      (by have := e.h_pos; omega)
  have drop : (e.D j).drop = 0 := by
    change (Canon.desc e.ls e.R e.mx j).drop = 0
    rw [Canon.desc_short e.ls jList lengthMax]
    rfl
  have bits : ((Canon.L e.ls j).toUInt8).toNat = Canon.L e.ls j := by
    rw [UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have here : e.here j = ⟨0, (Canon.L e.ls j).toUInt8, UInt16.ofNat w⟩ := by
    unfold Env.here
    change hereC e.c (UInt16.ofNat w) (Canon.L e.ls j - (e.D j).drop).toUInt8 = _
    rw [drop, Nat.sub_zero]
    unfold hereC
    rw [if_pos test]
  rw [here]
  change 1 ≤ ((Canon.L e.ls j).toUInt8).toNat ∧
    ((Canon.L e.ls j).toUInt8).toNat ≤ e.R ∧ (0 : UInt8) = 0 ∧ (UInt16.ofNat w).toNat < 19
  rw [bits, word]
  change w < e.n at symbol
  exact ⟨lengthBounds.1, lengthMax, rfl, by omega⟩

theorem codes_table_of_written {e : Env} {ca : Array Code}
    (type : e.c.type = CODES) (written : Written e e.m ca) :
    CodeLengthTableSafe ca e.oc e.R := by
  obtain ⟨maxBound, root, _, _⟩ := e.h_codes type
  have complete : Kc e.f e.n 15 = 2 ^ 15 := by
    rcases e.h_end with full | ⟨_, _, notCodes⟩
    · exact full
    · exact False.elim (notCodes type)
  have entry : ∀ cell, cell < 2 ^ e.R →
      ∃ j, j < e.m ∧ ca[e.oc + cell]? = some (e.here j) := by
    intro cell inside
    have cover := Cover.root_cover_complete_fn e.h_fits complete
      (by rw [root]; exact Nat.le_trans maxBound (by decide)) inside
    rcases cover with ⟨j, short, _, _⟩ | ⟨⟨j, long⟩, _⟩
    · have shortList := (Cover.shortAt_iff e.f e.n e.R cell j).mpr short
      obtain ⟨replica, bounded, address⟩ := short_root_replica (mx := e.mx)
        shortList.1 shortList.2.1 inside shortList.2.2
      refine ⟨j, short.1, ?_⟩
      have cellValue := written j short.1 replica bounded
      change gAddr e.ls e.R e.mx j replica = cell at address
      rwa [address] at cellValue
    · have upper : lenAt e.f e.n j ≤ e.R := by
        rw [root]
        have index := long.1
        exact lenAt_mono (f := e.f) (n := e.n) (by omega)
          (by have := e.h_pos; omega)
      exact False.elim (by have := long.2.1; omega)
  have limit : e.oc + 2 ^ e.R ≤ ca.size := by
    have positive := Nat.two_pow_pos e.R
    obtain ⟨j, _, last⟩ := entry (2 ^ e.R - 1) (by omega)
    have inArray : e.oc + (2 ^ e.R - 1) < ca.size := by
      by_cases bound : e.oc + (2 ^ e.R - 1) < ca.size
      · exact bound
      · rw [Array.getElem?_eq_none (by omega)] at last
        contradiction
    omega
  refine ⟨e.h_R1, by omega, limit, ?_⟩
  intro cell inside
  obtain ⟨j, index, get⟩ := entry cell inside
  have here := codes_here type index
  have value : ca.getD (e.oc + cell) default = e.here j := by
    simp only [Array.getD_eq_getD_getElem?, get, Option.getD_some]
  dsimp only
  rw [value]
  exact ⟨here.1, here.2.1, Or.inl here.2.2⟩

/-- `int inflate_table(codetype type, unsigned short *lens, unsigned codes,
code **table, unsigned *bits, unsigned short *work)` for CODES.
On every existing constructor precondition, the actual call returns with its
original safety frame. A successful return establishes the code-length table
predicate used at CODELENS. No table predicate or callee contract is assumed. -/
theorem inflate_table_codes_decoder_safe
    {h : Heap} {rl rw : WRef} {ol ow oc : Nat} {codes bits : UInt32} {rc : CodeRef}
    (pre : CallPre h CODES rl ol codes rc oc bits rw ow) :
    ∃ result after,
      C.run (inflate_table CODES (.ref rl ol) codes (.ref rc oc) bits (.ref rw ow)) h =
        .ok (result, after) ∧
      Result h rw rc ow oc (capOf CODES) codes.toNat pre.wa pre.ca (.ref rc oc) bits result after ∧
      (result.1 = 0 → ∃ ca : Array Code, Space.get after rc = some ca ∧
        CodeLengthTableSafe ca oc result.2.2.toNat) := by
  obtain ⟨result, after, run, frame, _, content⟩ :=
    inflate_table_content h CODES rl ol codes rc oc bits rw ow pre
  refine ⟨result, after, run, frame, ?_⟩
  intro success
  rcases content success with ⟨_, root, _, ca, get, first, second⟩ |
    ⟨_, e, ca, _, _, width, reference, offset, type, get, written, _⟩
  · refine ⟨ca, get, ?_⟩
    rw [root]
    have bound : oc + 1 < ca.size := by
      by_cases inside : oc + 1 < ca.size
      · exact inside
      · rw [Array.getElem?_eq_none (by omega)] at second
        contradiction
    refine ⟨by decide, by decide, by change oc + 2 ≤ ca.size; omega, ?_⟩
    intro cell inside
    have value : ca.getD (oc + cell) default = ⟨64, 1, 0⟩ := by
      have cases : cell = 0 ∨ cell = 1 := by change cell < 2 at inside; omega
      rcases cases with rfl | rfl
      · simpa only [Nat.add_zero, Array.getD_eq_getD_getElem?, first, Option.getD_some]
      · simp only [Array.getD_eq_getD_getElem?, second, Option.getD_some]
    dsimp only
    rw [value]
    exact ⟨by decide, by decide, Or.inr rfl⟩
  · refine ⟨ca, get, ?_⟩
    rw [← offset, ← width]
    exact codes_table_of_written type written

end Zlib.Inftrees.Proofs
