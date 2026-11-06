import ZlibF.Spec.InflateDecodeTableFrame

/-!
# A later table preserves queries to an unchanged earlier extent

The result concerns both successful and failed queries. In particular,
it transports leaf meaning without assuming the whole backing array is
unchanged. The actual later constructor must still establish the frame.
-/

set_option autoImplicit false

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees.Spec Zlib.Inftrees.Spec.DecodeSemantics
open Zlib.Inftrees.Spec.DecodeTableFrame ZlibF.Spec

private theorem query_value_lt {n : Nat} {inp rest : List Bool} {v : Nat}
    (hr : readBits n inp = some (v, rest)) : v < 2 ^ n := by
  induction n generalizing inp v rest with
  | zero => simp only [readBits, Option.some.injEq, Prod.mk.injEq] at hr; omega
  | succ n ih =>
    cases inp with
    | nil => cases hr
    | cons b r =>
      cases hread : readBits n r with
      | none => simp [readBits, hread] at hr
      | some vr =>
        rcases vr with ⟨v1, r1⟩
        have hv := ih hread
        simp only [readBits, hread, Option.some.injEq, Prod.mk.injEq] at hr
        rcases hr with ⟨rfl, rfl⟩
        rw [Nat.pow_succ]
        cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

private theorem link_guard {type : UInt32} (entry : Code)
    (ht : type = LENS ∨ type = DISTS)
    (hl : (if type = LENS then entry.op != 0 && (entry.op &&& 0xf0) == 0
      else (entry.op &&& 0xf0) == 0) = true) :
    (type = LENS ∧ Zlib.Inffast.Spec.LenLink entry) ∨
      (type = DISTS ∧ Zlib.Inffast.Spec.DistLink entry) := by
  have mask_bits (hm : entry.op &&& 0xf0 = 0) :
      entry.op &&& 16 = 0 ∧ entry.op &&& 64 = 0 := by
    have h16 := congrArg (fun x : UInt8 => x &&& 16) hm
    have h64 := congrArg (fun x : UInt8 => x &&& 64) hm
    rw [UInt8.and_assoc] at h16 h64
    exact ⟨h16, h64⟩
  rcases ht with rfl | rfl
  · simp only [ite_true, Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at hl
    exact Or.inl ⟨rfl, hl.1, mask_bits hl.2⟩
  · simp only [show DISTS ≠ LENS by decide, ite_false, beq_iff_eq] at hl
    exact Or.inr ⟨rfl, mask_bits hl⟩

/-- Every query is confined to the returned extent, so a later builder's
cell frame transports the exact result, including input-short failures. -/
theorem decode_table_read_preserved : Goal.decode_table_read_preserved := by
  intro type before after offset root used ht hext hcells inp
  unfold tableRead
  cases hread : readBits root inp with
  | none => simp
  | some ir =>
    rcases ir with ⟨i, rest⟩
    have hi := query_value_lt hread
    have hroot := hcells (offset + i) (by omega) (by have := hext.2.2.1; omega)
    simp only [bind, Option.bind]
    rw [hroot]
    cases hfirst : before[offset + i]? with
    | none => simp
    | some entry =>
      by_cases hl : (if type = LENS then entry.op != 0 && (entry.op &&& 0xf0) == 0
        else (entry.op &&& 0xf0) == 0) = true
      · simp only [ite_eq_left hl]
        have hentry : before.getD (offset + i) default = entry := by
          simp only [Array.getD_eq_getD_getElem?, hfirst, Option.getD_some]
        have hend := hext.2.2.2 i hi
        rw [hentry] at hend
        have hbound := hend (link_guard entry ht hl)
        cases hread2 : readBits entry.op.toNat (inp.drop entry.bits.toNat) with
        | none => simp
        | some jr =>
          rcases jr with ⟨j, rest2⟩
          have hj := query_value_lt hread2
          dsimp only
          rw [hcells (offset + entry.val.toNat + j) (by omega) (by omega)]
      · simp only [ite_eq_right hl]

end Zlib.Inftrees.Proofs
