import ZlibF.Proof.«inflate.c.main.table6»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

theorem readBits_three_group (input : List Bool) (enough : 3 ≤ input.length) :
    readBits 3 input = some (grp0 input, input.drop 3) := by
  cases input with
  | nil => simp at enough
  | cons a input =>
    cases input with
    | nil => simp at enough
    | cons b input =>
      cases input with
      | nil => simp at enough
      | cons d input =>
        cases a <;> cases b <;> cases d <;> rfl

theorem orderNat_format_inverse : ∀ i, i < 19 → clOrder.idxOf (orderNat i) = i := by
  unfold clOrder orderNat order
  decide +kernel

theorem format_orderNat_inverse : ∀ symbol, symbol < 19 →
    clOrder.idxOf symbol < 19 ∧ orderNat (clOrder.idxOf symbol) = symbol := by
  unfold clOrder orderNat order
  decide +kernel

theorem orderNat_injective {i j : Nat} (left : i < 19) (right : j < 19)
    (same : orderNat i = orderNat j) : i = j := by
  have inverse := congrArg (fun symbol => clOrder.idxOf symbol) same
  simpa only [orderNat_format_inverse i left, orderNat_format_inverse j right] using inverse

theorem readNats_three_groups (n : Nat) (input : List Bool) (enough : 3 * n ≤ input.length) :
    readNats 3 n input = some ((List.range n).map (grp input), input.drop (3 * n)) := by
  induction n generalizing input with
  | zero => rfl
  | succ n ih =>
    have first := readBits_three_group input (by omega)
    have rest := ih (input.drop 3) (by simp only [List.length_drop]; omega)
    rw [readNats, first]
    simp only
    rw [rest]
    simp only
    refine congrArg some (Prod.ext ?_ ?_)
    · rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
      · simp [grp]
      · apply List.map_congr_left
        intro i _
        simp only [Function.comp_apply, grp, List.drop_drop]
        rw [show 3 + 3 * i = 3 * i.succ by omega]
    · simp only [List.drop_drop]
      congr 1
      omega


theorem lensRead_order_cell {a : Array UInt16} (size : 19 ≤ a.size) (input : List Bool)
    (n i : Nat) (index : i < 19) : n ≤ 19 →
    (lensRead a 0 input n).getD (orderNat i) 0 =
      if i < n then (grp input i).toUInt16 else a.getD (orderNat i) 0 := by
  induction n with
  | zero => intro _; simp [lensRead]
  | succ n ih =>
    intro bound
    have inside : orderNat n < (lensRead a 0 input n).size := by
      rw [lensRead_size]
      have cellBound := order_lt n (by omega)
      omega
    rw [lensRead, Zlib.Inftrees.Proofs.getD_set!]
    simp only [Nat.zero_add]
    by_cases same : n = i
    · subst i
      simp [inside]
    · have distinct : orderNat n ≠ orderNat i := fun equal => same (orderNat_injective (by omega) index equal)
      rw [if_neg (fun both => distinct both.1), ih (by omega)]
      have condition : (i < n) = (i < n + 1) := by apply propext; omega
      simp only [condition]

theorem lensZero_order_cell {a : Array UInt16} (size : 19 ≤ a.size)
    (start n i : Nat) (index : i < 19) : start + n ≤ 19 →
    (lensZero a start n).getD (orderNat i) 0 =
      if start ≤ i ∧ i < start + n then 0 else a.getD (orderNat i) 0 := by
  induction n with
  | zero =>
    intro _
    have outside : ¬ (start ≤ i ∧ i < start + 0) := by omega
    simp only [lensZero, ite_eq_right outside]
  | succ n ih =>
    intro bound
    have inside : orderNat (start + n) < (lensZero a start n).size := by
      rw [lensZero_size]
      have cellBound := order_lt (start + n) (by omega)
      omega
    rw [lensZero, Zlib.Inftrees.Proofs.getD_set!]
    by_cases same : start + n = i
    · subst i
      simp [inside]
    · have distinct : orderNat (start + n) ≠ orderNat i := fun equal =>
        same (orderNat_injective (by omega) index equal)
      rw [if_neg (fun both => distinct both.1), ih (by omega)]
      have condition : (start ≤ i ∧ i < start + n) = (start ≤ i ∧ i < start + (n + 1)) := by
        apply propext
        omega
      simp only [condition]

theorem code_length_header_cell {a : Array UInt16} (size : 19 ≤ a.size) (input : List Bool)
    (n i : Nat) (bound : n ≤ 19) (index : i < 19) :
    ((lensZero (lensRead a 0 input n) n (19 - n)).getD (orderNat i) 0).toNat =
      if i < n then grp input i else 0 := by
  have readSize : 19 ≤ (lensRead a 0 input n).size := by rw [lensRead_size]; exact size
  rw [lensZero_order_cell readSize n (19 - n) i index (by omega)]
  by_cases before : i < n
  · rw [if_neg (by omega), lensRead_order_cell size input n i index bound, if_pos before, if_pos before]
    have small := grp_le input i
    simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']
    omega
  · rw [if_pos (by omega), if_neg before]
    rfl


theorem code_length_header_lensOf {a : Array UInt16} (size : 19 ≤ a.size)
    (input : List Bool) (n : Nat) (bound : n ≤ 19) :
    Zlib.Inftrees.Proofs.lensOf
      (fun k => ((lensZero (lensRead a 0 input n) n (19 - n)).getD k 0).toNat) 19 =
      (List.range 19).map (fun symbol => if clOrder.idxOf symbol < n then grp input (clOrder.idxOf symbol) else 0) := by
  apply List.ext_getElem
  · simp [Zlib.Inftrees.Proofs.lensOf]
  · intro symbol inside _
    have index : symbol < 19 := by simpa [Zlib.Inftrees.Proofs.lensOf] using inside
    simp only [Zlib.Inftrees.Proofs.lensOf, List.getElem_map, List.getElem_range]
    obtain ⟨orderedBound, ordered⟩ := format_orderNat_inverse symbol index
    have observed := code_length_header_cell size input n (clOrder.idxOf symbol) bound orderedBound
    rw [ordered] at observed
    exact observed

theorem readCodeLenLens_header_array {a : Array UInt16} (size : 19 ≤ a.size)
    (input : List Bool) (n : Nat) (bound : n ≤ 19) (enough : 3 * n ≤ input.length) :
    readCodeLenLens n input = some
      (Zlib.Inftrees.Proofs.lensOf
        (fun k => ((lensZero (lensRead a 0 input n) n (19 - n)).getD k 0).toNat) 19,
       input.drop (3 * n)) := by
  rw [readCodeLenLens, readNats_three_groups n input enough]
  simp only
  rw [code_length_header_lensOf size input n bound]
  refine congrArg some (Prod.ext ?_ rfl)
  simp only
  apply List.map_congr_left
  intro symbol _
  by_cases index : clOrder.idxOf symbol < n
  · simp [index, List.getD_eq_getElem?_getD]
  · simp [index]

theorem llDone_code_length_alphabet {s : InflateState} (size : s.lens.size = 320)
    (start : s.«have» = 0) (bound : s.ncode.toNat ≤ 19) (input : List Bool)
    (enough : 3 * s.ncode.toNat ≤ input.length) :
    readCodeLenLens s.ncode.toNat input = some
      (Zlib.Inftrees.Proofs.lensOf (fun k => ((llDone s input).lens.getD k 0).toNat) 19,
       input.drop (3 * s.ncode.toNat)) := by
  have fields := llDone_lens s input bound (by rw [start]; simp)
  simp only [start, UInt32.toNat_zero, Nat.sub_zero] at fields
  rw [fields]
  exact readCodeLenLens_header_array (by omega) input s.ncode.toNat bound enough


#print axioms readBits_three_group
#print axioms orderNat_format_inverse
#print axioms format_orderNat_inverse
#print axioms orderNat_injective
#print axioms readNats_three_groups
#print axioms lensRead_order_cell
#print axioms lensZero_order_cell
#print axioms code_length_header_cell
#print axioms code_length_header_lensOf
#print axioms readCodeLenLens_header_array
#print axioms llDone_code_length_alphabet
end Zlib.Inflate.Proofs
