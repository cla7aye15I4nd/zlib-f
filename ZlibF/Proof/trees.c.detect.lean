import ZlibF.Proof.«trees.c.arrays»

/-! # The data-type hint loops are bounded reads of the actual literal tree -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees Out
set_option autoImplicit false

def dataTypeBlack (s : DeflateStatePtr) : M (Int32 × UInt64 × Option Int32) :=
  cwhile
    (fun (n, bm, r) => pure (r.isNone && decide (n.toInt ≤ 31), (n, bm, r)))
    (fun (n, bm, _) => do
      if (bm &&& 1) != 0 ∧ (← getFc (← pLtree s) n.toInt) != 0 then return (n, bm, some Z_BINARY)
      pure (← iadd n 1, bm >>> 1, none))
    (0, 0xf3ffc07f, none)

def dataTypeText (s : DeflateStatePtr) : M (Int32 × Option Int32) :=
  cwhile
    (fun (n, r) => pure (r.isNone && decide (n.toInt < LITERALS.toInt), (n, r)))
    (fun (n, _) => do
      if (← getFc (← pLtree s) n.toInt) != 0 then return (n, some Z_TEXT)
      pure (← iadd n 1, none))
    (32, none)

/-- The complete source with only its two loops named. -/
theorem detect_data_type_source (s : DeflateStatePtr) : detect_data_type s = (do
    let (_, _, r) ← dataTypeBlack s
    if let some v := r then return v
    if (← getFc (← pLtree s) 9) != 0 ∨ (← getFc (← pLtree s) 10) != 0 ∨ (← getFc (← pLtree s) 13) != 0 then
      return Z_TEXT
    let (_, r) ← dataTypeText s
    if let some v := r then return v
    return Z_BINARY) := by
  unfold detect_data_type dataTypeBlack dataTypeText
  rfl

/-- A literal-frequency read within the admitted array leaves the heap unchanged. -/
theorem data_type_read {h : Heap} {id i : Nat} {d : DeflateState}
    (state : h.dstates id = some d) (bound : i < d.dyn_ltree.size) :
    (do getFc (← pLtree (some (.tab id))) (i : Int)) h = .ok (d.dyn_ltree[i]!.fc, h) := by
  rw [bind_app, pLtree_run state]
  exact getFc_sel state .l bound

/-- The black-byte loop terminates and makes no writes. Its only possible
nonempty early result is the source's binary hint. -/
theorem data_type_black_safe {h : Heap} {id : Nat} {d : DeflateState}
    (state : h.dstates id = some d) (extent : 32 ≤ d.dyn_ltree.size) :
    ∃ n bm r, dataTypeBlack (some (.tab id)) h = .ok ((n, bm, r), h) ∧
      (r = none ∨ r = some Z_BINARY) := by
  let Inv : (Int32 × UInt64 × Option Int32) → Heap → Prop := fun (n, _, r) g =>
    g = h ∧ 0 ≤ n.toInt ∧ n.toInt ≤ 32 ∧ (r = none ∨ r = some Z_BINARY)
  let measure : (Int32 × UInt64 × Option Int32) → Nat := fun (n, _, r) =>
    if r.isNone then (32 - n.toInt).toNat else 0
  have loop : Wp (dataTypeBlack (some (.tab id))) h (fun st g => g = h ∧ (st.2.2 = none ∨ st.2.2 = some Z_BINARY)) := by
    unfold dataTypeBlack
    refine Wp.cwhile Inv measure _ ?_ ?_ ?_
    · rintro ⟨n, bm, r⟩ g invariant
      rcases invariant with ⟨equal, lower, upper, allowed⟩
      subst g
      by_cases enabled : r.isNone = true ∧ n.toInt ≤ 31
      · have empty : r = none := by simpa using enabled.1
        subst r
        have read := getFc_sel state .l (i := n.toInt.toNat) (by change _ < d.dyn_ltree.size; omega)
        have cast : (n.toInt.toNat : Int) = n.toInt := by omega
        rw [cast] at read
        simp only [Sel.ref, Sel.arr] at read
        have add := iadd_eq (a := n) (b := 1) (by change -2147483648 ≤ n.toInt + 1; omega)
          (by change n.toInt + 1 ≤ 2147483647; omega)
        have value : (Int32.ofInt (n.toInt + 1)).toInt = n.toInt + 1 := i32_ofInt_toInt (by omega) (by omega)
        by_cases hit : (bm &&& 1) != 0 ∧ d.dyn_ltree[n.toInt.toNat]!.fc != 0
        · right
          refine ⟨(n, bm, none), h, (n, bm, some Z_BINARY), h, ?_, ?_, ?_, ?_⟩
          · simp only [pure_app, Option.isNone_none, enabled.2, decide_true, Bool.true_and]
          · simp only [bind_app, pLtree_run state, read, hit, and_self, ite_true, pure_app]
          · exact ⟨rfl, lower, upper, Or.inr rfl⟩
          · dsimp only [measure]
            simp only [Option.isNone_some, Bool.false_eq_true, ite_false, Option.isNone_none, ite_true]
            omega
        · right
          refine ⟨(n, bm, none), h, (Int32.ofInt (n.toInt + 1), bm >>> 1, none), h, ?_, ?_, ?_, ?_⟩
          · simp only [pure_app, Option.isNone_none, enabled.2, decide_true, Bool.true_and]
          · simp only [bind_app, pLtree_run state, read, hit, Bool.false_eq_true, ite_false, add, pure_app, show (1 : Int32).toInt = 1 from rfl]
          · exact ⟨rfl, by rw [value]; omega, by rw [value]; omega, Or.inl rfl⟩
          · dsimp only [measure]
            simp only [Option.isNone_none, ite_true, value]
            omega
      · left
        refine ⟨(n, bm, r), h, ?_, rfl, allowed⟩
        have stopped : (r.isNone && decide (n.toInt ≤ 31)) = false := by
          cases r <;> simp_all
        simp only [pure_app, stopped]
    · exact ⟨rfl, by decide, by decide, Or.inl rfl⟩
    · change 32 < fuel
      decide +kernel
  obtain ⟨⟨n, bm, r⟩, g, run, equal, allowed⟩ := loop
  subst g
  exact ⟨n, bm, r, run, allowed⟩

/-- The printable-byte loop terminates and makes no writes. Its only
possible nonempty early result is the source's text hint. -/
theorem data_type_text_safe {h : Heap} {id : Nat} {d : DeflateState}
    (state : h.dstates id = some d) (extent : 256 ≤ d.dyn_ltree.size) :
    ∃ n r, dataTypeText (some (.tab id)) h = .ok ((n, r), h) ∧ (r = none ∨ r = some Z_TEXT) := by
  let Inv : (Int32 × Option Int32) → Heap → Prop := fun (n, r) g =>
    g = h ∧ 32 ≤ n.toInt ∧ n.toInt ≤ 256 ∧ (r = none ∨ r = some Z_TEXT)
  let measure : (Int32 × Option Int32) → Nat := fun (n, r) =>
    if r.isNone then (256 - n.toInt).toNat else 0
  have loop : Wp (dataTypeText (some (.tab id))) h (fun st g => g = h ∧ (st.2 = none ∨ st.2 = some Z_TEXT)) := by
    unfold dataTypeText
    refine Wp.cwhile Inv measure _ ?_ ?_ ?_
    · rintro ⟨n, r⟩ g invariant
      rcases invariant with ⟨equal, lower, upper, allowed⟩
      subst g
      by_cases enabled : r.isNone = true ∧ n.toInt < 256
      · have empty : r = none := by simpa using enabled.1
        subst r
        have read := getFc_sel state .l (i := n.toInt.toNat) (by change _ < d.dyn_ltree.size; omega)
        have cast : (n.toInt.toNat : Int) = n.toInt := by omega
        rw [cast] at read
        simp only [Sel.ref, Sel.arr] at read
        have add := iadd_eq (a := n) (b := 1) (by change -2147483648 ≤ n.toInt + 1; omega)
          (by change n.toInt + 1 ≤ 2147483647; omega)
        have value : (Int32.ofInt (n.toInt + 1)).toInt = n.toInt + 1 := i32_ofInt_toInt (by omega) (by omega)
        by_cases hit : d.dyn_ltree[n.toInt.toNat]!.fc != 0
        · right
          refine ⟨(n, none), h, (n, some Z_TEXT), h, ?_, ?_, ?_, ?_⟩
          · simp only [pure_app, Option.isNone_none, show LITERALS.toInt = 256 from rfl, enabled.2, decide_true, Bool.true_and]
          · simp only [bind_app, pLtree_run state, read, hit, and_self, ite_true, pure_app]
          · exact ⟨rfl, lower, upper, Or.inr rfl⟩
          · dsimp only [measure]
            simp only [Option.isNone_some, Bool.false_eq_true, ite_false, Option.isNone_none, ite_true]
            omega
        · right
          refine ⟨(n, none), h, (Int32.ofInt (n.toInt + 1), none), h, ?_, ?_, ?_, ?_⟩
          · simp only [pure_app, Option.isNone_none, show LITERALS.toInt = 256 from rfl, enabled.2, decide_true, Bool.true_and]
          · simp only [bind_app, pLtree_run state, read, hit, Bool.false_eq_true, ite_false, add, pure_app, show (1 : Int32).toInt = 1 from rfl]
          · exact ⟨rfl, by rw [value]; omega, by rw [value]; omega, Or.inl rfl⟩
          · dsimp only [measure]
            simp only [Option.isNone_none, ite_true, value]
            omega
      · left
        refine ⟨(n, r), h, ?_, rfl, allowed⟩
        have stopped : (r.isNone && decide (n.toInt < LITERALS.toInt)) = false := by
          cases r <;> simp_all [show LITERALS.toInt = 256 from rfl]
        simp only [pure_app, stopped]
    · exact ⟨rfl, by decide, by decide, Or.inl rfl⟩
    · change 224 < fuel
      decide +kernel
  obtain ⟨⟨n, r⟩, g, run, equal, allowed⟩ := loop
  subst g
  exact ⟨n, r, run, allowed⟩

/-- `local int detect_data_type(deflate_state *s)`.
Actual hint detection terminates with Z_BINARY or Z_TEXT and leaves the
entire heap unchanged. This proves safe execution and its return domain;
it does not characterize which frequency patterns receive each hint. -/
theorem detect_data_type_safe {h : Heap} {id : Nat} {d : DeflateState}
    (state : h.dstates id = some d) (extent : 256 ≤ d.dyn_ltree.size) :
    ∃ kind, detect_data_type (some (.tab id)) h = .ok (kind, h) ∧ (kind = Z_BINARY ∨ kind = Z_TEXT) := by
  obtain ⟨n, bm, result, black, casesBlack⟩ := data_type_black_safe state (by omega)
  have nine : getFc (.ref (.dstate_dyn_ltree id) 0) 9 h = .ok (d.dyn_ltree[9]!.fc, h) :=
    getFc_sel state .l (i := 9) (by change 9 < d.dyn_ltree.size; omega)
  have ten : getFc (.ref (.dstate_dyn_ltree id) 0) 10 h = .ok (d.dyn_ltree[10]!.fc, h) :=
    getFc_sel state .l (i := 10) (by change 10 < d.dyn_ltree.size; omega)
  have thirteen : getFc (.ref (.dstate_dyn_ltree id) 0) 13 h = .ok (d.dyn_ltree[13]!.fc, h) :=
    getFc_sel state .l (i := 13) (by change 13 < d.dyn_ltree.size; omega)
  rw [detect_data_type_source]
  rcases casesBlack with rfl | rfl
  · simp only [bind_app, black]
    by_cases white : d.dyn_ltree[9]!.fc != 0 ∨ d.dyn_ltree[10]!.fc != 0 ∨ d.dyn_ltree[13]!.fc != 0
    · exact ⟨Z_TEXT, by simpa only [bind_app, pLtree_run state, nine, ten, thirteen, white, ite_true, pure_app], Or.inr rfl⟩
    · obtain ⟨n2, result2, text, casesText⟩ := data_type_text_safe state extent
      rcases casesText with rfl | rfl
      · exact ⟨Z_BINARY, by simpa only [bind_app, pLtree_run state, nine, ten, thirteen, white, ite_false, text, pure_app], Or.inl rfl⟩
      · exact ⟨Z_TEXT, by simpa only [bind_app, pLtree_run state, nine, ten, thirteen, white, ite_false, text, pure_app], Or.inr rfl⟩
  · exact ⟨Z_BINARY, by simp only [bind_app, black, pure_app], Or.inl rfl⟩

end Zlib.Trees.Proofs
