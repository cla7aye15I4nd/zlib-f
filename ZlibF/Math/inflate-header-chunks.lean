import ZlibF.Math.«inflate-header-alphabet»
import ZlibF.Math.«code-length-prefix»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
set_option autoImplicit false

/-- The source-order field prefix below the actual LENLENS counter.
This view alone does not assert that arbitrary cells were initialized. -/
def headerFields (a : Array UInt16) (count : Nat) : List Nat :=
  (List.range count).map (fun i => (a.getD (orderNat i) 0).toNat)

theorem headerFields_store {a : Array UInt16} (size : 19 ≤ a.size) (n : Nat)
    (inside : n < 19) (value : UInt16) :
    headerFields (a.set! (orderNat n) value) (n + 1) = headerFields a n ++ [value.toNat] := by
  rw [headerFields, List.range_succ, List.map_append, List.map_singleton]
  congr 1
  · apply List.map_congr_left
    intro i member
    have index : i < n := List.mem_range.mp member
    have distinct : orderNat n ≠ orderNat i := by
      intro equal
      have same := orderNat_injective inside (by omega) equal
      omega
    rw [Zlib.Inftrees.Proofs.getD_set!, ite_eq_right (fun both => distinct both.1)]
  · have cellBound : orderNat n < a.size := by have small := order_lt n inside; omega
    rw [Zlib.Inftrees.Proofs.getD_set!, ite_eq_left ⟨rfl, cellBound⟩]

theorem lensRead_headerFields {a : Array UInt16} (size : 19 ≤ a.size)
    (input : List Bool) (start count : Nat) : start + count ≤ 19 →
    headerFields (lensRead a start input count) (start + count) =
      headerFields a start ++ (List.range count).map (grp input) := by
  induction count with
  | zero => intro _; simp [lensRead]
  | succ count ih =>
    intro bound
    have readSize : 19 ≤ (lensRead a start input count).size := by rw [lensRead_size]; exact size
    rw [show start + (count + 1) = start + count + 1 by omega, lensRead,
      headerFields_store readSize (start + count) (by omega), ih (by omega)]
    rw [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    have small := grp_le input count
    have value : (grp input count).toUInt16.toNat = grp input count := by
      simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']
      omega
    rw [value]

theorem headerFields_get {a : Array UInt16} {count i : Nat} (inside : i < count) :
    (headerFields a count).getD i 0 = (a.getD (orderNat i) 0).toNat := by
  simp [headerFields, List.getD_eq_getElem?_getD, inside]


/-- A successful independent fixed-width list read records exactly its
consumed bit word. No unread suffix needs to be retained by a caller. -/
theorem readNats_word {width count : Nat} {input rest : List Bool} {values : List Nat}
    (read : readNats width count input = some (values, rest)) :
    input = values.flatMap (fun value => Zlib.Inffast.Proofs.bitsOfNat value width) ++ rest := by
  induction count generalizing input values rest with
  | zero =>
    simp only [readNats] at read
    cases read
    rfl
  | succ count ih =>
    cases first : readBits width input with
    | none => simp [readNats, first] at read
    | some pair =>
      obtain ⟨value, middle⟩ := pair
      cases tail : readNats width count middle with
      | none => simp [readNats, first, tail] at read
      | some pair =>
        obtain ⟨suffix, final⟩ := pair
        simp only [readNats, first, tail] at read
        cases read
        have firstWord := (ZlibF.Math.CodeLengthPrefix.read_word first).2
        have tailWord := ih tail
        rw [firstWord, tailWord]
        simp only [List.flatMap_cons, List.append_assoc]

theorem headerFields_good3 {a : Array UInt16} {count : Nat} (good : Good3 a count) :
    ∀ value ∈ headerFields a count, value < 8 := by
  intro value member
  simp only [headerFields] at member
  obtain ⟨index, indexBound, rfl⟩ := List.mem_map.mp member
  have small := good index (List.mem_range.mp indexBound)
  omega

/-- An already-read bounded field word can be followed by any future input
that completes the remaining fields. This relation does not fix an unread buffer. -/
theorem readNats_words_append {count : Nat} {future rest : List Bool} {suffix : List Nat}
    (tail : readNats 3 count future = some (suffix, rest)) (values : List Nat) :
    (∀ value ∈ values, value < 8) →
    readNats 3 (values.length + count)
      (values.flatMap (fun value => Zlib.Inffast.Proofs.bitsOfNat value 3) ++ future) =
        some (values ++ suffix, rest) := by
  induction values with
  | nil =>
    intro _
    simpa only [List.length_nil, Nat.zero_add, List.flatMap_nil, List.nil_append] using tail
  | cons value values ih =>
    intro bounded
    have firstBound : value < 8 := bounded value (by simp)
    have tailBound : ∀ v ∈ values, v < 8 := by
      intro v member
      exact bounded v (by simp [member])
    have firstRead : readBits 3
        (Zlib.Inffast.Proofs.bitsOfNat value 3 ++
          (values.flatMap (fun v => Zlib.Inffast.Proofs.bitsOfNat v 3) ++ future)) =
        some (value, values.flatMap (fun v => Zlib.Inffast.Proofs.bitsOfNat v 3) ++ future) := by
      simpa only [Nat.mod_eq_of_lt firstBound, Nat.sub_self, Zlib.Inffast.Proofs.bitsOfNat_zero, List.nil_append] using
        Zlib.Inffast.Proofs.readBits_bitsOfNat 3 3 value
          (values.flatMap (fun v => Zlib.Inffast.Proofs.bitsOfNat v 3) ++ future) (Nat.le_refl 3)
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc]
    rw [show values.length + 1 + count = values.length + count + 1 by omega]
    simp only [readNats, firstRead, ih tailBound, List.cons_append]





/-- The prefix view has exactly the source counter's length. -/
theorem headerFields_length (a : Array UInt16) (count : Nat) :
    (headerFields a count).length = count := by simp [headerFields]

/-- Zeroing only the unused suffix retains all previously read fields. -/
theorem lensZero_headerFields {a : Array UInt16} (size : 19 ≤ a.size)
    (start count : Nat) (bound : start + count ≤ 19) :
    headerFields (lensZero a start count) start = headerFields a start := by
  unfold headerFields
  apply List.map_congr_left
  intro index member
  have inside : index < start := List.mem_range.mp member
  rw [lensZero_order_cell size start count index (by omega) bound,
    ite_eq_right (by omega)]

/-- The actual zero suffix converts the source-order prefix into the
independent format's complete nineteen-symbol alphabet. -/
theorem lensZero_alphabet_fields {a : Array UInt16} (size : 19 ≤ a.size)
    (count : Nat) (bound : count ≤ 19) :
    Zlib.Inftrees.Proofs.lensOf
      (fun k => ((lensZero a count (19 - count)).getD k 0).toNat) 19 =
      (List.range 19).map (fun symbol => if clOrder.idxOf symbol < count then
        (headerFields a count).getD (clOrder.idxOf symbol) 0 else 0) := by
  apply List.ext_getElem
  · simp [Zlib.Inftrees.Proofs.lensOf]
  · intro symbol inside _
    have symbolBound : symbol < 19 := by simpa [Zlib.Inftrees.Proofs.lensOf] using inside
    simp only [Zlib.Inftrees.Proofs.lensOf, List.getElem_map, List.getElem_range]
    obtain ⟨indexBound, orderEq⟩ := format_orderNat_inverse symbol symbolBound
    have cell := lensZero_order_cell size count (19 - count) (clOrder.idxOf symbol) indexBound (by omega)
    rw [orderEq] at cell
    by_cases before : clOrder.idxOf symbol < count
    · rw [cell, ite_eq_right (by omega), ite_eq_left before, headerFields_get before, orderEq]
    · rw [cell, ite_eq_left (by omega), ite_eq_right before]
      rfl

/-- The source prefix determines its independent alphabet for every future
suffix, including one supplied by a replacement input buffer. -/
theorem readCodeLenLens_header_fields {a : Array UInt16} (size : 19 ≤ a.size)
    (count : Nat) (bound : count ≤ 19) (good : Good3 a count) (future : List Bool) :
    readCodeLenLens count
      ((headerFields a count).flatMap (fun value => Zlib.Inffast.Proofs.bitsOfNat value 3) ++ future) =
        some (Zlib.Inftrees.Proofs.lensOf
          (fun k => ((lensZero a count (19 - count)).getD k 0).toNat) 19, future) := by
  have parsed := readNats_words_append (count := 0) (future := future)
    (rest := future) (suffix := []) rfl (headerFields a count) (headerFields_good3 good)
  simp only [headerFields_length, Nat.add_zero, List.append_nil] at parsed
  simp only [readCodeLenLens, parsed]
  rw [lensZero_alphabet_fields size count bound]

#print axioms headerFields_length
#print axioms lensZero_headerFields
#print axioms lensZero_alphabet_fields
#print axioms readCodeLenLens_header_fields

#print axioms headerFields_store
#print axioms lensRead_headerFields
#print axioms headerFields_get
#print axioms readNats_word
#print axioms headerFields_good3
#print axioms readNats_words_append
end Zlib.Inflate.Proofs
