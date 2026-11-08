import ZlibF.Proof.«inftrees.c.geom»
import ZlibF.Proof.«inffast.c.sig»
import ZlibF.Math.InflateLookupBits

set_option autoImplicit false

namespace ZlibF.Math.InflateDecode
open ZlibF.Spec Zlib.Inffast.Proofs

theorem reversed_bits (len value : Nat) :
    bitsOfNat (Zlib.Inftrees.Canon.rev len value) len = natToBitsMSB len value := by
  apply List.ext_getElem
  · simp [bitsOfNat, natToBitsMSB]
  · intro i hi _
    have inside : i < len := by simpa [bitsOfNat] using hi
    simp only [bitsOfNat, natToBitsMSB, List.getElem_map, List.getElem_range]
    simp only [Nat.testBit_eq_decide_div_mod_eq]
    have rev := Zlib.Inftrees.Canon.rev_bit len (len - 1 - i) value (by omega)
    simpa only [show len - 1 - (len - 1 - i) = i by omega] using
      congrArg (fun v : Nat => decide (v = 1)) rev

theorem read_total (n : Nat) (inp : List Bool) (enough : n ≤ inp.length) :
    ∃ value rest, readBits n inp = some (value, rest) ∧ value < 2 ^ n ∧
      inp = bitsOfNat value n ++ rest := by
  induction n generalizing inp with
  | zero => exact ⟨0, inp, rfl, by decide, rfl⟩
  | succ n ih =>
      cases inp with
      | nil => simp at enough
      | cons b inp =>
          obtain ⟨value, rest, run, bound, source⟩ := ih inp (by simpa using enough)
          refine ⟨(if b then 1 else 0) + 2 * value, rest, ?_, ?_, ?_⟩
          · simp [readBits, run]
          · rw [Nat.pow_succ]
            cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
          · rw [bitsOfNat_succ]
            have low : (((if b then 1 else 0) + 2 * value).testBit 0) = b := by
              rw [Nat.testBit_zero]
              cases b <;> simp
            have high : ((if b then 1 else 0) + 2 * value) / 2 = value := by
              cases b <;> simp <;> omega
            rw [low, high, List.cons_append, ← source]

/-- A prefix of a retained bit word gives its low bits, with the original
remaining sequence. This uses the ordinary reader's exact execution. -/
theorem read_prefix {value width : Nat} {suffix : List Bool} (n : Nat) (le : n ≤ width) :
    ∃ rest, readBits n (bitsOfNat value width ++ suffix) = some (value % 2 ^ n, rest) := by
  exact ⟨_, readBits_bitsOfNat n width value suffix le⟩

theorem read_drop_prefix {value width : Nat} {suffix : List Bool} (drop n : Nat)
    (dropBound : drop ≤ width) (le : n ≤ width - drop) :
    ∃ rest, readBits n ((bitsOfNat value width ++ suffix).drop drop) =
      some (value / 2 ^ drop % 2 ^ n, rest) := by
  have fit : drop ≤ (bitsOfNat value width).length := by simpa only [bitsOfNat_length] using dropBound
  rw [List.drop_append_of_le_length fit, ← bitsOfNat_drop value width drop dropBound]
  exact read_prefix n le

theorem replica_of_residue {len drop width cell word : Nat}
    (fits : len - drop ≤ width) (inside : cell < 2 ^ width)
    (residue : cell % 2 ^ (len - drop) = word / 2 ^ drop) :
    ∃ replica, replica < 2 ^ (width - (len - drop)) ∧
      word / 2 ^ drop + replica * 2 ^ (len - drop) = cell := by
  refine ⟨cell / 2 ^ (len - drop), ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      show width - (len - drop) + (len - drop) = width by omega]
    exact inside
  · have eq := Nat.mod_add_div cell (2 ^ (len - drop))
    rw [residue] at eq
    simpa only [Nat.mul_comm] using eq

theorem slice_residue {value word len drop width : Nat}
    (dropBound : drop ≤ len) (fits : len - drop ≤ width)
    (residue : value % 2 ^ len = word) :
    (value / 2 ^ drop % 2 ^ width) % 2 ^ (len - drop) = word / 2 ^ drop := by
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 fits),
    ← ZlibF.Math.InflateLookup.slice_eq,
    show drop + (len - drop) = len by omega, residue]

end ZlibF.Math.InflateDecode

namespace Zlib.Inftrees.Proofs
open C Zlib.Inftrees ZlibF.Spec Zlib.Inffast.Proofs

/-- The constructor's allocation order gives the independent canonical
word of every nonzero-length symbol, in transmission order. -/
theorem allocated_symbol_code (f : Nat → Nat) (n symbol : Nat)
    (inside : symbol < n) (positive : 1 ≤ f symbol) (bounded : f symbol ≤ 15) :
    ∃ j, j < Tc f n 15 ∧ Canon.sy (lensOf f n) j = symbol ∧
      Canon.L (lensOf f n) j = f symbol ∧
      codeOf (lensOf f n) symbol =
        bitsOfNat (Canon.H (lensOf f n) j) (f symbol) := by
  let ls := lensOf f n
  let len := f symbol
  let rank := (ls.take symbol).count len
  let j := Canon.offL ls len + rank
  have symbolInside : symbol < ls.length := by simpa [ls, lensOf_length] using inside
  have lengthGet : ls.getD symbol 0 = len := lensOf_getD f inside
  have rankBound : rank < ls.count len := Canon.count_take_lt ls symbolInside lengthGet
  have index : j < Canon.nz ls := by
    have interval : j < Canon.offL ls (len + 1) := by
      dsimp only [j]
      rw [Canon.offL_succ_pos ls (show 1 ≤ len from positive)]
      omega
    have mono := Canon.offL_mono ls (show len + 1 ≤ 16 by omega)
    rw [Canon.nz_eq]
    omega
  have selected : Canon.sy ls j = symbol := Canon.sy_sorted ls symbolInside positive bounded lengthGet
  have length : Canon.L ls j = len := by rw [Canon.L, selected, lengthGet]
  have modelIndex : j < Tc f n 15 := by simpa only [ls, nz_eq] using index
  have indexLength : lenAt f n j = len := (L_eq f n modelIndex).symm.trans length
  have offset : Canon.offL ls len = Tc f n (len - 1) := by
    have eq := offL_eq f n (len - 1)
    simpa only [show len - 1 + 1 = len by omega] using eq
  have start : codeStart ls len = 2 * Kc f n (len - 1) := by
    have eq := codeStart_lensOf f n (len - 1)
    simpa only [show len - 1 + 1 = len by omega] using eq
  have counted : ((ls.take symbol).filter (· == len)).length = rank := by
    simp only [rank, List.count_eq_countP, List.countP_eq_length_filter]
  have value : val f n j = codeStart ls len + rank := by
    rw [val, indexLength, start]
    dsimp only [j]
    rw [offset, Nat.add_sub_cancel_left]
  refine ⟨j, modelIndex, selected, length, ?_⟩
  rw [H_eq f n modelIndex, indexLength, value]
  change codeOf ls symbol = bitsOfNat (rev len (codeStart ls len + rank)) len
  rw [← canon_rev_eq, ZlibF.Math.InflateDecode.reversed_bits]
  simp only [codeOf, lengthGet, counted]


end Zlib.Inftrees.Proofs
