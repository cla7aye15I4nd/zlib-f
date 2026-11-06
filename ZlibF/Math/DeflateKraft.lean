import ZlibF.Proof.«trees.c.heap.gbsym»
import ZlibF.Math.DeflateCodes
import ZlibF.Proof.«inftrees.c.link»

/-! # From the compressor's exact Kraft sum to format-valid code lengths -/

namespace Zlib.Trees.Proofs.GB

/-- The decoder's count and the compressor's bounded sum count the same
symbol indices. -/
theorem decoder_count_rs (len : Nat → Nat) (N b : Nat) :
    Zlib.Inftrees.Proofs.cnt len N b = rs (fun i => if len i = b then 1 else 0) N := by
  rw [← countBefore_rs]
  unfold countBefore Zlib.Inftrees.Proofs.cnt Zlib.Inftrees.Proofs.fl
  congr 1

/-- The decoder's cumulative Kraft recurrence is the symbol-level Kraft
sum, with lengths zero and lengths beyond the current level omitted. -/
theorem decoder_kraft_rs (len : Nat → Nat) (N l : Nat) :
    Zlib.Inftrees.Proofs.Kc len N l =
      rs (fun i => if 1 ≤ len i ∧ len i ≤ l then 2 ^ (l - len i) else 0) N := by
  induction l with
  | zero =>
    rw [Zlib.Inftrees.Proofs.Kc]
    symm
    exact rs_eq_zero (fun i hi => by rw [if_neg (by omega)])
  | succ l ih =>
    rw [Zlib.Inftrees.Proofs.Kc, ih, decoder_count_rs, ← rs_mul, ← rs_add]
    apply rs_congr
    intro i hi
    by_cases he : len i = l + 1
    · rw [if_neg (by omega), if_pos he, if_pos (by omega), he, Nat.sub_self, Nat.pow_zero]
    · by_cases hb : 1 ≤ len i ∧ len i ≤ l
      · rw [if_pos hb, if_neg he, if_pos (by omega)]
        rw [show l + 1 - len i = (l - len i) + 1 by omega, Nat.pow_succ]
        omega
      · rw [if_neg hb, if_neg he, if_neg (by omega)]

/-- A prefix Kraft sum scaled to a later level is bounded by the complete
symbol sum at that level. -/
theorem decoder_kraft_scaled (len : Nat → Nat) (N l L : Nat) (hl : l ≤ L) :
    Zlib.Inftrees.Proofs.Kc len N l * 2 ^ (L - l) ≤
      rs (fun i => if len i ≠ 0 then 2 ^ (L - len i) else 0) N := by
  rw [decoder_kraft_rs, Nat.mul_comm, ← rs_mul]
  apply rs_le
  intro i hi
  by_cases hb : 1 ≤ len i ∧ len i ≤ l
  · rw [if_pos hb, if_pos (by omega), ← Nat.pow_add]
    have he : L - l + (l - len i) = L - len i := by omega
    rw [he]
    exact Nat.le_refl _
  · rw [if_neg hb, Nat.mul_zero]
    omega

/-- Scaling an exact Kraft sum retains exactness when every symbol length
fits the earlier level. -/
theorem symbol_kraft_scale (len : Nat → Nat) (N L M : Nat) (hLM : L ≤ M)
    (hlen : ∀ i < N, len i ≤ L)
    (hk : rs (fun i => if len i ≠ 0 then 2 ^ (L - len i) else 0) N = 2 ^ L) :
    rs (fun i => if len i ≠ 0 then 2 ^ (M - len i) else 0) N = 2 ^ M := by
  have hs : rs (fun i => if len i ≠ 0 then 2 ^ (M - len i) else 0) N =
      2 ^ (M - L) * rs (fun i => if len i ≠ 0 then 2 ^ (L - len i) else 0) N := by
    rw [← rs_mul]
    apply rs_congr
    intro i hi
    have hli := hlen i hi
    by_cases hz : len i = 0
    · rw [if_neg (by omega), if_neg (by omega), Nat.mul_zero]
    · rw [if_pos hz, if_pos hz, ← Nat.pow_add]
      congr 1
      omega
  rw [hs, hk, ← Nat.pow_add, show M - L + L = M by omega]

/-- Exact Kraft equality and bounded lengths imply the independent
format's Fits and Complete predicates, for any of its three code kinds. -/
theorem format_code_complete (len : Nat → Nat) (N L : Nat) (hL : L ≤ 15)
    (hlen : ∀ i < N, len i ≤ L)
    (hk : rs (fun i => if len i ≠ 0 then 2 ^ (L - len i) else 0) N = 2 ^ L) :
    ∀ kind : ZlibF.Spec.CodeKind, ZlibF.Spec.Acceptable kind (Zlib.Inftrees.Proofs.lensOf len N) := by
  have h15 : ∀ i < N, len i ≤ 15 := fun i hi => Nat.le_trans (hlen i hi) hL
  have hk15 := symbol_kraft_scale len N L 15 hL hlen hk
  have hfit : Zlib.Inftrees.Proofs.Fits len N := by
    intro l hl1 hl15
    have hs := decoder_kraft_scaled len N l 15 hl15
    rw [hk15] at hs
    have hpow : 2 ^ 15 = 2 ^ l * 2 ^ (15 - l) := by
      rw [← Nat.pow_add, show l + (15 - l) = 15 by omega]
    rw [hpow] at hs
    exact Nat.le_of_mul_le_mul_right hs (Nat.two_pow_pos _)
  have hfull : Zlib.Inftrees.Proofs.Kc len N 15 = 2 ^ 15 := by
    rw [decoder_kraft_rs, ← hk15]
    apply rs_congr
    intro i hi
    have hv := h15 i hi
    by_cases hz : len i = 0
    · rw [if_neg (by omega), if_neg (by omega)]
    · rw [if_pos (by omega), if_pos hz]
  intro kind
  refine ⟨?_, (Zlib.Inftrees.Proofs.fits_iff len N).mpr hfit,
    Or.inl ((Zlib.Inftrees.Proofs.complete_iff len N).mpr hfull)⟩
  intro x hx
  simp only [Zlib.Inftrees.Proofs.lensOf, List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact h15 i (List.mem_range.mp hi)


/-- Rank within the earlier symbols is the format's rank in the length
list prefix. Symbol order is unchanged by the representation conversion. -/
theorem canonical_rank_format (len : Nat → Nat) (N v l : Nat) (hv : v ≤ N) :
    Zlib.Trees.Math.countBefore len l v =
      (((Zlib.Inftrees.Proofs.lensOf len N).take v).filter (· == l)).length := by
  unfold Zlib.Trees.Math.countBefore Zlib.Inftrees.Proofs.lensOf
  rw [← List.map_take, List.take_range, Nat.min_eq_left hv, List.filter_map, List.length_map]
  rfl

/-- Actual count values with a zero length-zero count induce the independent
format's starting-code recurrence. -/
theorem canonical_start_format (len bl : Nat → Nat) (N : Nat) (h0 : bl 0 = 0)
    (hc : ∀ b, 1 ≤ b → b < 16 → bl b = ZlibF.Spec.count (Zlib.Inftrees.Proofs.lensOf len N) b) :
    ∀ b, b ≤ 15 → Zlib.Trees.Math.nextCode bl b = ZlibF.Spec.codeStart (Zlib.Inftrees.Proofs.lensOf len N) b := by
  intro b
  induction b with
  | zero => intro hb; rfl
  | succ b ih =>
    intro hb
    rw [Zlib.Trees.Math.nextCode, ZlibF.Spec.codeStart, ih (by omega)]
    by_cases hb0 : b = 0
    · subst b
      rw [h0, if_pos rfl]
    · rw [if_neg hb0, hc b (by omega) (by omega)]

/-- Exact stored-code bits coincide with the independent format code for
that symbol. This establishes meaning of the bits, separately from Fits. -/
theorem stored_bits_format (len bl : Nat → Nat) (N v : Nat) (hv : v < N) (hl : len v ≤ 15)
    (h0 : bl 0 = 0)
    (hc : ∀ b, 1 ≤ b → b < 16 → bl b = ZlibF.Spec.count (Zlib.Inftrees.Proofs.lensOf len N) b) :
    (List.range (len v)).map (fun i => (Zlib.Trees.Math.storedCode bl len v).testBit i) =
      ZlibF.Spec.codeOf (Zlib.Inftrees.Proofs.lensOf len N) v := by
  unfold Zlib.Trees.Math.storedCode
  rw [Zlib.Trees.Math.reverseLowBits_wire]
  have hlen : (Zlib.Inftrees.Proofs.lensOf len N).getD v 0 = len v := by
    simp [Zlib.Inftrees.Proofs.lensOf, List.getD_eq_getElem?_getD, hv]
  unfold ZlibF.Spec.codeOf Zlib.Trees.Math.canonicalCode
  rw [hlen, canonical_start_format len bl N h0 hc _ hl, canonical_rank_format len N v (len v) (by omega)]
  rfl

end Zlib.Trees.Proofs.GB
