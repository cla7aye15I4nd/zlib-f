import ZlibF.Math.DeflatePayload
import ZlibF.Math.DeflateStaticBudget

/-! # Exact symbol histograms count the payload writer's bits

This adapts the reference CostBody argument to the current Symbol ledger,
finite-sum API and payload bit model. It says nothing about a translated
call until that call's original frequencies and actual returned words are
supplied by execution theorems.
-/

namespace ZlibF.Math.DeflateCosts
open C Zlib.Trees
open Zlib.Trees.Proofs.Out
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem symbol_payload_cost (lt dt : Nat → UInt16 × UInt16) (s : Symbol) (valid : s.Valid) :
    (lt (s.literalKey lcodeN)).2.toNat +
      (if s.literalKey lcodeN < 257 then 0 else extra_lbits_tab[s.literalKey lcodeN - 257]!.toInt.toNat) +
      (match s.distanceKey dcodeN with
      | none => 0
      | some v => (dt v).2.toNat + extra_dbits_tab[v]!.toInt.toNat) =
      (payloadSymBits lt dt (s.distance, s.value)).length := by
  by_cases literal : s.distance = 0
  · have small : s.value < 257 := by have := valid.2; omega
    simp only [Symbol.literalKey, literal, ite_true, Symbol.distanceKey, small,
      Nat.add_zero, payloadSymBits, codeBits, natBits_length]
  · have matchKey : ¬ (lcodeN s.value + 257 < 257) := by omega
    simp only [Symbol.literalKey, literal, ite_false, Symbol.distanceKey, matchKey,
      Nat.add_sub_cancel, payloadSymBits, List.length_append, codeBits, natBits_length]
    exact (Nat.add_assoc _ _ _).symm

/-- Original exact frequencies and the actual encoder words give precisely
the payload and END_BLOCK bit length. Forced zero-original-frequency leaves
make no contribution. Word values do not affect their encoded lengths. -/
theorem histogram_payload_cost (literal distance : Nat → Nat)
    (lt dt : Nat → UInt16 × UInt16) (xs : List Symbol)
    (valid : ∀ s ∈ xs, s.Valid)
    (literalKeys : ∀ s ∈ xs, s.literalKey lcodeN < 286)
    (distanceKeys : ∀ s ∈ xs, ∀ v, s.distanceKey dcodeN = some v → v < 30)
    (literalFrequencyExact : ∀ v, v < 286 → literal v = literalFrequency lcodeN xs v)
    (distanceFrequencyExact : ∀ v, v < 30 → distance v = distanceFrequency dcodeN xs v) :
    mass (fun v => literal v * ((lt v).2.toNat + if v < 257 then 0 else extra_lbits_tab[v - 257]!.toInt.toNat)) 286 +
      mass (fun v => distance v * ((dt v).2.toNat + extra_dbits_tab[v]!.toInt.toNat)) 30 =
      (xs.flatMap (fun s => payloadSymBits lt dt (s.distance, s.value)) ++ codeBits lt 256).length := by
  let literalCost := fun v => (lt v).2.toNat + if v < 257 then 0 else extra_lbits_tab[v - 257]!.toInt.toNat
  let distanceCost := fun v => (dt v).2.toNat + extra_dbits_tab[v]!.toInt.toNat
  let symbolDistance := fun s : Symbol => match s.distanceKey dcodeN with
    | none => 0
    | some v => distanceCost v
  have lit : mass (fun v => literal v * literalCost v) 286 =
      (lt 256).2.toNat + (xs.map (fun s => literalCost (s.literalKey lcodeN))).sum := by
    rw [mass_congr (fun v fit => by rw [literalFrequencyExact v fit]),
      literal_frequency_cost lcodeN xs literalCost 286 (by decide +kernel) literalKeys]
    rfl
  have dist : mass (fun v => distance v * distanceCost v) 30 = (xs.map symbolDistance).sum := by
    rw [mass_congr (fun v fit => by rw [distanceFrequencyExact v fit])]
    exact weighted_optional_key (Symbol.distanceKey dcodeN) 30 distanceCost distanceKeys
  have payload : (xs.map (fun s => literalCost (s.literalKey lcodeN))).sum +
      (xs.map symbolDistance).sum = (xs.flatMap (fun s => payloadSymBits lt dt (s.distance, s.value))).length := by
    clear literalFrequencyExact distanceFrequencyExact lit dist literalKeys distanceKeys
    induction xs with
    | nil => rfl
    | cons s xs ih =>
      have head := symbol_payload_cost lt dt s (valid s (by simp))
      have tail := ih (fun t member => valid t (by simp [member]))
      change literalCost (s.literalKey lcodeN) + symbolDistance s = _ at head
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append]
      rw [← head, ← tail]
      ac_rfl
  change mass (fun v => literal v * literalCost v) 286 + mass (fun v => distance v * distanceCost v) 30 = _
  rw [lit, dist, List.length_append]
  simp only [codeBits, natBits_length]
  rw [← payload]
  ac_rfl

end ZlibF.Math.DeflateCosts
