import ZlibF.Proof.«deflate.c.engine.overlay-gain»
import ZlibF.Proof.«deflate.c.engine.static-budget-data»

/-!
# deflate.c: the dynamic choice per code (`TinyOverlay`, memLevel 1, R2)

`choice_gain` truncates the gain symbol by symbol. The memLevel 1 certificate needs the choice
untruncated and split by code: in the dynamic branch,

  `H + Σ_v fl v · ll v + Σ_v fd v · dl v + 1 ≤ Σ_v fl v · sl v + 5 · Σ_v fd v`,

where `ll`, `dl` are the dynamic code lengths, `sl` the fixed literal/length code lengths (5 for
every distance code), and `fl`, `fd` the actual frequencies (end of block included). The extra
bits are the same in both branches and cancel.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (blPrepare curL dynamicHeaderBits fixedLiteralWords fixedDistanceWords)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflatePush (symbolCost)
open ZlibF.Math.DeflateSelection (byteCost)
set_option autoImplicit false

/-- The literal/length cost of key `v` with lengths `len`: the length plus the extra bits of a
length code. -/
def keyCost (len : Nat → Nat) (v : Nat) : Nat := len v + if v < 257 then 0 else sourceLiteralExtra (v - 257)

/-- The distance cost of a symbol with lengths `len`: none for a literal. -/
def distKeyCost (len : Nat → Nat) (s : Symbol) : Nat :=
  match s.distanceKey dcodeN with
  | none => 0
  | some k => len k + sourceDistanceExtra k

theorem distKeyCost_sum (len : Nat → Nat) (xs : List Symbol)
    (keys : ∀ s ∈ xs, ∀ k, s.distanceKey dcodeN = some k → k < 30) :
    mass (fun k => countKey (Symbol.distanceKey dcodeN) xs k * (len k + sourceDistanceExtra k)) 30 =
      (xs.map (distKeyCost len)).sum := by
  rw [weighted_optional_key (Symbol.distanceKey dcodeN) 30 (fun k => len k + sourceDistanceExtra k) keys]
  congr 1

set_option maxRecDepth 10000 in
theorem fixed_distance_five : ∀ c : Fin 30, (fixedDistanceWords c.val).2.toNat = 5 := by decide +kernel

theorem fixed_end_seven : (fixedLiteralWords 256).2.toNat = 7 := by decide +kernel

/-- A symbol's dynamic cost is its literal/length key cost plus its distance cost. -/
theorem symbolCost_split (ll dl : Nat → Nat) (s : Symbol) (valid : s.Valid) :
    symbolCost ll dl sourceLiteralExtra sourceDistanceExtra symbolLengthCode dcodeN s =
      keyCost ll (s.literalKey symbolLengthCode) + distKeyCost dl s := by
  have v := valid.2
  by_cases z : s.distance = 0
  · simp [symbolCost, keyCost, distKeyCost, Symbol.literalKey, Symbol.distanceKey, z, show s.value < 257 by omega]
  · simp only [symbolCost, keyCost, distKeyCost, Symbol.literalKey, Symbol.distanceKey, z, if_false,
      show ¬ (symbolLengthCode s.value + 257 < 257) by omega, Nat.add_sub_cancel]
    omega

/-- A symbol's fixed cost is its fixed key cost plus 5 and the extra bits of its distance. -/
theorem staticCost_split (s : Symbol) (valid : s.Valid) :
    staticLiteralCost (s.literalKey symbolLengthCode) + staticDistanceSymbolCost s =
      keyCost (fun v => (fixedLiteralWords v).2.toNat) (s.literalKey symbolLengthCode) +
        distKeyCost (fun _ => 5) s := by
  have dist := fixed_distance_five
  cases hk : s.distanceKey dcodeN with
  | none => simp [staticLiteralCost, keyCost, staticDistanceSymbolCost, distKeyCost, hk]
  | some k =>
    have small := valid_distance_key valid hk
    simp [staticLiteralCost, keyCost, staticDistanceSymbolCost, distKeyCost, hk, staticDistanceCost, dist ⟨k, small⟩]

/-- **The choice row**: in the dynamic branch, from a cleared block entry. -/
theorem choice_row {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready))
    (header : (dynamicHeaderBits ready mb).length ≤ 2283)
    (excess : 1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 6257 * (xs.length + 3))
    (dynamic : ¬ (byteCost ready.static_len ≤ byteCost ready.opt_len ∨ (ready.strategy == Z_FIXED) = true)) :
    (dynamicHeaderBits ready mb).length +
        mass (fun v => literalFrequency symbolLengthCode xs v * curL ready.dyn_ltree v) 286 +
        mass (fun v => distanceFrequency dcodeN xs v * curL ready.dyn_dtree v) 30 + 1 ≤
      mass (fun v => literalFrequency symbolLengthCode xs v * (fixedLiteralWords v).2.toNat) 286 +
        5 * mass (distanceFrequency dcodeN xs) 30 := by
  have hopt := dynamic_opt_len trees ledger clear run
  have hstat := dynamic_static_len trees ledger clear run
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have low := trees.base.lit_lo
    omega
  have litMax := UInt32.toNat_lt d.lit_bufsize
  have eobMax : curL ready.dyn_ltree 256 < 2 ^ 16 := by unfold curL; exact UInt16.toNat_lt _
  have prefixAll := Zlib.Trees.Overlay.prefix_bits_le (dynamicSymbolCosts ready xs)
    (dynamicSymbolCosts ready xs).length
  rw [List.take_length] at prefixAll
  have costLength : (dynamicSymbolCosts ready xs).length = xs.length := by
    simp only [dynamicSymbolCosts, List.length_map]
  have bits := choice_bits hopt (by omega)
    (by rw [hstat, UInt64.toNat_ofNat']; exact Nat.mod_le _ _) (fun le => dynamic (Or.inl le))
  -- the dynamic and the fixed sums by key
  have keysL : ∀ s ∈ xs, s.literalKey symbolLengthCode < 286 := fun s m => valid_literal_key (ledger.valid s m)
  have keysD : ∀ s ∈ xs, ∀ k, s.distanceKey dcodeN = some k → k < 30 :=
    fun s m k sel => valid_distance_key (ledger.valid s m) sel
  have dynSum : (dynamicSymbolCosts ready xs).sum =
      (xs.map (fun s => keyCost (curL ready.dyn_ltree) (s.literalKey symbolLengthCode))).sum +
        (xs.map (distKeyCost (curL ready.dyn_dtree))).sum := by
    unfold dynamicSymbolCosts
    rw [← sum_map_add]
    congr 1
    apply List.map_congr_left
    intro s m
    exact symbolCost_split (curL ready.dyn_ltree) (curL ready.dyn_dtree) s (ledger.valid s m)
  have statSum : (xs.map (fun s => staticLiteralCost (s.literalKey symbolLengthCode))).sum +
      (xs.map staticDistanceSymbolCost).sum =
      (xs.map (fun s => keyCost (fun v => (fixedLiteralWords v).2.toNat) (s.literalKey symbolLengthCode))).sum +
        (xs.map (distKeyCost (fun _ => 5))).sum := by
    rw [← sum_map_add, ← sum_map_add]
    congr 1
    apply List.map_congr_left
    intro s m
    exact staticCost_split s (ledger.valid s m)
  have litDyn := literal_frequency_cost symbolLengthCode xs (keyCost (curL ready.dyn_ltree)) 286 (by omega) keysL
  have litStat := literal_frequency_cost symbolLengthCode xs (keyCost (fun v => (fixedLiteralWords v).2.toNat)) 286
    (by omega) keysL
  have distDyn := distKeyCost_sum (curL ready.dyn_dtree) xs keysD
  have distStat := distKeyCost_sum (fun _ => 5) xs keysD
  -- split the key costs into lengths and extra bits
  have splitL : ∀ (len : Nat → Nat), mass (fun v => literalFrequency symbolLengthCode xs v * keyCost len v) 286 =
      mass (fun v => literalFrequency symbolLengthCode xs v * len v) 286 +
        mass (fun v => literalFrequency symbolLengthCode xs v * (if v < 257 then 0 else sourceLiteralExtra (v - 257))) 286 := by
    intro len
    rw [← mass_add]
    apply mass_congr
    intro v _
    simp only [keyCost, Nat.mul_add]
  have splitD : ∀ (len : Nat → Nat), mass (fun k => countKey (Symbol.distanceKey dcodeN) xs k * (len k + sourceDistanceExtra k)) 30 =
      mass (fun k => distanceFrequency dcodeN xs k * len k) 30 +
        mass (fun k => distanceFrequency dcodeN xs k * sourceDistanceExtra k) 30 := by
    intro len
    rw [← mass_add]
    apply mass_congr
    intro v _
    simp only [distanceFrequency, Nat.mul_add]
  have five : mass (fun k => distanceFrequency dcodeN xs k * 5) 30 = 5 * mass (distanceFrequency dcodeN xs) 30 := by
    rw [mass_mul_right, Nat.mul_comm]
  have endDyn : keyCost (curL ready.dyn_ltree) 256 = curL ready.dyn_ltree 256 := by simp [keyCost]
  have endStat : keyCost (fun v => (fixedLiteralWords v).2.toNat) 256 = 7 := by
    simp [keyCost, fixed_end_seven]
  rw [splitL] at litDyn litStat
  rw [splitD (curL ready.dyn_dtree)] at distDyn
  rw [splitD (fun _ => 5), five] at distStat
  rw [costLength] at prefixAll
  rw [dynSum] at bits
  rw [endDyn] at litDyn
  rw [endStat] at litStat
  omega

#print axioms choice_row

end Zlib.Deflate.Engine.Proofs
