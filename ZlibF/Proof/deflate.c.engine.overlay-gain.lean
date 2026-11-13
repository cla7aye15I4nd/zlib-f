import ZlibF.Proof.«deflate.c.engine.overlay-costs»
import ZlibF.Proof.«trees.c.source-format»
import ZlibF.Proof.«trees.c.universal-overlay-mid»

/-!
# deflate.c: the dynamic choice bounds the header and the excess by the gain (`TinyOverlay`, half A)

`_tr_flush_block` sends a dynamic block only when `byteCost opt_len < byteCost static_len`. With the
meaning of both counters (`dynamic_opt_len`, `dynamic_static_len`) the choice gives

  `H + bitExcess ≤ 5 + G`,  where `G = Σ_i (s_i − min(d_i, 24))`.

Here `H` is the length of the dynamic header, `d_i` the dynamic cost and `s_i` the fixed cost of
symbol `i`, both with extra bits. So `G + 30 ≤ 8 * lit_bufsize` gives the order-free overlay budget
`OverlayBudget`, and `OverlayBudget` gives the overlay room `DynamicRoom`.

The facts are stated for the prepared state on any heap with the tree invariant, so they apply on
the heap with any stream record, as `DynamicOverlay` asks.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (blPrepare BLInput curL same_record_of_runs dynamicHeaderBits)
open Zlib.Trees.Proofs.Out (TreesInvAt dcodeN)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateSelection (byteCost)
open ZlibF.Math.DeflatePush (symbolCost)
open ZlibF.Math.DeflateOverlaySmall (overlay_prefix_of_budget overlay_block_of_budget)
open Zlib.Deflate.Universal.Block (DynamicRoom DynamicOverlay treesInvAt_put)
set_option autoImplicit false

/-- The fixed cost of one symbol, extra bits included. -/
def staticSymbolCost (s : Symbol) : Nat :=
  staticLiteralCost (s.literalKey symbolLengthCode) + staticDistanceSymbolCost s

/-- The dynamic cost of one symbol in the prepared state, extra bits included. -/
def dynamicSymbolCost (ready : DeflateState) (s : Symbol) : Nat :=
  symbolCost (curL ready.dyn_ltree) (curL ready.dyn_dtree) sourceLiteralExtra sourceDistanceExtra
    symbolLengthCode dcodeN s

/-- The gain of the block: `Σ_i (s_i − min(d_i, 24))`. -/
def dynamicGain (ready : DeflateState) (xs : List Symbol) : Nat :=
  (xs.map (fun s => staticSymbolCost s - min (dynamicSymbolCost ready s) 24)).sum

/-- The order-free overlay budget of a dynamic block. -/
def OverlayBudget (ready : DeflateState) (mb : Int32) (xs : List Symbol) : Prop :=
  (dynamicHeaderBits ready mb).length + Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) + 25 ≤
    8 * ready.lit_bufsize.toNat

/-- **The byte-cost comparison in bits.** If the dynamic branch is taken, the dynamic bit count is
below the fixed one. `static` may wrap; `opt` must not. -/
theorem choice_bits {opt static : UInt64} {optN statN : Nat} (hopt : opt = UInt64.ofNat optN)
    (fit : optN + 10 < 2 ^ 64) (hstat : static.toNat ≤ statN) (dynamic : ¬ byteCost static ≤ byteCost opt) :
    optN + 1 ≤ statN := by
  have lt : (byteCost opt).toNat < (byteCost static).toNat := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp dynamic)
    exact this
  have optV : opt.toNat = optN := by
    rw [hopt, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have eo : (byteCost opt).toNat = (optN + 10) / 8 := by
    unfold byteCost
    rw [UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_add, optV, Nat.shiftRight_eq_div_pow]
    have a : (optN + (3 : UInt64).toNat) % 2 ^ 64 = optN + 3 := Nat.mod_eq_of_lt (by simp; omega)
    rw [a]
    have b : (optN + 3 + (7 : UInt64).toNat) % 2 ^ 64 = optN + 10 := by
      rw [Nat.mod_eq_of_lt (by simp; omega)]; simp
    rw [b]; simp
  have es : (byteCost static).toNat ≤ (static.toNat + 10) / 8 := by
    unfold byteCost
    rw [UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_add, Nat.shiftRight_eq_div_pow]
    apply Nat.div_le_div_right
    have m1 := Nat.mod_le (static.toNat + (3 : UInt64).toNat) (2 ^ 64)
    have m2 := Nat.mod_le ((static.toNat + (3 : UInt64).toNat) % 2 ^ 64 + (7 : UInt64).toNat) (2 ^ 64)
    simp only [UInt64.reduceToNat] at m1 m2 ⊢
    omega
  omega

/-- Pointwise: `g + (f − 24) ≤ f + (g − min f 24)`, summed. -/
theorem gain_sum {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map g).sum + Zlib.Trees.Overlay.bitExcess (xs.map f) ≤
      (xs.map f).sum + (xs.map (fun x => g x - min (f x) 24)).sum := by
  induction xs with
  | nil => simp [Zlib.Trees.Overlay.bitExcess]
  | cons x rest ih =>
    simp only [Zlib.Trees.Overlay.bitExcess, List.map_cons, List.sum_cons] at ih ⊢
    have one : g x + (f x - 24) ≤ f x + (g x - min (f x) 24) := by omega
    omega

theorem sum_map_add {α : Type} (f g : α → Nat) (xs : List α) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- **The end-of-block code is used**: its dynamic length is not zero. -/
theorem dynamic_eob_length {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready)) :
    1 ≤ curL ready.dyn_ltree 256 := by
  have eobUsed : (d.dyn_ltree[256]!).fc ≠ 0 := by
    intro zero
    have freq := ledger.literal 256 (by decide)
    rw [zero] at freq
    simp only [UInt16.toNat_zero, literalFrequency, if_pos] at freq
    omega
  obtain ⟨readyP, prepare, input, treesR, _, _⟩ := Zlib.Trees.Proofs.bl_prepare trees
  replace prepare : blPrepare (some (.tab ds)) h = .ok ((), setD h ds readyP) := prepare
  replace treesR : TreesInvAt (setD h ds readyP) ds readyP pb buf := treesR
  obtain ⟨other, otherRun, format⟩ := Zlib.Trees.Proofs.bl_prepare_source_format trees eobUsed
  have sameP : other = readyP := same_record_of_runs otherRun prepare
  subst other
  obtain ⟨mb', result, finish, formatR⟩ := Zlib.Trees.Proofs.build_bl_preserves_source_format treesR input format
  change Zlib.Trees.build_bl_tree (some (.tab ds)) (setD h ds readyP) =
    .ok (mb', setD (setD h ds readyP) ds result) at finish
  rw [setD_setD] at finish
  have complete : (do
      Zlib.Trees.Proofs.blPrepare (some (.tab ds))
      Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb', setD h ds result) := by
    rw [bind_app, prepare]
    exact finish
  have eR : ready = result := same_record_of_runs run complete
  subst eR
  have eob := formatR.eob
  unfold ZlibF.Spec.HasEndOfBlock Zlib.Trees.Proofs.Out.lens at eob
  rw [List.getD_eq_getElem?_getD] at eob
  by_cases fit : 256 < ready.l_desc.max_code.toInt.toNat + 1
  · rw [List.getElem?_map, List.getElem?_range fit] at eob
    simp only [Option.map_some, Option.getD_some] at eob
    change ready.dyn_ltree[256]!.dl.toNat ≠ 0 at eob
    unfold curL
    omega
  · rw [List.getElem?_map, List.getElem?_eq_none (by simp only [List.length_range]; omega)] at eob
    simp at eob

/-- **Half A: the choice bounds the header and the excess by the gain.** In the dynamic branch,
from a cleared block entry, `H + bitExcess ≤ 5 + G`. -/
theorem choice_gain {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready))
    (header : (dynamicHeaderBits ready mb).length ≤ 2283)
    (excess : 1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 6257 * (xs.length + 3))
    (dynamic : ¬ (byteCost ready.static_len ≤ byteCost ready.opt_len ∨ (ready.strategy == Z_FIXED) = true)) :
    (dynamicHeaderBits ready mb).length + Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤
      5 + dynamicGain ready xs := by
  have hopt := dynamic_opt_len trees ledger clear run
  have hstat := dynamic_static_len trees ledger clear run
  have eob := dynamic_eob_length trees ledger run
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have low := trees.base.lit_lo
    omega
  have litMax := UInt32.toNat_lt d.lit_bufsize
  have eobMax : curL ready.dyn_ltree 256 < 2 ^ 16 := by unfold curL; exact UInt16.toNat_lt _
  have costs : dynamicSymbolCosts ready xs = xs.map (dynamicSymbolCost ready) := by
    unfold dynamicSymbolCosts dynamicSymbolCost; rfl
  have prefixAll := Zlib.Trees.Overlay.prefix_bits_le (dynamicSymbolCosts ready xs)
    (dynamicSymbolCosts ready xs).length
  rw [List.take_length] at prefixAll
  have costLength : (dynamicSymbolCosts ready xs).length = xs.length := by
    simp only [dynamicSymbolCosts, List.length_map]
  -- the bits of both branches
  have bits := choice_bits hopt (by omega)
    (by rw [hstat, UInt64.toNat_ofNat']; exact Nat.mod_le _ _) (fun le => dynamic (Or.inl le))
  have statSum : (xs.map (fun s => staticLiteralCost (s.literalKey symbolLengthCode))).sum +
      (xs.map staticDistanceSymbolCost).sum = (xs.map staticSymbolCost).sum :=
    (sum_map_add _ _ xs).symm
  have gain := gain_sum (dynamicSymbolCost ready) staticSymbolCost xs
  rw [← costs] at gain
  unfold dynamicGain
  omega

/-- **The budget from a small gain.** -/
theorem overlay_budget_of_gain {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    {xs : List Symbol} (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs)
    (clear : BlockInit.BlockClear d) {mb : Int32} {ready : DeflateState}
    (run : (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready))
    (header : (dynamicHeaderBits ready mb).length ≤ 2283)
    (excess : 1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 6257 * (xs.length + 3))
    (dynamic : ¬ (byteCost ready.static_len ≤ byteCost ready.opt_len ∨ (ready.strategy == Z_FIXED) = true))
    (small : dynamicGain ready xs + 30 ≤ 8 * ready.lit_bufsize.toNat) :
    OverlayBudget ready mb xs := by
  have bound := choice_gain trees ledger clear run header excess dynamic
  unfold OverlayBudget
  omega

/-- **The overlay room from the budget**: the last step of `dynamic_overlay_mid`, for any
prepared state with a drained entry. -/
theorem dynamic_room_of_budget {d ready : DeflateState} {mb : Int32} {xs : List Symbol}
    (frame : TreePreparationFrame d ready) (pending : d.pending = 0)
    (bits : d.bi_valid.toInt ≤ 7) (symbolsFit : xs.length + 1 ≤ d.lit_bufsize.toNat)
    (budget : OverlayBudget ready mb xs) :
    DynamicRoom ready mb xs := by
  have fields : ready.pending = d.pending ∧ ready.bi_valid = d.bi_valid ∧ ready.lit_bufsize = d.lit_bufsize := by
    rw [frame]
    exact ⟨rfl, rfl, rfl⟩
  have fitR : xs.length + 1 ≤ ready.lit_bufsize.toNat := by rw [fields.2.2]; exact symbolsFit
  have pendingZero : ready.pending.toNat = 0 := by rw [fields.1, pending]; rfl
  have bitsN : ready.bi_valid.toInt.toNat ≤ 7 := by rw [fields.2.1]; omega
  have costLength : (dynamicSymbolCosts ready xs).length = xs.length := by
    simp only [dynamicSymbolCosts, List.length_map]
  unfold OverlayBudget at budget
  have budget' : (dynamicHeaderBits ready mb).length + Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) +
      25 ≤ 8 * ready.lit_bufsize.toNat := budget
  constructor
  · intro k
    have room := overlay_prefix_of_budget ready.lit_bufsize.toNat ready.bi_valid.toInt.toNat
      (dynamicHeaderBits ready mb).length (dynamicSymbolCosts ready xs) bitsN budget' k
    omega
  · have room := overlay_block_of_budget ready.lit_bufsize.toNat ready.bi_valid.toInt.toNat
      (dynamicHeaderBits ready mb).length (dynamicSymbolCosts ready xs) bitsN budget' (by omega)
    omega

/-- **`DynamicOverlay` from the gain case**: on the heap with any stream record, a drained cleared
block entry whose every prepared state has a small gain has the overlay room. -/
theorem dynamic_overlay_of_gain {h : Heap} {r : ZStreamRef} {ds pb : Nat} {d : DeflateState}
    {buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7) (z' : ZStream)
    (small : ∀ (mb : Int32) (ready : DeflateState),
      (do blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) (r.put h z') =
        .ok (mb, setD (r.put h z') ds ready) →
      dynamicGain ready xs + 30 ≤ 8 * ready.lit_bufsize.toNat) :
    DynamicOverlay (r.put h z') ds d xs := by
  intro mb ready run frame header excess dynamic
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have low := trees.base.lit_lo
    omega
  exact dynamic_room_of_budget frame pending bits capacity
    (overlay_budget_of_gain (treesInvAt_put trees) ledger clear run header excess dynamic (small mb ready run))

#print axioms choice_gain
#print axioms dynamic_overlay_of_gain

end Zlib.Deflate.Engine.Proofs
