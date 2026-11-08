import ZlibF.Proof.«deflate.c.engine.static-budget»
import ZlibF.Math.DeflateStreamBudget

/-! # Fixed-code cost measured against actual represented input bytes

The ledger is the real symbol buffer/frequency relation. The three-byte
match quality condition must still be derived over complete source loops
and histories. It is internal data, not a proposed public precondition.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs Zlib.Trees
open Zlib.Trees.Proofs (fixedLiteralWords fixedDistanceWords)
open Zlib.Trees.Proofs.Out (payloadSymBits dcodeN lcodeN codeBits natBits_length distance_payload_fields)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
/-- The translated distance-code table needs at most ten extra bits
for the distance accepted by the default short-match filter. -/
theorem near_distance_extra (d : Nat) (small : d < 4096) :
    extra_dbits_tab[dcodeN d]!.toInt.toNat ≤ 10 := by
  have table : ∀ i : Fin 288,
      extra_dbits_tab[dist_code_tab[i.val]!.toNat]!.toInt.toNat ≤ 10 := by decide +kernel
  by_cases low : d < 256
  · simpa only [dcodeN, low, ite_true] using table ⟨d, by omega⟩
  · simpa only [dcodeN, low, ite_false] using table ⟨256 + d / 128, by omega⟩

/-- Length-three and length-four fixed matches use twelve code bits
plus their actual distance extras. -/
theorem short_fixed_symbol_cost (dist lc : Nat) (nonzero : dist ≠ 0)
    (distance : dist ≤ 32768) (short : lc < 2) :
    (payloadSymBits fixedLiteralWords fixedDistanceWords (dist, lc)).length =
      12 + extra_dbits_tab[dcodeN (dist - 1)]!.toInt.toNat := by
  have dk := (distance_payload_fields (dist - 1) (by omega)).1
  have fixed := (Zlib.Trees.Proofs.fixed_distance_fits (dcodeN (dist - 1)) dk).2
  have cases : lc = 0 ∨ lc = 1 := by omega
  rcases cases with rfl | rfl <;>
    simp only [payloadSymBits, nonzero, ite_false, codeBits, natBits_length, List.length_append, fixed] <;>
    change 7 + 0 + 5 + _ = _ <;> omega

/-- A legal symbol passing the short-match quality rule has a fixed
wire cost controlled by the number of represented input bytes. -/
theorem filtered_fixed_cost (s : Symbol) (valid : s.Valid)
    (quality : s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    2 * (payloadSymBits fixedLiteralWords fixedDistanceWords (s.distance, s.value)).length ≤
      13 * s.bytes + 5 := by
  by_cases literal : s.distance = 0
  · have bound := Zlib.Trees.Proofs.fixed_literal_fits s.value valid.2
    simp only [payloadSymBits, literal, ite_true, codeBits, natBits_length, Symbol.bytes]
    omega
  · by_cases shortest : s.value = 0
    · have near := near_distance_extra (s.distance - 1) (by have := quality literal shortest; omega)
      rw [short_fixed_symbol_cost s.distance s.value literal valid.1 (by omega)]
      simp only [Symbol.bytes, literal, ite_false, shortest]
      omega
    · by_cases next : s.value = 1
      · have fields := distance_payload_fields (s.distance - 1) (by have := valid.1; omega)
        rw [short_fixed_symbol_cost s.distance s.value literal valid.1 (by omega)]
        simp only [Symbol.bytes, literal, ite_false, next]
        omega
      · have bound := Zlib.Trees.Proofs.fixed_payload_symbol_length s.distance s.value valid.1 valid.2
        simp only [Symbol.bytes, literal, ite_false]
        omega

/-- The per-symbol byte estimate sums over a complete symbol list. -/
theorem filtered_static_cost_sum (xs : List Symbol)
    (valid : ∀ s ∈ xs, s.Valid)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    2 * ((xs.map (fun s => staticLiteralCost (s.literalKey symbolLengthCode))).sum +
      (xs.map staticDistanceSymbolCost).sum) ≤ 13 * represented xs + 5 * xs.length := by
  induction xs with
  | nil => simp [represented]
  | cons s xs ih =>
    have head := filtered_fixed_cost s (valid s (by simp)) (quality s (by simp))
    rw [← static_symbol_cost s (valid s (by simp))] at head
    have tail := ih (fun t member => valid t (by simp [member]))
      (fun t member => quality t (by simp [member]))
    simp only [List.map_cons, List.sum_cons, represented, List.length_cons]
    omega

/-- The original actual frequency ledger yields the byte-sensitive
fixed-tree cost, including the seven-bit end marker. -/
theorem ledger_static_byte_budget {buf : Array UInt8} {d : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf d xs)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    2 * (mass (fun v => d.dyn_ltree[v]!.fc.toNat * staticLiteralCost v) 286 +
      mass (fun v => d.dyn_dtree[v]!.fc.toNat * staticDistanceCost v) 30) ≤
      13 * represented xs + 5 * xs.length + 14 := by
  have literal : mass (fun v => d.dyn_ltree[v]!.fc.toNat * staticLiteralCost v) 286 =
      7 + (xs.map (fun s => staticLiteralCost (s.literalKey symbolLengthCode))).sum := by
    rw [mass_congr (fun v fit => by rw [ledger.literal v fit]),
      literal_frequency_cost symbolLengthCode xs staticLiteralCost 286 (by decide +kernel)
        (fun s member => valid_literal_key (ledger.valid s member))]
    rfl
  have distance : mass (fun v => d.dyn_dtree[v]!.fc.toNat * staticDistanceCost v) 30 =
      (xs.map staticDistanceSymbolCost).sum := by
    rw [mass_congr (fun v fit => by rw [ledger.distance v fit])]
    exact weighted_optional_key (Symbol.distanceKey dcodeN) 30 staticDistanceCost
      (fun s member _ selected => valid_distance_key (ledger.valid s member) selected)
  have bound := filtered_static_cost_sum xs ledger.valid quality
  rw [literal, distance]
  omega

/-- For a large default block the fixed-code rounded cost is no more
than its represented bytes. The quality and size producers are separate
actual-history obligations, not public API restrictions. -/
theorem ledger_large_static_no_expansion {buf : Array UInt8} {d : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf d xs)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (symbols : xs.length ≤ 16383) (large : 32506 ≤ represented xs) :
    (mass (fun v => d.dyn_ltree[v]!.fc.toNat * staticLiteralCost v) 286 +
      mass (fun v => d.dyn_dtree[v]!.fc.toNat * staticDistanceCost v) 30 + 10) / 8 ≤ represented xs := by
  have bound := ledger_static_byte_budget ledger quality
  omega

/-- Cumulative byte rounding retains the large-block estimate even
when the block starts after a partial byte. -/
theorem ledger_large_static_alignment {buf : Array UInt8} {d : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf d xs)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (symbols : xs.length ≤ 16383) (large : 32506 ≤ represented xs) (prior : Nat) :
    (prior + (mass (fun v => d.dyn_ltree[v]!.fc.toNat * staticLiteralCost v) 286 +
      mass (fun v => d.dyn_dtree[v]!.fc.toNat * staticDistanceCost v) 30) + 10) / 8 ≤
      (prior + 7) / 8 + represented xs := by
  have compressed := ledger_large_static_no_expansion ledger quality symbols large
  have rounded := ZlibF.Math.DeflateBound.ceil_bytes_append prior
    (mass (fun v => d.dyn_ltree[v]!.fc.toNat * staticLiteralCost v) 286 +
      mass (fun v => d.dyn_dtree[v]!.fc.toNat * staticDistanceCost v) 30 + 3)
  omega

/-- The actual data-type hint and complete source tree constructors
establish the byte-sensitive bound on their returned static_len counter.
The symbol-quality producer is still a separate history obligation. -/
theorem block_prepare_static_byte_budget {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d pb buf)
    (buffers : ZlibF.Spec.Public.StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (clear : BlockInit.BlockClear d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    ∃ (mb : Int32) (z' : ZStream) (result : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds result) ∧
      DGood (setD (r.put h z') ds result) r ds z' result ∧
      2 * result.static_len.toNat ≤ 13 * represented xs + 5 * xs.length + 14 := by
  obtain ⟨mb, z', result, run, goodA, _treesA, _buffersA, _account,
    _sizes, _storage, _frame, exactCost, _coarse⟩ :=
    block_prepare_static_budget_engine (ob := 0) good trees buffers ledger clear
  have budget : 2 * originalStaticCost d ≤ 13 * represented xs + 5 * xs.length + 14 :=
    ledger_static_byte_budget ledger quality
  refine ⟨mb, z', result, run, goodA, ?_⟩
  rw [exactCost, UInt64.toNat_ofNat']
  have reduced := Nat.mod_le (originalStaticCost d) (2 ^ 64)
  omega




end Zlib.Deflate.Engine.Proofs
