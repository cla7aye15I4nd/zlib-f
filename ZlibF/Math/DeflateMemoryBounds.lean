import ZlibF.Math.DeflateBlockSelection
import ZlibF.Math.DeflateDefaultBudget
import ZlibF.Math.DeflateStaticBudget
import ZlibF.Zlib.«deflate_strategies.c»

/-! Heap-free arithmetic for every legal memLevel. Actual execution must
establish the input, cost and header premises before using these budgets. -/
namespace ZlibF.Math.DeflateMemLevel
open Zlib.Deflate
open ZlibF.Math.DeflateSelection
open Zlib.Trees.Overlay
set_option autoImplicit false

def symbolSlots (memory : Nat) : Nat := 2 ^ (memory + 6)
def pendingBytes (memory : Nat) : Nat := 4 * symbolSlots memory

theorem memory_cases {memory : Nat} (low : 1 ≤ memory) (high : memory ≤ 9) :
    memory = 1 ∨ memory = 2 ∨ memory = 3 ∨ memory = 4 ∨ memory = 5 ∨
      memory = 6 ∨ memory = 7 ∨ memory = 8 ∨ memory = 9 := by omega

/-- Allocation sizes at all nine legal memory settings. -/
theorem allocation_geometry {memory : Nat} (low : 1 ≤ memory) (high : memory ≤ 9) :
    128 ≤ symbolSlots memory ∧ symbolSlots memory ≤ 32768 ∧
      512 ≤ pendingBytes memory ∧ pendingBytes memory ≤ 131072 ∧
      2 * symbolSlots memory = 2 ^ (memory + 7) := by
  rcases memory_cases low high with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Actual allocation word multiplications do not wrap at any memLevel. -/
theorem allocation_words {memory : Nat} (low : 1 ≤ memory) (high : memory ≤ 9) :
    ((UInt32.ofNat (2 ^ (memory + 7)) * 2).toNat / 2) = 2 ^ (memory + 7) ∧
      ((UInt32.ofNat (2 ^ (memory + 6)) * 4).toNat) = pendingBytes memory ∧
      (UInt32.ofNat (2 ^ (memory + 6))).toUInt64 * 4 = UInt64.ofNat (pendingBytes memory) ∧
      (UInt64.ofNat (pendingBytes memory)).toNat = pendingBytes memory := by
  rcases memory_cases low high with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The source direct minimum changes at memory eight. -/
theorem direct_minimum {memory : Nat} (low : 1 ≤ memory) (high : memory ≤ 9) :
    min (pendingBytes memory - 5) 32768 =
      if memory ≤ 7 then pendingBytes memory - 5 else 32768 := by
  rcases memory_cases low high with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Capacity is storage-limited through memory eight, LEN16-limited at nine. -/
theorem buffered_capacity {memory header : Nat} (low : 1 ≤ memory) (high : memory ≤ 9)
    (headerLow : 5 ≤ header) (headerHigh : header ≤ 6) :
    min (pendingBytes memory - header) 65535 =
      if memory ≤ 8 then pendingBytes memory - header else 65535 := by
  have headerCases : header = 5 ∨ header = 6 := by omega
  rcases memory_cases low high with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases headerCases with rfl | rfl <;> decide

/-- Small configurations cannot reuse the default buffered minimum 32768. -/
theorem buffered_minimum {memory header : Nat} (low : 1 ≤ memory) (high : memory ≤ 9)
    (headerLow : 5 ≤ header) (headerHigh : header ≤ 6) :
    min (min (pendingBytes memory - header) 65535) 32768 =
      if memory ≤ 7 then pendingBytes memory - header else 32768 := by
  have headerCases : header = 5 ∨ header = 6 := by omega
  rcases memory_cases low high with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases headerCases with rfl | rfl <;> decide

/-- The actual unsigned subtract/min/narrow formula is exact. -/
theorem buffered_capacity_word {memory : Nat} {header : UInt32}
    (low : 1 ≤ memory) (high : memory ≤ 9)
    (headerLow : 5 ≤ header.toNat) (headerHigh : header.toNat ≤ 6) :
    (MIN (UInt64.ofNat (pendingBytes memory) - header.toUInt64) (65535 : UInt64)).toUInt32.toNat =
      min (pendingBytes memory - header.toNat) 65535 := by
  have headerCases : header = 5 ∨ header = 6 := by
    by_cases five : header.toNat = 5
    · exact Or.inl (UInt32.toNat_inj.mp five)
    · exact Or.inr (UInt32.toNat_inj.mp (by change header.toNat = 6; omega))
  rcases memory_cases low high with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases headerCases with rfl | rfl <;> decide

/-- Actual selected payload fits the unread window and exact pending room. -/
theorem buffered_selected_room {memory header left : Nat} (low : 1 ≤ memory) (high : memory ≤ 9)
    (headerLow : 5 ≤ header) (headerHigh : header ≤ 6) :
    let len := min left (min (pendingBytes memory - header) 65535)
    len ≤ left ∧ len < 65536 ∧ header + len ≤ pendingBytes memory := by
  have geometry := allocation_geometry low high
  dsimp only
  omega

/-- Every legal memory setting has enough separation for fixed-code
prefixes, even the smallest 128-slot buffer. The individual bit bound is
a data premise supplied by fixed-code accounting, not a callee contract. -/
theorem fixed_overlay_prefix {memory start : Nat} (low : 1 ≤ memory) (high : memory ≤ 9)
    (startMax : start ≤ 7) (costs : List Nat)
    (costBound : ∀ cost ∈ costs, cost ≤ 31)
    (symbolsFit : costs.length + 1 ≤ symbolSlots memory) (k : Nat) (prefixBound : k ≤ costs.length) :
    start + 3 + (costs.take k).sum + 15 ≤ 8 * (symbolSlots memory + 3 * k) := by
  have slots := (allocation_geometry low high).1
  have costsBound : ∀ (xs : List Nat), (∀ cost ∈ xs, cost ≤ 31) → xs.sum ≤ 31 * xs.length := by
    intro xs
    induction xs with
    | nil => intro _; simp
    | cons cost xs ih =>
      intro bound
      have head := bound cost (by simp)
      have tail := ih (fun c member => bound c (by simp [member]))
      simp only [List.sum_cons, List.length_cons]
      omega
  have sumBound := costsBound (costs.take k) (fun c member => costBound c (List.mem_of_mem_take member))
  have takeLength : (costs.take k).length = k := by rw [List.length_take]; omega
  rw [takeLength] at sumBound
  omega

/-- The existing coarse dynamic-excess argument covers unread-prefix
room already at memory five; actual trees must establish the premises. -/
theorem dynamic_overlay_prefix_from_memory_five {memory start header : Nat}
    (low : 5 ≤ memory) (high : memory ≤ 9) (costs : List Nat)
    (startMax : start ≤ 7) (headerMax : header ≤ 2283)
    (symbolsFit : costs.length + 1 ≤ symbolSlots memory)
    (excess : 1000 * bitExcess costs ≤ 6257 * (costs.length + 3)) (k : Nat) :
    start + 3 + header + (costs.take k).sum + 15 ≤ 8 * (symbolSlots memory + 3 * k) := by
  have capacityMin : 2048 ≤ symbolSlots memory := by
    have cases : memory = 5 ∨ memory = 6 ∨ memory = 7 ∨ memory = 8 ∨ memory = 9 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> decide
  have prefixCost := prefix_bits_le costs k
  omega

/-- The coarse dynamic budget fits whole pending storage for memory
five through nine. A stronger 31-bits-per-slot bound is unnecessary here. -/
theorem dynamic_pending_room_from_memory_five {memory start header : Nat}
    (low : 5 ≤ memory) (high : memory ≤ 9) (costs : List Nat)
    (startMax : start ≤ 7) (headerMax : header ≤ 2283)
    (symbolsFit : costs.length + 1 ≤ symbolSlots memory)
    (excess : 1000 * bitExcess costs ≤ 6257 * (costs.length + 3)) :
    start + 3 + header + costs.sum + 15 + 7 ≤ 8 * pendingBytes memory := by
  have capacityMin : 2048 ≤ symbolSlots memory := by
    have cases : memory = 5 ∨ memory = 6 ∨ memory = 7 ∨ memory = 8 ∨ memory = 9 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> decide
  have total := prefix_bits_le costs costs.length
  rw [List.take_length] at total
  unfold pendingBytes
  omega

/-- The exact unsigned byte-cost rounding leaves the two bytes needed
for transferring the winning stored comparison to actual pending room. -/
theorem fixed_byte_cost_room {memory symbols : Nat} {bits : UInt64}
    (low : 1 ≤ memory) (high : memory ≤ 9)
    (symbolsFit : symbols + 1 ≤ symbolSlots memory)
    (budget : bits.toNat ≤ 31 * symbols + 7) :
    (byteCost bits).toNat + 2 ≤ pendingBytes memory := by
  have geometry := allocation_geometry low high
  have first : (bits + 3).toNat = bits.toNat + 3 := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by change bits.toNat + 3 < 18446744073709551616; omega)
  have second : (bits + 3 + 7).toNat = bits.toNat + 10 := by
    rw [UInt64.toNat_add, first]
    exact Nat.mod_eq_of_lt (by change bits.toNat + 3 + 7 < 18446744073709551616; omega)
  unfold byteCost pendingBytes
  rw [UInt64.toNat_shiftRight, second]
  change (bits.toNat + 10) >>> 3 + 2 ≤ _
  rw [Nat.shiftRight_eq_div_pow]
  omega

/-- A stored candidate winning the actual source cost comparison fits
its payload and worst six-byte header at every legal memLevel. -/
theorem selected_stored_room {memory symbols : Nat} {bits opt stored : UInt64} {forceFixed : Bool}
    (low : 1 ≤ memory) (high : memory ≤ 9)
    (symbolsFit : symbols + 1 ≤ symbolSlots memory)
    (budget : bits.toNat ≤ 31 * symbols + 7)
    (storedWord : stored.toNat ≤ 4294967296)
    (selected : stored + 4 ≤ selectedCost opt (byteCost bits) forceFixed) :
    stored.toNat + 6 ≤ pendingBytes memory := by
  have fixedBound := fixed_byte_cost_room low high symbolsFit budget
  have minBound := selected_le_fixed opt (byteCost bits) forceFixed
  have add : (stored + 4).toNat = stored.toNat + 4 := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by change stored.toNat + 4 < 18446744073709551616; omega)
  change (stored + 4).toNat ≤ (selectedCost opt (byteCost bits) forceFixed).toNat at selected
  rw [add] at selected
  omega

end ZlibF.Math.DeflateMemLevel

#print axioms ZlibF.Math.DeflateMemLevel.memory_cases
#print axioms ZlibF.Math.DeflateMemLevel.allocation_geometry
#print axioms ZlibF.Math.DeflateMemLevel.allocation_words
#print axioms ZlibF.Math.DeflateMemLevel.direct_minimum
#print axioms ZlibF.Math.DeflateMemLevel.buffered_capacity
#print axioms ZlibF.Math.DeflateMemLevel.buffered_minimum
#print axioms ZlibF.Math.DeflateMemLevel.buffered_capacity_word
#print axioms ZlibF.Math.DeflateMemLevel.buffered_selected_room
#print axioms ZlibF.Math.DeflateMemLevel.fixed_overlay_prefix
#print axioms ZlibF.Math.DeflateMemLevel.dynamic_overlay_prefix_from_memory_five
#print axioms ZlibF.Math.DeflateMemLevel.dynamic_pending_room_from_memory_five
#print axioms ZlibF.Math.DeflateMemLevel.fixed_byte_cost_room
#print axioms ZlibF.Math.DeflateMemLevel.selected_stored_room
