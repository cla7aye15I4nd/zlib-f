import ZlibF.Spec.ByteAddress

/-!
# Positive checks of the CRC low-address-bit interpretation

Only residues observed by the alignment mask are represented. The proofs
range over arbitrary non-block residues and preserve the raw-block case.
-/

set_option autoImplicit false

namespace C.ByteAddress.Proofs
open C.ByteAddress C.ByteAddress.Spec

private theorem low_ofNat (n : Nat) : low (UInt64.ofNat n) = n % 8 := by
  unfold low
  rw [UInt64.toNat_and,UInt64.toNat_ofNat']
  have mask : (7 : UInt64).toNat = 2^3-1 := by decide
  rw [mask,Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_mod_of_dvd n (Nat.pow_dvd_pow 2 (by decide))

private theorem value_ref (h : Heap) (ref : BRef) (offset : Nat) :
    value h (.ref ref offset) = UInt64.ofNat (base h ref + offset) := by
  cases ref <;> simp only [value,base,Nat.zero_add]

/-- The actual translated address observation reads metadata without any
heap update or pointer access. -/
theorem address_read_is_pure : Goal.address_read_is_pure := by
  intro h p
  rfl

/-- Existing raw-block observations retain their exact original value. -/
theorem raw_block_unchanged : Goal.raw_block_unchanged := by
  intro h block offset
  rfl

/-- Each non-block byte origin can have any concrete residue. The witness
changes only the symbolic address assignment of the otherwise empty heap. -/
theorem every_layout_is_representable : Goal.every_layout_is_representable := by
  intro physical aligned
  let assignment : ByteBaseRef → Fin 8 := fun ref =>
    ⟨physical ref.toBRef % 8,Nat.mod_lt _ (by decide)⟩
  refine ⟨{ Heap.empty with byteBase := assignment },?_⟩
  intro ref
  cases ref with
  | blk block => exact aligned block
  | str id => rfl
  | dstate_depth id => rfl
  | st_dist_code => rfl
  | st_length_code => rfl

/-- Unsigned conversion before masking preserves the base-plus-offset
residue, even when the natural-number address exceeds the machine word. -/
theorem mask_refines_base_plus_offset : Goal.mask_refines_base_plus_offset := by
  intro h physical represented ref offset
  rw [value_ref,low_ofNat,← represented ref]
  simp only [Nat.add_mod,Nat.mod_mod]

/-- Advancing a byte pointer advances its represented residue modulo eight. -/
theorem pointer_advance_preserves_low_bits : Goal.pointer_advance_preserves_low_bits := by
  intro h ref offset count
  rw [value_ref,low_ofNat,value_ref,low_ofNat]
  omega

/-- Every represented origin reaches alignment at its first such position
within seven bytes, with no earlier aligned position. -/
theorem first_aligned_offset : Goal.first_aligned_offset := by
  intro h ref offset
  have residueBound : low (value h (.ref ref offset)) < 8 := by
    rw [value_ref,low_ofNat]
    exact Nat.mod_lt _ (by decide)
  dsimp only
  refine ⟨by omega,?_,?_⟩
  · rw [pointer_advance_preserves_low_bits h ref offset]
    omega
  · intro before shorter
    rw [pointer_advance_preserves_low_bits h ref offset]
    omega

/-- Byte-array stores cannot change symbolic origin metadata. -/
theorem byte_stores_preserve_bases : Goal.byte_stores_preserve_bases := by
  intro h ref bytes
  cases ref <;> try rfl
  simp only [Space.put]
  split <;> rfl

/-- In-place byte-array modifications preserve the same metadata. -/
theorem byte_modifies_preserve_bases : Goal.byte_modifies_preserve_bases := by
  intro h ref modify
  cases ref <;> rfl

/-- An arbitrary concrete layout can be assigned to any existing heap
without changing any storage, allocator oracle or garbage assignment. -/
theorem every_existing_heap_accepts_layout : Goal.every_existing_heap_accepts_layout := by
  intro h physical aligned
  refine ⟨?_,?_⟩
  · intro ref
    cases ref with
    | blk block => exact aligned block
    | str id => rfl
    | dstate_depth id => rfl
    | st_dist_code => rfl
    | st_length_code => rfl
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end C.ByteAddress.Proofs
