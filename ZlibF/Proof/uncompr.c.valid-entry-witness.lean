import ZlibF.Proof.«uncompr.c.wrapper-safe»

/-!
# A valid successful-initialization caller witness

Two existing caller byte objects hold zero length cells. NULL+zero data buffers
are valid, and the actual first state allocation succeeds. The full initialized
wrapper theorem applies on this concrete heap, ruling out an empty internal
domain without reducing the compressed-data execution.
-/

set_option maxRecDepth 8192
namespace Zlib.Uncompr.Proof.ValidEntryWitness
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs

def zeros : Array UInt8 := Array.replicate 8 0

def firstHeap : Heap := { witnessHeap with bytes := upd witnessHeap.bytes 1 (some zeros) }
def entryHeap : Heap := { firstHeap with bytes := upd firstHeap.bytes 2 (some zeros) }

theorem entry_shape : Shape witnessHeap entryHeap := by
  have get1 : Space.get witnessHeap (.blk 1 : BRef) = some #[49, 0] := by
    simp [Space.get, witnessHeap, Heap.empty]
  have shape1 : Shape witnessHeap firstHeap := byte_view_put_shape get1 (by rfl) zeros
  have get2 : Space.get firstHeap (.blk 2 : BRef) = some (Array.replicate 32768 0) := by
    simp [Space.get, firstHeap, witnessHeap, Heap.empty]
  have shape2 : Shape firstHeap entryHeap := byte_view_put_shape get2 (by rfl) zeros
  exact shape1.trans shape2

theorem entry_fresh : Fresh entryHeap :=
  entry_shape.fresh rfl ZlibF.Spec.Public.Proofs.InflateInit.public_witness_fresh

theorem entry_uniq : Uniq entryHeap :=
  entry_shape.uniq ZlibF.Spec.Public.Proofs.InflateInit.public_witness_uniq

theorem entry_platform : ZlibF.PlatformMemory.ByteObjectsFit entryHeap := by
  have bound : zeros.size < ZlibF.PlatformMemory.byteObjectLimit := by
    simp only [zeros, Array.size_replicate, ZlibF.PlatformMemory.byteObjectLimit]
    decide
  exact (inflate_default_witness_platform.with_bytes (block := 1) bound).with_bytes (block := 2) bound

theorem entry_cell (b : Nat) (which : b = 1 ∨ b = 2) : LengthCell entryHeap (.ref (.blk b) 0) 0 := by
  have get : Space.get entryHeap (.blk b : BRef) = some zeros := by
    rcases which with rfl | rfl <;> simp [Space.get, entryHeap, firstHeap]
  constructor
  · exact Or.inr ⟨.blk b, 0, zeros, rfl, get, by simp [zeros], by decide +kernel⟩
  · exact Or.inr ⟨.blk b, 0, zeros, rfl, get, rfl, by simp [zeros]⟩

/-- A valid caller with a genuinely successful first allocation inhabits the
full initialized wrapper theorem. No compressed execution is reduced here. -/
theorem successful_entry_witness :
    ∃ rc after used made,
      C.run (uncompress2_z .null (.ref (.blk 2) 0) .null (.ref (.blk 1) 0)) entryHeap = .ok (rc, after) ∧
      LengthCell after (.ref (.blk 1) 0) (UInt64.ofNat used) ∧
      LengthCell after (.ref (.blk 2) 0) (UInt64.ofNat made) ∧
      used = 0 ∧ made = 0 ∧ LiveChange entryHeap after (fun _ => False) (fun _ => False) := by
  obtain ⟨rc, after, used, made, run, input, output, usedBound, madeBound, ledger, _codes⟩ :=
    Zlib.Uncompr.Proof.WrapperSafe.uncompress2_z_safe entryHeap .null .null
      (.ref (.blk 1) 0) (.ref (.blk 2) 0) 0 0 [] entry_fresh entry_uniq rfl entry_platform rfl
      (entry_cell 1 (Or.inl rfl)) (entry_cell 2 (Or.inr rfl))
      (Or.inl ⟨rfl, rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
      (by simp [Separate]) (by simp [Separate]) (by simp [Separate]) (by simp [Separate])
      (fun _ => rfl) (fun _ => rfl)
  exact ⟨rc, after, used, made, run, input, output, by simpa using usedBound, by simpa using madeBound, ledger⟩

#print axioms successful_entry_witness
end Zlib.Uncompr.Proof.ValidEntryWitness
