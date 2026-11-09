import ZlibF.Spec.Public.Utilities
import ZlibF.Spec.Public.Initialisation

/-! # Actual argument refusals and compatibility returns in compress.c -/

namespace ZlibF.Spec.Public.Proofs.CompressEntry
open C Zlib.Compress
set_option autoImplicit false

private theorem u64_positive {n : UInt64} (nonzero : n ≠ 0) : 0 < n := by
  rw [UInt64.lt_iff_toNat_lt]
  have positive : n.toNat ≠ 0 := fun eq => nonzero (UInt64.toNat_inj.mp eq)
  change 0 < n.toNat
  omega

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
Every actual entry rejection returns STREAM_ERROR before clearing the
length or allocating the automatic stream. This covers exactly the
argument-refusal branch; it asserts no compression or successful-call
contract and assumes no engine contract. -/
theorem compress2_z_rejected (h : Heap) (dest : BPtr) (capacity : Option UInt64)
    (source : BPtr) (n : UInt64) (level : Int32)
    (rejected : compressRejected dest capacity source n) :
    C.run (compress2_z dest capacity source n level) h =
      .ok ((Z_STREAM_ERROR, capacity), h) := by
  cases capacity with
  | none => rfl
  | some amount =>
      have guard : ((n > 0 && source == .null) || (amount > 0 && dest == .null)) = true := by
        rcases rejected with missing | ⟨null, nonzero⟩ | ⟨other, same, null, nonzero⟩
        · cases missing
        · simp [null, u64_positive nonzero]
        · have equal : other = amount := Option.some.inj same.symm
          subst other
          simp [null, u64_positive nonzero]
      simp only [C.run, compress2_z, guard, ite_true, pure_app]

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen, int level)`.
The complete physical postcondition on every argument-refusal branch:
zero output, unchanged stored capacity, exact unchanged heap and live
allocation ledger. No readability premise is needed for rejected input. -/
theorem compress2_z_rejected_effects (h : Heap) (dest : BPtr) (capacity : Option UInt64)
    (source : BPtr) (n : UInt64) (level : Int32)
    (rejected : compressRejected dest capacity source n) :
    C.run (compress2_z dest capacity source n level) h =
      .ok ((Z_STREAM_ERROR, capacity), h) ∧
    Store h dest [] h ∧ SameObjects h h ∧
    LiveChange h h (fun _ => False) (fun _ => False) := by
  exact ⟨compress2_z_rejected h dest capacity source n level rejected,
    Or.inl ⟨rfl, rfl⟩, by simp [SameObjects], fun _ => by simp⟩

/-- `int compress2(Bytef *dest, uLongf *destLen, const Bytef *source,
uLong sourceLen, int level)`.
With its required nonnull length cell, the actual compatibility wrapper
preserves that cell's value on entry rejection and writes the same value
back. The proof follows the actual wrapper, not an assumed callee contract. -/
theorem compress2_rejected (h : Heap) (dest : BPtr) (amount : UInt64)
    (source : BPtr) (n : UInt64) (level : Int32)
    (rejected : compressRejected dest (some amount) source n) :
    C.run (compress2 dest (some amount) source n level) h =
      .ok ((Z_STREAM_ERROR, amount), h) := by
  have run := compress2_z_rejected h dest (some amount) source n level rejected
  change compress2_z dest (some amount) source n level h = _ at run
  simp only [C.run, compress2, bind_app, run, pure_app, Option.getD_some]

/-- `int compress_z(Bytef *dest, z_size_t *destLen, const Bytef *source,
z_size_t sourceLen)`.
The real default-level alias has the same complete entry refusal. -/
theorem compress_z_rejected (h : Heap) (dest : BPtr) (capacity : Option UInt64)
    (source : BPtr) (n : UInt64)
    (rejected : compressRejected dest capacity source n) :
    C.run (compress_z dest capacity source n) h =
      .ok ((Z_STREAM_ERROR, capacity), h) :=
  compress2_z_rejected h dest capacity source n Z_DEFAULT_COMPRESSION rejected

/-- `int compress(Bytef *dest, uLongf *destLen, const Bytef *source,
uLong sourceLen)`.
The real default-level compatibility alias retains the admitted length
cell on the same actual argument-refusal execution. -/
theorem compress_rejected (h : Heap) (dest : BPtr) (amount : UInt64)
    (source : BPtr) (n : UInt64)
    (rejected : compressRejected dest (some amount) source n) :
    C.run (compress dest (some amount) source n) h =
      .ok ((Z_STREAM_ERROR, amount), h) :=
  compress2_rejected h dest amount source n Z_DEFAULT_COMPRESSION rejected

end ZlibF.Spec.Public.Proofs.CompressEntry
