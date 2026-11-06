import ZlibF.Spec.Api.Concrete

namespace ZlibF.Spec.Api.Proofs

/-- Argument rejection precedes clearing the scalar or initialising a compressor:
the `_z` model writes no bytes and preserves the initial capacity when it has a scalar. -/
theorem compress2Z_rejected {c : CompressCall} {r : CompressResult}
    (hrejected : c.rejected) (hr : Compress2Z c r) :
    r.rc = Z.streamError ∧ r.produced = [] ∧
      r.storedLength = (if c.lengthNull then none else some c.capacity) := by
  simpa only [Compress2Z, ite_eq_left hrejected] using hr

/-- A null destination with zero capacity reaches initialisation. For valid parameters
its only model outcomes are allocation failure or the inner stream error, with zero output
and the scalar cleared. -/
theorem compress2Z_null_zero_iff {c : CompressCall} {r : CompressResult} {p : DeflParams}
    (hdest : c.destNull = true) (hcap : c.capacity = 0)
    (hsource : c.sourceNull = false) (hlength : c.lengthNull = false)
    (hparams : compressParams c.level = some p) :
    Compress2Z c r ↔
      (r.rc = Z.memError ∨ r.rc = Z.streamError) ∧ r.produced = [] ∧
        r.storedLength = some 0 := by
  simp [Compress2Z, CompressCall.rejected, hdest, hcap, hsource, hlength, hparams]

/-- The compatibility-wrapper model has no defined outcome for a null length pointer. -/
theorem compress2Wrapper_null_length {c : CompressCall} {r : CompressResult}
    (hlength : c.lengthNull = true) : ¬ Compress2Wrapper c r := by
  simp [Compress2Wrapper, hlength]

/-- A missing scalar is a clean error in the actual translated `_z` entry, on every heap. -/
theorem compress2_z_null_length_returns (dest source : C.BPtr) (sourceLen : UInt64)
    (level : Int32) (h : C.Heap) :
    Concrete.compress2_z dest none source sourceLen level h =
      .ret h (C.Z_STREAM_ERROR, none) := by
  rfl

/-- A missing scalar faults in the actual translated compatibility wrapper before `_z`
can perform its argument checks, on every heap. -/
theorem compress2_null_length_faults (dest source : C.BPtr) (sourceLen : UInt64)
    (level : Int32) (h : C.Heap) :
    Concrete.compress2 dest none source sourceLen level h = .fault := by
  rfl

/-- Positive model witness: a null source with nonempty input is rejected even for a bad level;
the original length survives. -/
theorem compress2Z_source_null_witness :
    Compress2Z ⟨[0], 7, 10, true, false, false⟩ ⟨Z.streamError, [], some 7⟩ := by
  simp [Compress2Z, CompressCall.rejected]

/-- Positive model witness: a null scalar is rejected without a stored length, before level
validation or the positive-capacity null-destination check. -/
theorem compress2Z_length_null_witness :
    Compress2Z ⟨[], 7, 10, true, true, true⟩ ⟨Z.streamError, [], none⟩ := by
  simp [Compress2Z, CompressCall.rejected]

/-- Positive model witness: a null destination with positive capacity is an early argument
error, so the original length survives. -/
theorem compress2Z_dest_null_positive_witness :
    Compress2Z ⟨[0], 7, 10, false, true, false⟩ ⟨Z.streamError, [], some 7⟩ := by
  simp [Compress2Z, CompressCall.rejected]

/-- Positive model witness: a bad level with acceptable pointer shapes is rejected after
clearing the scalar. -/
theorem compress2Z_invalid_level_witness :
    Compress2Z ⟨[0], 7, 10, false, false, false⟩ ⟨Z.streamError, [], some 0⟩ := by
  simp [Compress2Z, CompressCall.rejected, compressParams, deflInit?]

/-- Positive model witness: the zero-capacity null destination may fail allocation. -/
theorem compress2Z_null_zero_mem_witness :
    Compress2Z ⟨[0], 0, 6, false, true, false⟩ ⟨Z.memError, [], some 0⟩ := by
  simp [Compress2Z, CompressCall.rejected, compressParams, deflInit?]

/-- Positive model witness: after successful initialisation, the zero-capacity null
destination is refused by the inner compressor. -/
theorem compress2Z_null_zero_stream_witness :
    Compress2Z ⟨[0], 0, 6, false, true, false⟩ ⟨Z.streamError, [], some 0⟩ := by
  simp [Compress2Z, CompressCall.rejected, compressParams, deflInit?]

end ZlibF.Spec.Api.Proofs
