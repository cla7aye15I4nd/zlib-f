import ZlibF.Proof.«deflate.c.init.general-main»

/-! # `Goal.deflateInit2_`

Every signed level, method, window, memory level and strategy: the version and stream-size
refusal, the `NULL` stream refusal, the parameter refusal of `Api.deflInit?`, the state allocation
failure, exact cleanup when any of the four buffer allocations fails, and `DeflateInitial` on
success. Composed from `deflate.c.init.general` and `deflate.c.init.general-main`.
-/

namespace ZlibF.Spec.Public.Proofs.DeflateInit2
open ZlibF.Spec.Public Zlib.Deflate.Proofs.GeneralInit

/-- **`Goal.deflateInit2_`**: for every signed level, method, window, memory level and strategy, the
version and stream-size refusal, the `NULL` stream refusal, the parameter refusal, the state
allocation failure, exact cleanup when a buffer allocation fails, and `DeflateInitial` on success. -/
theorem deflateInit2_proof : Goal.deflateInit2_ := fun level method wb mem strategy =>
  ⟨init2_version level method wb mem strategy, init2_null level method wb mem strategy,
   init2_main level method wb mem strategy⟩

end ZlibF.Spec.Public.Proofs.DeflateInit2

#print axioms ZlibF.Spec.Public.Proofs.DeflateInit2.deflateInit2_proof
