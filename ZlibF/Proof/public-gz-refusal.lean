import ZlibF.Spec.Public.GzRefusal

/-!
# `Goal.gz_refusal`

Each gz function tests `file == NULL` first and returns at once (`gzseek`, `gztell`, `gzoffset`,
`gzprintf` and `gzgetc_` through the function they call; `gzseek`, `gztell` and `gzoffset` then
compare the result with itself). Every clause holds by evaluation.
-/

namespace ZlibF.Spec.Public.GzRefusalProof
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-- Every gz function called with a NULL handle returns its refusal value at once and changes neither the
heap nor the file system. -/
theorem gz_refusal : Goal.gz_refusal := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

end ZlibF.Spec.Public.GzRefusalProof

#print axioms ZlibF.Spec.Public.GzRefusalProof.gz_refusal
