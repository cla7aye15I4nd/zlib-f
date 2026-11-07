import ZlibF.Spec.Public.Queries

namespace ZlibF.Spec.Public.Proofs

/-- `uLong zlibCompileFlags(void)`: the default LP64 flags, with the heap unchanged. -/
theorem zlibCompileFlags : Goal.zlibCompileFlags := by
  intro h
  rfl

#print axioms zlibCompileFlags
end ZlibF.Spec.Public.Proofs
