import ZlibF.Proof.«inffast.c.call-origin»
import ZlibF.Proof.«inftrees.c.decode.fast-flags-frame»
import ZlibF.Proof.«inffixed.h.fast-flags»

/-! Documented registrations of existing supporting proofs.

Each alias has the exact existing target type. No input premise or mathematical
result changes. These internal targets do not establish the public inflate goal.
-/
namespace ZlibF.Proof.Registration

/-- The actual fast call preserves input-bit origin under the existing call
environment, including byte rollback and final state writeback. -/
theorem fast_call_origin :
    Zlib.Inffast.Spec.CallOrigin.Goal.actual_fast_preserves_origin := by
  exact Zlib.Inffast.Proofs.actual_fast_preserves_origin

/-- An unchanged readable table prefix preserves the existing compatibility
predicate for every admitted table query. -/
theorem fast_leaf_flags_of_prefix :
    Zlib.Inftrees.Spec.FastTableFlags.Goal.fast_leaf_flags_of_prefix := by
  exact Zlib.Inftrees.Proofs.fast_leaf_flags_of_prefix

/-- Both fixed decode tables satisfy the existing fast-leaf compatibility
target for their complete stated query domains. -/
theorem fixed_tables_fast_leaf_flags :
    Zlib.Inftrees.Spec.FastTableFlags.Goal.fixed_tables_have_fast_leaf_flags := by
  exact Zlib.Inftrees.Proofs.fixed_tables_have_fast_leaf_flags

/-- Fast and slow leaf acceptance agree under the existing leaf-shape and
compatibility conditions. This does not construct an initialized decoder. -/
theorem leaf_classification_agrees :
    Zlib.Inftrees.Spec.FastTableFlags.Goal.leaf_classification_agrees := by
  exact Zlib.Inftrees.Proofs.leaf_classification_agrees

end ZlibF.Proof.Registration
