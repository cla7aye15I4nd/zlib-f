import ZlibF.Proof.«gz.sequence-safety»
import ZlibF.Proof.«gz.read-assembly»
import ZlibF.Proof.«gz.read-getc-step»
import ZlibF.Proof.«gz.read-gets-step»
import ZlibF.Proof.«gz.read-direct-step»

/-!
# The gz sequence goal

`gz_sequence_safety_public`: `Goal.gz_sequence_safety`, from the assembly `gz_sequence_safety_of` and the six read
leaves of the skeleton, each proved with no premise and with exactly the skeleton's statement: `gzread_step`,
`gzfread_step` (`gz.read-assembly`), `gzgetc_step`, `gzungetc_step` (`gz.read-getc-step`), `gzgets_step`
(`gz.read-gets-step`) and `gzdirect_step` (`gz.read-direct-step`).
-/

namespace ZlibF.Spec.Public.Proofs
open ZlibF.Spec.Public

/-- The open read leaves of the gz skeleton, all proved. -/
theorem gz_read_leaves : GzSkeleton.GzReadLeaves :=
  ⟨GzRead.gzread_step, GzRead.gzfread_step, GzRead.gzgetc_step, GzRead.gzungetc_step, GzRead.gzgets_step,
    GzRead.gzdirect_step⟩

/-- **Safety of every gz file history** (`Goal.gz_sequence_safety`), with no premise. -/
theorem gz_sequence_safety_public : Goal.gz_sequence_safety :=
  GzSkeleton.gz_sequence_safety_of gz_read_leaves

#print axioms gz_sequence_safety_public

end ZlibF.Spec.Public.Proofs
