import ZlibF.Proof.«gz.skeleton-model»
import ZlibF.Proof.«gz.skeleton-read»
import ZlibF.Proof.«gz.sequence-safety»

/-!
# gz file interface, safety skeleton: the goal (skeleton)

The proof of `Goal.gz_sequence_safety` from the open read leaves (`gz.skeleton-read.lean`, `sorry` there). The
assembly is on `dev`: `gz_sequence_safety_of` (`gz.sequence-safety`) proves the goal from `GzReadLeaves`, the six
open read leaves with the skeleton's exact statements, and uses every other leaf from `dev` directly.

Closed on `dev` with exactly the skeleton's statement, and deleted here: `gzopen_safe`, `gzopen64_safe`
(`gz.inv-open-fresh`), `gzdopen_safe` (`gz.inv-open`), `gzclose_step` (`gz.inv-close`), `gzoffset64_step`,
`gzoffset_step`, `gzrewind_step` (`gz.inv-offset-rewind`), `gzclose_dispatch_inv`, `gztell64_step`, `gztell_step`,
`post_unchanged`, `safe_of_unchanged`, `gzeof_step`, `gzbuffer_step` (`gz.inv-queries`), `gzseek64_step`,
`gzseek_step` (`gz.inv-seek`), `gzclearerr_step` (`gz.inv-clearerr`), `gzerror_step` (`gz.inv-frame`), the write
leaves (`gzwrite.c.safety`), and the assembly `history_inv`, `operation_safe`, `close_safe` (`gz.sequence-safety`).
-/

namespace ZlibF.Spec.Public.GzSkeleton
open C Zlib.GzFs ZlibF.Spec.Public
set_option autoImplicit false

/-- **Safety of every gz file history** (skeleton: `dev`'s assembly applied to the open read leaves). -/
theorem gz_sequence_safety : Goal.gz_sequence_safety :=
  gz_sequence_safety_of ⟨gzread_step, gzfread_step, gzgetc_step, gzungetc_step, gzgets_step, gzdirect_step⟩

end ZlibF.Spec.Public.GzSkeleton
