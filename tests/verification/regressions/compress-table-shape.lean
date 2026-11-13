import ZlibF.Spec.Public.Utilities
import ZlibF.Spec.Public.Domains
import ZlibF.Zlib.«compress.c»

open C ZlibF.Spec.Public ZlibF.Spec

/-! The former compressor contracts (`CompressorContract`, `CompressorSafety`) compared the
heap after the call with `SameObjects`, which requires equal object tables, including their
physical length. After the argument checks `compress2_z` creates a local `z_stream` and frees
it on every later path. Freeing leaves an empty entry, so the stream table grows even when
`deflateInit` refuses the level before allocating anything. The accepted arguments below
(empty source and output, an invalid level) were therefore a counterexample to the former
goals. No C operation observes the table length; the contracts now compare tables entry by
entry (`SameObjectsUpToTableShape`), as the decompression contracts do. -/
namespace CompressRegression

set_option maxRecDepth 8192

/-- Accepted arguments: empty output, empty source, level 10 (refused by `deflateInit`). -/
def run : M (Int32 × Option UInt64) := Zlib.Compress.compress2_z .null (some 0) .null 0 10

/-- The actual run returns `Z_STREAM_ERROR` with a longer stream table. -/
def observed : Bool :=
  match C.run run witnessHeap with
  | .ok ((rc, _), after) => rc == Z_STREAM_ERROR && after.streams.arr.size != witnessHeap.streams.arr.size
  | .error _ => false

theorem observed_eq : observed = true := by
  decide +kernel

/-- The accepted call leaves the stream table physically longer, so `SameObjects` fails. -/
theorem table_grows : ∃ stored after,
    C.run run witnessHeap = .ok ((Z_STREAM_ERROR, stored), after) ∧ ¬ SameObjects witnessHeap after := by
  have h := observed_eq
  unfold observed at h
  split at h
  · rename_i rc stored after r
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    refine ⟨stored, after, by rw [r, h.1], ?_⟩
    intro same
    exact h.2 (congrArg (fun t => t.arr.size) same.2.2.2.1)
  · cases h

#print axioms table_grows

end CompressRegression
