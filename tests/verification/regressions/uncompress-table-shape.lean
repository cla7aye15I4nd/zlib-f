import ZlibF.Spec.Public.Utilities
import ZlibF.Spec.Public.Domains
import ZlibF.Zlib.«uncompr.c»

open C ZlibF.Spec.Public ZlibF.Spec

/-! The former decompression utility contracts compared the heap after the call with
`SameObjects`, which requires equal object tables, including their physical length.
`uncompress2_z` allocates a local `z_stream` and a local 8-byte block before its argument
checks, and frees both on every path. Freeing leaves an empty entry, so the stream table
grows from one entry to four even on the null-argument refusal. The former
`Goal.uncompress2_z` was therefore false on the public caller witness. No C operation
observes the table length; the contracts now compare tables entry by entry
(`SameObjectsUpToTableShape`), as the `inflateInit2_` contract already does. -/
namespace UncompressRegression

set_option maxRecDepth 8192

/-- The four null arguments: the call refuses them with `Z_STREAM_ERROR`. -/
def refusal : M Int32 := Zlib.Uncompr.uncompress2_z .null .null .null .null

/-- The actual run returns `Z_STREAM_ERROR` with a stream table of four entries. -/
def observed : Bool :=
  match C.run refusal witnessHeap with
  | .ok (rc, after) => rc == Z_STREAM_ERROR && after.streams.arr.size == 4
  | .error _ => false

theorem observed_eq : observed = true := by
  decide +kernel

theorem witness_streams_size : witnessHeap.streams.arr.size = 1 := by
  decide +kernel

/-- The refusal leaves the stream table physically longer, with an empty entry. -/
theorem refusal_table_grows : ∃ after,
    C.run refusal witnessHeap = .ok (Z_STREAM_ERROR, after) ∧
    after.streams.arr.size = 4 ∧ ¬ SameObjects witnessHeap after := by
  have h := observed_eq
  unfold observed at h
  split at h
  · rename_i rc after run
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨after, by rw [run, h.1], h.2, ?_⟩
    intro same
    have sizes := congrArg (fun t => t.arr.size) same.2.2.2.1
    simp only [h.2, witness_streams_size] at sizes
    omega
  · cases h

#print axioms refusal_table_grows

end UncompressRegression
