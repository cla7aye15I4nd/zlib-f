import ZlibF.Proof.«gz.inv-model»

/-!
# gz: a zero-length read may not name its buffer as a written region

`GzWriteRegions` named `[buf, buf + 0)` for `gzread` and `[buf, buf + 0)` for a zero product in `gzfread`, and
`GzArguments` puts no condition on `buf` when the length is 0. `BufferFrame` keeps the view of every named region,
also an empty one. A caller may pass the handle's message (the pointer `gzerror` returns) with `len = 0`. With
`again = 1` and a message set, `gzread` runs `gz_error(state, Z_OK, NULL)`, which frees the message block, so the
view behind `buf` is gone and the old `GzStepPost` cannot hold. The frame below fails for any freed block.
-/

namespace GzReadEmptyRegionRegression
open C ZlibF.Spec.Public Zlib.Gzlib.Proofs

/-- **The empty region of a freed block has no buffer frame**, whatever the changed set. -/
theorem empty_region_frame_fails (h : Heap) (C : Nat → Prop) (b : Nat) (a : Array UInt8)
    (hb : h.bytes b = some a) :
    ¬ BufferFrame h (freeStr h (.ref (.blk b) 0)) C [⟨.ref (.blk b) 0, 0⟩] := by
  rintro ⟨-, cells⟩
  obtain ⟨a', h', -⟩ := cells _ (List.mem_singleton_self _) (.blk b) 0 a rfl hb
  have e : (freeStr h (.ref (.blk b) 0)).bytes b = some a' := h'
  simp [freeStr] at e

end GzReadEmptyRegionRegression
