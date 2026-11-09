import ZlibF.Proof.«inflate.c.origin-history-calls»
import ZlibF.Proof.«inflate.c.output-frame-footprint-compose»
import ZlibF.Spec.Public.Sequences

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Widening a declared output prefix is valid for null and nonnull pointers. -/
theorem buffer_frame_output_capacity {h after : Heap} {changed : Nat → Prop}
    {pointer : BPtr} {made capacity : Nat}
    (frame : BufferFrame h after changed [⟨pointer, made⟩]) (bound : made ≤ capacity) :
    BufferFrame h after changed [⟨pointer, capacity⟩] := by
  cases pointer with
  | null =>
    refine ⟨?_, ?_⟩
    · simpa only [restoreRegions, List.foldl_cons, List.foldl_nil] using frame.1
    · intro region member ref off array pointer get
      have same : region = (⟨.null, capacity⟩ : Region) := List.mem_singleton.mp member
      subst region
      cases pointer
  | ref ref off =>
    exact BufferFrame.singleton_widen frame (Nat.le_refl off) (by omega)

/-- The initialized default header is absent. The produced-output prefix
therefore widens to exactly the original public output region. -/
theorem inflate_default_public_buffer_frame {h after : Heap} {r : ZStreamRef} {zs made : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s)
    (flush : Int32)
    (frame : BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b)
      [⟨z.next_out, made⟩]) (bound : made ≤ z.avail_out.toNat) :
    BufferFrame h after
      (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r (.inflate (some r) flush) b)
      (StreamWriteRegions h r (.inflate (some r) flush)) := by
  have regions : StreamWriteRegions h r (.inflate (some r) flush) =
      [⟨z.next_out, z.avail_out.toNat⟩] := by
    simp only [StreamWriteRegions, before.good.live.hz, before.good.live.zst,
      before.good.live.hs, before.header, HeaderRegions]
  rw [regions]
  apply inflate_buffer_frame_mono (buffer_frame_output_capacity frame bound)
  intro b changed
  rcases changed with root | owned
  · exact Or.inl root
  · exact Or.inr (Or.inl ((before.good.streamOwned_iff b).mpr owned))

#print axioms buffer_frame_output_capacity
#print axioms inflate_default_public_buffer_frame
end Zlib.Inflate.Proofs
