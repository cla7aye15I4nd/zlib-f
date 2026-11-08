import ZlibF.Proof.«inflate.c.slow-length-exact-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Restoring caller byte views commutes with a private decoder-record write. -/
theorem restoreRegions_setI (before after : Heap) (zs : Nat) (state : InflateState)
    (regions : List Region) :
    restoreRegions before (setI after zs state) regions = setI (restoreRegions before after regions) zs state := by
  induction regions generalizing after with
  | nil => rfl
  | cons region rest ih =>
    cases pointer : region.pointer with
    | null => simpa only [restoreRegions, List.foldl_cons, pointer] using ih after
    | ref ref off =>
      cases get : (Space.get before ref : Option (Array UInt8)) with
      | none => simpa only [restoreRegions, List.foldl_cons, pointer, get] using ih after
      | some array =>
        simpa only [restoreRegions, List.foldl_cons, pointer, get, byte_view_put_setI]
          using ih (Space.put after ref array)

/-- An additional allowed private-record write retains the exact caller
output frame without imposing an allocation-shape premise on its prefix. -/
theorem bufferFrame_setI_after {h after : Heap} {zs : Nat} {state : InflateState}
    {changed : Nat → Prop} {regions : List Region}
    (frame : BufferFrame h after changed regions) (allowed : changed zs) :
    BufferFrame h (setI after zs state) changed regions := by
  obtain ⟨⟨statics, allocOk, garbage, frontier, allocations, objects⟩, cells⟩ := frame
  refine ⟨?_, ?_⟩
  · rw [restoreRegions_setI]
    refine ⟨statics, allocOk, garbage, frontier, allocations, ?_⟩
    intro b live outside
    have different : b ≠ zs := fun same => outside (same ▸ allowed)
    simpa only [setI, upd_ne _ _ _ _ different] using objects b live outside
  · intro region member ref off array pointer get
    obtain ⟨next, nextGet, size, unchanged⟩ := cells region member ref off array pointer get
    exact ⟨next, by rw [byte_view_get_setI]; exact nextGet, size, unchanged⟩

/-- Adjacent actual output prefixes compose using their summed produced
count. The original capacity and both read-only facts come from execution. -/
theorem output_prefix_buffer_frame_trans {first second third : Heap}
    {changed : Nat → Prop} {dest : BRef} {off a b : Nat} {array : Array UInt8}
    (left : BufferFrame first second changed [⟨.ref dest off, a⟩])
    (right : BufferFrame second third changed [⟨.ref dest (off + a), b⟩])
    (shape : Shape first second) (get : Space.get first dest = some array)
    (writeSecond : Space.ro second dest = false) (writeThird : Space.ro third dest = false) :
    BufferFrame first third changed [⟨.ref dest off, a + b⟩] := by
  have firstFrame := BufferFrame.singleton_widen left (Nat.le_refl off) (by omega : off + a ≤ off + (a + b))
  have secondFrame := BufferFrame.singleton_widen right (by omega : off ≤ off + a)
    (by omega : off + a + b ≤ off + (a + b))
  exact BufferFrame.singleton_trans firstFrame secondFrame shape get writeSecond writeThird

#print axioms bufferFrame_setI_after
#print axioms output_prefix_buffer_frame_trans
end Zlib.Inflate.Proofs
