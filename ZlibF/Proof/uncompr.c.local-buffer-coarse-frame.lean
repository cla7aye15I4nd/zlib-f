import ZlibF.Proof.«uncompr.c.caller-frame»
import ZlibF.Proof.«inflate.c.local-public-resources-frame-observer»

namespace Zlib.Uncompr.Proof.LocalFrame
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.CallerFrame
set_option autoImplicit false

private theorem put_reverse_frame (h : Heap) (ref : BRef) (a : Array UInt8) (off : Nat) :
    Frame (Space.put h ref a) h (ByteRoot (.ref ref off)) := by
  cases ref with
  | blk i =>
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b live outside
    have ne : b ≠ i := outside
    simp [Space.put, ne]
  | dstate_depth i =>
    cases stored : h.dstates i with
    | none => simp only [Space.put, stored]; exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, by intro b _ _; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
    | some state =>
      simp only [Space.put, stored]
      refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
      intro b live outside
      have ne : b ≠ i := outside
      simp [ne]
  | str i => exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, by intro b _ _; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
  | st_dist_code => exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, by intro b _ _; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
  | st_length_code => exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, by intro b _ _; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩

theorem put_forward_frame (h : Heap) (ref : BRef) (a : Array UInt8) (off : Nat) :
    Frame h (Space.put h ref a) (ByteRoot (.ref ref off)) := by
  cases ref with
  | blk i =>
    refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
    intro b live outside
    have ne : b ≠ i := outside
    simp [Space.put, ne]
  | dstate_depth i =>
    cases stored : h.dstates i with
    | none => simp only [Space.put, stored]; exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, by intro b _ _; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
    | some state =>
      simp only [Space.put, stored]
      refine ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_⟩
      intro b live outside
      have ne : b ≠ i := outside
      simp [ne]
  | str i => exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, by intro b _ _; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
  | st_dist_code => exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, by intro b _ _; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
  | st_length_code => exact ⟨rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _, by intro b _ _; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩

/-- A real scalar Store changes only the pointer's byte root. -/
theorem store_frame {h after : Heap} {p : BPtr} {xs : List UInt8}
    (store : Store h p xs after) : Frame h after (ByteRoot p) := by
  rcases store with ⟨_, rfl⟩ | ⟨ref,off,a,pointer,get,write,room,rfl⟩
  · exact ⟨rfl,rfl,rfl,Nat.le_refl _,Nat.le_refl _,by intro b _ _; exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩
  · subst p
    exact put_forward_frame h ref _ off

/-- Forgetting the interval of an exact byte frame yields the ordinary
object frame. All seven typed tables, static data and metadata are retained
outside the explicit private/output-root footprint. -/
theorem buffer_frame_object_frame {h after : Heap} {changed : Nat → Prop}
    {pointer : BPtr} {count : Nat}
    (frame : BufferFrame h after changed [⟨pointer,count⟩]) :
    Frame h after (fun b => changed b ∨ ByteRoot pointer b) := by
  have base := frame.1
  cases pointer with
  | null =>
    simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, ByteRoot, or_false] using base
  | ref ref off =>
    cases get : (Space.get h ref : Option (Array UInt8)) with
    | none =>
      simp only [restoreRegions, List.foldl_cons, List.foldl_nil, get] at base
      obtain ⟨static, alloc, garbage, next, allocations, slots⟩ := base
      refine ⟨static, alloc, garbage, next, allocations, ?_⟩
      intro b live outside
      exact slots b live (fun old => outside (Or.inl old))
    | some a =>
      simp only [restoreRegions, List.foldl_cons, List.foldl_nil, get] at base
      apply frame_trans_restrict base (put_reverse_frame after ref a off)
      intro b live outside
      exact ⟨fun old => outside (Or.inl old), fun root => outside (Or.inr root)⟩

#print axioms buffer_frame_object_frame
end Zlib.Uncompr.Proof.LocalFrame
