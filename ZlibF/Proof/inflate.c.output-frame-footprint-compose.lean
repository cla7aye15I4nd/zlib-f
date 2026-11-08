import ZlibF.Proof.«inflate.c.window-pointer-run»
import ZlibF.Proof.«inflate.c.caller-input-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem inflate_buffer_frame_mono {h after : Heap} {small large : Nat → Prop} {regions : List Region}
    (frame : BufferFrame h after small regions) (included : ∀ b, small b → large b) :
    BufferFrame h after large regions := ⟨inflate_frame_mono frame.1 included, frame.2⟩

/-- A whole-object frame and an unchanged output view give an exact frame
for any selected slice of that view, without treating private writes as output. -/
theorem frame_unchanged_view_buffer {h after : Heap} {changed : Nat → Prop}
    {ref : BRef} {array : Array UInt8} (frame : Frame h after changed)
    (get : Space.get h ref = some array) (unchanged : Space.get after ref = some array)
    (off count : Nat) : BufferFrame h after changed [⟨.ref ref off, count⟩] := by
  refine ⟨?_, ?_⟩
  · simpa only [restoreRegions, List.foldl_cons, List.foldl_nil, get,
      slow_byte_view_put_self unchanged] using frame
  · intro region member dest start old pointer oldGet
    have same : region = (⟨.ref ref off, count⟩ : Region) := by simpa only [List.mem_singleton] using member
    subst region
    have ptr : Ptr.ref ref off = Ptr.ref dest start := pointer
    cases ptr
    have oldEq : old = array := Option.some.inj (oldGet.symm.trans get)
    subst old
    exact ⟨array, unchanged, rfl, fun _ _ _ => rfl⟩

theorem frame_byte_view_ro {h after : Heap} {changed : Nat → Prop}
    {ref : BRef} {array : Array UInt8} {off : Nat}
    (frame : Frame h after changed) (get : Space.get h ref = some array)
    (outside : ∀ b, ByteRoot (.ref ref off) b → ¬ changed b) : Space.ro after ref = Space.ro h ref := by
  cases ref with
  | blk b =>
    have live : h.live b := by simp [Heap.live, show h.bytes b = some array from get]
    exact (frame.2.2.2.2.2 b live (outside b rfl)).2.2.2.2.2.2.2
  | dstate_depth _ | str _ | st_dist_code | st_length_code => rfl

/-- The caller's admitted byte view is outside the stream and the incoming
owned decoder storage. Mutability does not change the ownership argument. -/
theorem caller_byte_root_outside_writing {h : Heap} {r : ZStreamRef} {zs off count b : Nat}
    {z : ZStream} {s : InflateState} {ref : BRef} {array : Array UInt8} {writing : Bool}
    (good : Good h r zs z s) (get : Space.get h ref = some array)
    (range : CallerRange h r (.ref ref off) count writing) (root : ByteRoot (.ref ref off) b) :
    ¬ (StreamRoot r b ∨ InflateOwned zs s b) := by
  rcases range with null | ⟨_, _, outside⟩
  · cases null
  · rintro (stream | owned)
    · exact caller_byte_root_not_stream good get root stream
    · exact outside b root ((good.streamOwned_iff b).mpr owned)

/-- Private leave/window writes retain the caller's full output byte view
and its mutability, even when the output slice is empty. -/
theorem inflate_leave_output_view_unchanged {c : Ctx} {l : IL} {h after : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {rc : Int32} {ref : BRef} {off : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (run : inflate_leave c l h = .ok (rc, after)) (pointer : l.put = .ref ref off)
    (get : Space.get h ref = some array) :
    Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) ∧
    Space.get after ref = some array ∧ Space.ro after ref = Space.ro h ref := by
  have frame := inflate_leave_frame_public E invariant allocator buffers bits run
  have range : CallerRange h r (.ref ref off) l.left.toNat true := by rw [← pointer]; exact buffers.output.range
  have outside := fun b root => caller_byte_root_outside_writing invariant.good get range (b := b) root
  exact ⟨frame, frame_byte_view_get frame get outside, frame_byte_view_ro frame get outside⟩

end Zlib.Inflate.Proofs
