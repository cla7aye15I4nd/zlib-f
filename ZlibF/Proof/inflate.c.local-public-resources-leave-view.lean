import ZlibF.Proof.«inflate.c.borrow-stable-leave»
import ZlibF.Proof.«inflate.c.local-public-state»
import ZlibF.Proof.«inflate.c.output-frame-footprint-compose»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The caller's admitted byte view is outside the stream and the incoming
owned decoder storage. Mutability does not change the ownership argument. -/
theorem caller_byte_root_outside_writing {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs off count b : Nat}
    {z : ZStream} {s : InflateState} {ref : BRef} {array : Array UInt8} {writing : Bool}
    (invariant : LocalStateJ h cutoff r zs z s) (get : Space.get h ref = some array)
    (range : CallerRange h r (.ref ref off) count writing) (root : ByteRoot (.ref ref off) b) :
    ¬ (StreamRoot r b ∨ InflateOwned zs s b) := by
  rcases range with null | ⟨_, _, outside⟩
  · cases null
  · rintro (stream | owned)
    · exact caller_byte_root_not_stream invariant get root stream
    · exact outside b root ((invariant.good.streamOwned_iff b).mpr owned)

/-- Private leave/window writes retain the caller's full output byte view
and its mutability, even when the output slice is empty. -/
theorem inflate_leave_output_view_unchanged {c : Ctx} {l : IL} {h after : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {bs : List UInt8} {rc : Int32} {ref : BRef} {off : Nat} {array : Array UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39)
    (run : inflate_leave c l h = .ok (rc, after)) (pointer : l.put = .ref ref off)
    (get : Space.get h ref = some array) :
    Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) ∧
    Space.get after ref = some array ∧ Space.ro after ref = Space.ro h ref := by
  have frame := inflate_leave_frame_local E invariant allocator buffers bits run
  have range : CallerRange h r (.ref ref off) l.left.toNat true := by rw [← pointer]; exact buffers.output.range
  have outside := fun b root => caller_byte_root_outside_writing invariant get range (b := b) root
  have stable := Zlib.Inflate.BorrowProofs.inflate_leave_borrow_stable c l h after rc run ref
  exact ⟨frame, frame_byte_view_get frame get outside stable, frame_byte_view_ro frame get outside⟩

#print axioms inflate_leave_output_view_unchanged
end Zlib.Inflate.Local
