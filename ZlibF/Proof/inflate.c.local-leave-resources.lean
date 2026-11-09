import ZlibF.Proof.«inflate.c.local-leave-origin»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- All local return facts are attached to the same real leave execution.
This is a local physical invariant/resource result, not an independent
encoded-stream or decoded-history correctness claim. -/
theorem inflate_leave_local_resources {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (allocator : DefAlloc z) (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      LocalStateJ after cutoff r zs stream state ∧ DefAlloc stream ∧
      Frame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) ∧
      LiveChange h after (fun b => InflateOwned zs state b ∧ ¬ h.live b) (fun _ => False) ∧
      (let update := (s.wsize != 0 || (l.out_ != l.left && s.mode < BAD &&
        (s.mode < CHECK || c.flush != Z_FINISH))) = true
      after.nextBlk = h.nextBlk + (if update ∧ s.window = .null ∧ h.allocOk h.nalloc = true then 1 else 0) ∧
      after.nalloc = h.nalloc + (if update ∧ s.window = .null then 1 else 0) ∧
      (state.window = s.window ∨ (s.window = .null ∧ state.window = .ref (.blk h.nextBlk) 0))) := by
  obtain ⟨rc, after, stream, state, run, final, finalAllocator⟩ :=
    inflate_leave_local_state E invariant allocator buffers bits
  exact ⟨rc, after, stream, state, run, final, finalAllocator,
    inflate_leave_frame_local E invariant allocator buffers bits run,
    inflate_leave_live_local E invariant allocator buffers bits run final.good,
    inflate_leave_effects_local E invariant allocator buffers bits run final.good⟩

#print axioms inflate_leave_local_resources
end Zlib.Inflate.Local
