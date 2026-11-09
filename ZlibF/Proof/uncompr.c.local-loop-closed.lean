import ZlibF.Proof.«uncompr.c.local-refill-post»
import ZlibF.Proof.«uncompr.c.local-loop-budget»
import ZlibF.Proof.«inflate.c.local-public-resources-frame-observer»

namespace Zlib.Uncompr.Proof.LocalLoop
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
set_option autoImplicit false

/-- The real refills and complete actual inflater preserve every premise
of the next outer iteration. Exact counts and strict OK progress belong to
this same call, including rejected input and partial output before failure. -/
theorem loop_iteration_closed (h : Heap) (cutoff b zs : Nat) (z : ZStream) (s : InflateState) (l : UncLoop)
    (invariant : LocalStateJ h cutoff (.tab b) zs z s) (allocator : DefAlloc z)
    (ranges : RemainingBuffers h b z l) (nonnull : z.next_out ≠ .null) :
    ∃ rc after stream state used made,
      C.run (loopBody (some (.tab b)) l) h = .ok ({ refilledLocals z l with err := rc }, after) ∧
      LocalStateJ after cutoff (.tab b) zs stream state ∧ DefAlloc stream ∧
      RemainingBuffers after b stream { refilledLocals z l with err := rc } ∧
      stream.next_out ≠ .null ∧
      ((refilledLocals z l).len.toNat + stream.avail_in.toNat) + used =
        l.len.toNat + z.avail_in.toNat ∧
      ((refilledLocals z l).left.toNat + stream.avail_out.toNat) + made =
        l.left.toNat + z.avail_out.toNat ∧
      (rc = Z_OK → used ≠ 0 ∨ made ≠ 0) ∧ PublicInflateCode rc := by
  obtain ⟨rc, after, stream, state, used, made, body, current, finalAllocator,
    account, codes, countIn, countOut, progress, strict⟩ :=
    loop_iteration_accounting h cutoff b zs z l s invariant allocator ranges.1 ranges.2.1 ranges.2.2
  have filledJ := refilledLocalStateJ h cutoff b zs z l s invariant
  have buffers := refilled_stream_buffers h b z l invariant.good.live.hz ranges.1 ranges.2.1 ranges.2.2
  have actual := (loopBody_inflate_run h b z l _ after invariant.good.live.hz body).1
  have frame := inflate_default_view_public_frame_of_run filledJ allocator buffers actual current.good account
  change BufferFrame (refilledHeap h b z l) after
    (fun x => StreamRoot (.tab b) x ∨ InflateOwned zs s x) [⟨z.next_out, made⟩] at frame
  obtain ⟨_, owners, _, _⟩ := loopBody_resources h after cutoff b zs z stream s state l _
    invariant allocator ranges body current.good
  have shape := shape_put (r := .tab b) invariant.good.live.hz (refilledStream z l)
  have stored : h.streams b = some z := invariant.good.live.hz
  have put : ZStreamRef.put h (.tab b) (refilledStream z l) = refilledHeap h b z l := by
    simp [ZStreamRef.put, stored, refilledHeap]
  rw [put] at shape
  have oldOwned (x : Nat) (live : (refilledHeap h b z l).live x)
      (owned : InflateOwned zs state x) : InflateOwned zs s x :=
    (owners x ((shape.live x).mp live)).mp owned
  obtain ⟨remaining, finalNonnull, _, _⟩ :=
    remaining_ranges_of_account_frame h after cutoff b zs z stream s state l rc used made made
      invariant current ranges nonnull account frame oldOwned
  exact ⟨rc, after, stream, state, used, made, body, current, finalAllocator,
    remaining, finalNonnull, countIn, countOut, progress, codes⟩

#print axioms loop_iteration_closed
end Zlib.Uncompr.Proof.LocalLoop
