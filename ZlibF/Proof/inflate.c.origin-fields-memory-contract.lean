import ZlibF.Proof.«inflate.c.origin-fields-public»
import ZlibF.Proof.«inflate.c.default-public-memory-contract»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual complete default public call satisfies its scalar, output
observation, exact caller frame and allocation clauses on one returned heap.
The incoming initialized DefaultOriginState and public caller premises remain
explicit. This does not establish the invariant for every StreamReachable history or
refine output bytes to the independent stream-format semantics. -/
theorem inflate_default_origin_public_memory_contract
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (entry : EntryHeaderFacts h r s z) (flush : Int32) :
    ∃ rc after stream state used output,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧
      StreamAccounting z stream used output.length ∧ Bytes after z.next_out output.length output ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        stream.total_in = z.total_in + UInt64.ofNat used ∧
        stream.total_out = z.total_out + UInt64.ofNat output.length) ∧
      (rc = Z_OK → (used ≠ 0 ∨ output ≠ []) ∧ flush ≠ Z_FINISH) ∧
      PublicInflateCode rc ∧
      (rc = Z_MEM_ERROR → stream.total_in = z.total_in ∧ stream.total_out = z.total_out) ∧
      ReturnedModes rc state ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) [⟨z.next_out, output.length⟩] ∧
      LiveChange h after (fun b => InflateOwned zs state b ∧ ¬ h.live b) (fun _ => False) := by
  obtain ⟨rc, after, stream, state, used, output, run, current, rest⟩ :=
    inflate_default_view_public_memory_contract invariant.toDefaultStateJ allocator buffers entry flush
  obtain ⟨rc2, after2, stream2, state2, actual, origins, _, _⟩ :=
    inflate_default_origin_state_safe invariant allocator buffers entry flush
  have same := Except.ok.inj (actual.symm.trans run)
  cases same
  have sameStream : stream2 = stream := Option.some.inj (origins.good.live.hz.symm.trans current.good.live.hz)
  have sameState : state2 = state := Option.some.inj (origins.good.live.hs.symm.trans current.good.live.hs)
  subst stream2 state2
  exact ⟨rc, after, stream, state, used, output, run, origins, rest⟩

#print axioms inflate_default_origin_public_memory_contract
end Zlib.Inflate.Proofs
