import ZlibF.Proof.«inflate.c.default-public-output-bytes»
import ZlibF.Proof.«inflate.c.live-frame-public»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual complete default public call satisfies its scalar, output
observation, exact caller frame and allocation clauses on one returned heap.
The incoming initialized DefaultStateJ and public caller premises remain
explicit. This does not establish J for every StreamReachable history or
refine output bytes to the independent stream-format semantics. -/
theorem inflate_default_view_public_memory_contract
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ rc after stream state used output,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
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
  obtain ⟨rc, after, stream, state, used, made, run, current, finalAllocator, freed,
    _usedBound, _madeBound, account, totals, progress, codes, memoryTotals, modes, ledger⟩ :=
    inflate_default_view_public_resource_contract invariant allocator buffers flush
  obtain ⟨rc2, after2, stream2, state2, used2, output, run2, current2, _, _, account2, observed, frame⟩ :=
    inflate_default_view_public_output_bytes invariant allocator buffers flush
  have sameRun := Except.ok.inj (run2.symm.trans run)
  cases sameRun
  have sameStream : stream2 = stream := Option.some.inj (current2.good.live.hz.symm.trans current.good.live.hz)
  have sameState : state2 = state := Option.some.inj (current2.good.live.hs.symm.trans current.good.live.hs)
  subst stream2 state2
  have inputCount := account.2.2.1
  have inputCount2 := account2.2.2.1
  have sameUsed : used2 = used := by omega
  subst used2
  have outputCount := account.2.2.2.1
  have outputCount2 := account2.2.2.2.1
  have sameMade : made = output.length := by omega
  rw [sameMade] at totals progress
  refine ⟨rc, after, stream, state, used, output, run, current, finalAllocator, freed,
    account2, observed, totals, ?_, codes, memoryTotals, modes, frame, ledger⟩
  intro ok
  obtain ⟨changed, finish⟩ := progress ok
  refine ⟨?_, finish⟩
  rcases changed with input | produced
  · exact Or.inl input
  · exact Or.inr (fun empty => produced (by rw [empty]; rfl))

#print axioms inflate_default_view_public_memory_contract
end Zlib.Inflate.Proofs
