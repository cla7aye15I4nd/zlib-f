import ZlibF.Proof.«inflate.c.default-extended-history»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual next-call memory result follows from selected
default histories, now including dictionaries and every read-only query.
J and allocator validity are derived. Recovery and copy histories and
independent format refinement remain separate open obligations. -/
theorem DefaultExtendedHistory.next_memory_contract {h : Heap} {r : ZStreamRef}
    (history : DefaultExtendedHistory h r) (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ zs z s rc after stream state used output,
      r.get h = some z ∧ h.istates zs = some s ∧
      C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultExtendedHistory after r ∧ StreamReachable .inflate after r ∧
      DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧
      after.bytes h.nextBlk = none ∧
      StreamAccounting z stream used output.length ∧ Bytes after z.next_out output.length output ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_DATA_ERROR ∨ rc = Z_BUF_ERROR →
        stream.total_in = z.total_in + UInt64.ofNat used ∧
        stream.total_out = z.total_out + UInt64.ofNat output.length) ∧
      (rc = Z_OK → (used ≠ 0 ∨ output ≠ []) ∧ flush ≠ Z_FINISH) ∧ PublicInflateCode rc ∧
      (rc = Z_MEM_ERROR → stream.total_in = z.total_in ∧ stream.total_out = z.total_out) ∧
      ReturnedModes rc state ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ InflateOwned zs s b) [⟨z.next_out, output.length⟩] ∧
      LiveChange h after (fun b => InflateOwned zs state b ∧ ¬ h.live b) (fun _ => False) := by
  obtain ⟨⟨zs, z, s, current, allocator⟩, _reachable⟩ := history.sound
  obtain ⟨rc, after, stream, state, used, output, run, next, nextAllocator, freed,
    account, observed, totals, progress, codes, memoryTotals, modes, frame, ledger⟩ :=
    inflate_default_view_public_memory_contract current allocator buffers flush
  have continued := DefaultExtendedHistory.step history (.inflate flush)
    ⟨buffers, current.active_header⟩ (heapCall_of_actual_run run default)
  exact ⟨zs, z, s, rc, after, stream, state, used, output, current.good.live.hz, current.good.live.hs,
    run, continued, continued.sound.2, next, nextAllocator, freed, account, observed, totals,
    progress, codes, memoryTotals, modes, frame, ledger⟩

#print axioms DefaultExtendedHistory.next_memory_contract
end Zlib.Inflate.Proofs
