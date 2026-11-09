import ZlibF.Proof.«inflate.c.origin-history»
import ZlibF.Proof.«inflate.c.default-public-memory-witness»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The complete actual next-call memory result follows from selected
default histories, including arbitrary recovery and copy interleavings, dictionaries and
every read-only query. The stronger state and allocator are derived.
Independent format refinement and wider initialization configurations
remain separate obligations. -/
theorem DefaultOriginHistory.next_memory_contract {h : Heap} {r : ZStreamRef}
    (history : DefaultOriginHistory h r) (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ zs z s rc after stream state used output,
      r.get h = some z ∧ h.istates zs = some s ∧
      C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginHistory after r ∧ StreamReachable .inflate after r ∧
      DefaultOriginState after r zs stream state ∧ DefAlloc stream ∧
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
    inflate_default_origin_public_memory_contract current allocator buffers flush
  have continued := DefaultOriginHistory.step history (.inflate flush)
    ⟨buffers, current.active_header⟩ (heapCall_of_actual_run run default)
  exact ⟨zs, z, s, rc, after, stream, state, used, output, current.good.live.hz, current.good.live.hs,
    run, continued, continued.sound.2, next, nextAllocator, freed, account, observed, totals,
    progress, codes, memoryTotals, modes, frame, ledger⟩

#print axioms DefaultOriginHistory.next_memory_contract
/-- Real initialization, legal buffer replacement and a public inflate
call realize the complete selected history contract. The existing malformed
header witness is retained; this is not a successful decoding witness. -/
theorem default_origin_memory_history_witness :
    ∃ incoming after stream returned state used output rc,
      DefaultOriginHistory incoming (.tab 0) ∧ DefaultOriginHistory after (.tab 0) ∧
      C.run (Zlib.Inflate.inflate (some (.tab 0)) Z_FINISH) incoming = .ok (rc, after) ∧
      StreamAccounting stream returned used output.length ∧ Bytes after stream.next_out output.length output ∧
      BufferFrame incoming after
        (fun b => StreamRoot (.tab 0) b ∨ InflateOwned witnessHeap.nextBlk state b) [⟨stream.next_out, output.length⟩] := by
  obtain ⟨initialized, z, s, incoming, stream, rc, after, returned, state, used, output,
    initRun, _initial, edit, _reachable, incomingJ, _allocator, buffers, run, _current,
    account, observed, frame, _ledger⟩ := inflate_default_public_memory_witness
  have first := DefaultOriginHistory.init ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain
    inflate_default_witness_platform rfl initRun
  have before := DefaultOriginHistory.rebuffer first edit incomingJ.platform
  have final := DefaultOriginHistory.step before (.inflate Z_FINISH)
    ⟨buffers, incomingJ.active_header⟩ (heapCall_of_actual_run run default)
  exact ⟨incoming, after, stream, returned, s, used, output, rc, before, final, run, account, observed, frame⟩

#print axioms default_origin_memory_history_witness
end Zlib.Inflate.Proofs
