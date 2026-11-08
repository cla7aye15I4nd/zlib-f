import ZlibF.Proof.«inflate.c.default-control-reachable»
import ZlibF.Proof.«inflate.c.default-public-memory-witness»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Derive the complete next-call memory contract from actual selected
initialization/control history. J is a conclusion of history induction,
not an incoming assumption. This selected relation still excludes Copy,
sync and dictionary operations; it does not establish the broad Goal.inflate. -/
theorem DefaultControlHistory.next_memory_contract {h : Heap} {r : ZStreamRef}
    (history : DefaultControlHistory h r) (buffers : StreamBuffers h r) (flush : Int32) :
    ∃ zs z s rc after stream state used output,
      r.get h = some z ∧ h.istates zs = some s ∧
      C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultControlHistory after r ∧ StreamReachable .inflate after r ∧
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
  obtain ⟨zs, z, s, current, allocator⟩ := history.invariant
  obtain ⟨rc, after, stream, state, used, output, run, next, nextAllocator, freed,
    account, observed, totals, progress, codes, memoryTotals, modes, frame, ledger⟩ :=
    inflate_default_view_public_memory_contract current allocator buffers flush
  have continued := DefaultControlHistory.inflate history buffers run
  exact ⟨zs, z, s, rc, after, stream, state, used, output, current.good.live.hz, current.good.live.hs,
    run, continued, continued.reachable, next, nextAllocator, freed, account, observed, totals,
    progress, codes, memoryTotals, modes, frame, ledger⟩

/-- Real default init, a legal rebuffer and an actual public request realize
the selected history contract. The input is the existing malformed-header
witness; no successful-decompression claim is made. -/
theorem default_control_memory_history_witness :
    ∃ incoming after stream returned state used output rc,
      DefaultControlHistory incoming (.tab 0) ∧ DefaultControlHistory after (.tab 0) ∧
      C.run (Zlib.Inflate.inflate (some (.tab 0)) Z_FINISH) incoming = .ok (rc, after) ∧
      StreamAccounting stream returned used output.length ∧ Bytes after stream.next_out output.length output ∧
      BufferFrame incoming after
        (fun b => StreamRoot (.tab 0) b ∨ InflateOwned witnessHeap.nextBlk state b) [⟨stream.next_out, output.length⟩] := by
  obtain ⟨initialized, z, s, incoming, stream, rc, after, returned, state, used, output,
    initRun, _initial, edit, _reachable, incomingJ, _allocator, buffers, run, _current,
    account, observed, frame, _ledger⟩ := inflate_default_public_memory_witness
  have first := DefaultControlHistory.init ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain
    inflate_default_witness_platform rfl initRun
  have bound := incomingJ.platform
  have before := DefaultControlHistory.rebuffer first edit bound
  have final := DefaultControlHistory.inflate before buffers run
  exact ⟨incoming, after, stream, returned, s, used, output, rc, before, final, run, account, observed, frame⟩

#print axioms DefaultControlHistory.next_memory_contract
#print axioms default_control_memory_history_witness
end Zlib.Inflate.Proofs
