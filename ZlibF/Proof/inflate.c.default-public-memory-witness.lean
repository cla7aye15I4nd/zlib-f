import ZlibF.Proof.«inflate.c.default-public-memory-contract»
import ZlibF.Proof.«inflate.c.default-view-witness»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual default initialization and a legal caller rebuffer realize the
full memory contract's domain. The same returning public call supplies
its observed bytes, exact caller frame and owned allocation ledger. -/
theorem inflate_default_public_memory_witness :
    ∃ initialized z s incoming stream rc after finalStream finalState used output,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, initialized) ∧
      DefaultStateJ initialized (.tab 0) witnessHeap.nextBlk z s ∧
      Rebuffer initialized incoming (.tab 0) ∧ StreamReachable .inflate incoming (.tab 0) ∧
      DefaultStateJ incoming (.tab 0) witnessHeap.nextBlk stream s ∧ DefAlloc stream ∧
      StreamBuffers incoming (.tab 0) ∧
      C.run (inflate (some (.tab 0)) Z_FINISH) incoming = .ok (rc, after) ∧
      DefaultStateJ after (.tab 0) witnessHeap.nextBlk finalStream finalState ∧
      StreamAccounting stream finalStream used output.length ∧
      Bytes after stream.next_out output.length output ∧
      BufferFrame incoming after (fun b => StreamRoot (.tab 0) b ∨ InflateOwned witnessHeap.nextBlk s b ∨
          s.head = some (.tab b))
        (⟨stream.next_out, output.length⟩ :: HeaderRegions incoming s.head) ∧
      LiveChange incoming after
        (fun b => InflateOwned witnessHeap.nextBlk finalState b ∧ ¬ incoming.live b) (fun _ => False) := by
  obtain ⟨initialized, z, s, incoming, stream, _rc, _after, _finalStream, _finalState,
    initRun, initial, _streamEq, _heapEq, invariant, allocator, headNone, buffers, edit, reachable, _⟩ :=
    inflate_default_view_state_witness
  have entry : EntryHeaderFacts incoming (.tab 0) s stream := EntryHeaderFacts.of_none headNone
  obtain ⟨rc, after, finalStream, finalState, used, output, run, current, _, _, account,
    observed, _, _, _, _, _, frame, ledger⟩ :=
    inflate_default_view_public_memory_contract invariant allocator buffers entry (Or.inl headNone) Z_FINISH
  exact ⟨initialized, z, s, incoming, stream, rc, after, finalStream, finalState, used, output,
    initRun, initial, edit, reachable, invariant, allocator, buffers, run, current, account, observed, frame, ledger⟩

#print axioms inflate_default_public_memory_witness
end Zlib.Inflate.Proofs
