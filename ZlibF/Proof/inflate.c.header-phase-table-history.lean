import ZlibF.Proof.«inflate.c.header-phase-table-public»
import ZlibF.Proof.«inflate.c.header-counts-history»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- An actual first public TABLE waiting return, its subsequent actual
waiting/rebuffer history, and its completing read share the original
header count and the independently parsed alphabet. -/
theorem inflate_TABLE_header_wait_history_alphabet
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (initial : DefaultOriginState h r zs z s) (allocator : DefAlloc z)
    (buffers : StreamBuffers h r) (entry : EntryHeaderFacts h r s z) (nonnull : z.next_out ≠ .null)
    (inputValid : z.next_in = .null → z.avail_in = 0)
    (inputBytes : Bytes h z.next_in z.avail_in.toNat bs) (mode : s.mode = TABLE)
    (flush : Int32) :
    ∃ rc after stream0 state0 outcome pulled used,
      C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      DefaultOriginState after r zs stream0 state0 ∧ DefAlloc stream0 ∧
      after.bytes h.nextBlk = none ∧
      runX (NEEDBITS 14) (dispatchRegs z s) (syncAlloc h) = .ok ((outcome, pulled), syncAlloc h) ∧
      used ≤ bs.length ∧ BitInv (syncAlloc h) pulled (bs.drop used) ∧
      (outcome = .ok () →
        ¬ ((tableCounts s pulled.hold).nlen > 286 ∨ (tableCounts s pulled.hold).ndist > 30) →
        (Zlib.Inflate.Proofs.stream (tableRegs pulled) (bs.drop used)).length / 3 <
          (tableCounts s pulled.hold).ncode.toNat →
        ∀ last inputs outputs, LenlensWaitingTrace after r zs last inputs outputs →
        ∃ stream1 state, DefaultOriginState last r zs stream1 state ∧ DefAlloc stream1 ∧ outputs = [] ∧
          state.ncode = (tableCounts s pulled.hold).ncode ∧
          state.nlen = (tableCounts s pulled.hold).nlen ∧
          state.ndist = (tableCounts s pulled.hold).ndist ∧
          ∀ c nextBytes, c.strm = some r → c.st = some (.tab zs) → state.mode = LENLENS →
            Bytes last stream1.next_in stream1.avail_in.toNat nextBytes →
            3 * (state.ncode.toNat - state.«have».toNat) ≤
              (Zlib.Inflate.Proofs.stream (dispatchRegs stream1 state) nextBytes).length →
            ∃ regs consumed filled, consumed ≤ nextBytes.length ∧
              BitInv last regs (nextBytes.drop consumed) ∧ filled.WellFormed ∧ Good3 filled.lens 19 ∧
              runX (inflate_LENLENS c) (dispatchRegs stream1 state) last =
                runX (llTail c) regs (setI last zs filled) ∧
              ∀ future, readCodeLenLens (tableCounts s pulled.hold).ncode.toNat
                (((natBits (tableRegs pulled).bits.toNat (tableRegs pulled).hold.toNat ++
                  bytesBits (bs.drop used) ++ bytesBits inputs) ++ bytesBits (nextBytes.take consumed)) ++ future) = some
                (Zlib.Inftrees.Proofs.lensOf (fun k => (filled.lens.getD k 0).toNat) 19,
                  natBits regs.bits.toNat regs.hold.toNat ++ future)) := by
  obtain ⟨rc, after, stream0, state0, outcome, pulled, used, run, current, currentAllocator,
    freed, pull, bound, inv, accepted⟩ :=
    inflate_TABLE_header_wait_public_seed initial allocator buffers entry nonnull inputValid inputBytes mode flush
  refine ⟨rc, after, stream0, state0, outcome, pulled, used, run, current, currentAllocator,
    freed, pull, bound, inv, ?_⟩
  intro normal valid short last inputs outputs history
  obtain ⟨seed, code0, lit0, dist0, _fields⟩ := accepted normal valid short
  obtain ⟨stream1, state, final, finalAllocator, empty, code, lit, dist, alphabet⟩ :=
    history.alphabet_with_counts current currentAllocator seed
  refine ⟨stream1, state, final, finalAllocator, empty,
    code.trans code0, lit.trans lit0, dist.trans dist0, ?_⟩
  intro c nextBytes strmPtr statePtr finalMode nextInput enough
  obtain ⟨regs, consumed, filled, bound1, inv1, wf, good, cut, read⟩ :=
    alphabet c nextBytes strmPtr statePtr finalMode nextInput enough
  refine ⟨regs, consumed, filled, bound1, inv1, wf, good, cut, ?_⟩
  intro future
  have parsed := read future
  rw [code0] at parsed
  exact parsed

#print axioms inflate_TABLE_header_wait_history_alphabet

end Zlib.Inflate.Proofs
