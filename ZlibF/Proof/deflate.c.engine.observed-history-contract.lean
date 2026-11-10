import ZlibF.Proof.«deflate.c.engine.encoding-all-scalar-history»
import ZlibF.Proof.«public-deflate-end»
import ZlibF.Proof.«deflate.c.engine.all-scalar-request-contract»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Default allocators are conclusions of actual init and every data
transition, including errors. They are not extra history premises. -/
theorem DefaultDataTrace.allocators {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) :
    ∃ z, r.get h = some z ∧ DefAlloc z := by
  induction history with
  | @init before after version domain actual =>
      obtain ⟨hf, hu, hg, hv, z, hz, ha, _null⟩ := domain
      have allocation := default_init_success_allocations hf hu hg hz ha hv actual
      obtain ⟨rc, computed, execution, properties⟩ :=
        (ZlibF.Spec.Public.Proofs.DeflateInit.deflateInit_proof Z_DEFAULT_COMPRESSION).2.2
          _ r z _ hf hu hg hz ha hv
      obtain ⟨_code, heaps⟩ := Prod.mk.inj (Except.ok.inj (execution.symm.trans actual))
      rw [heaps] at properties
      have first : before.allocOk before.nalloc ≠ false := by
        have zero : before.allocOk before.nalloc = true := by
          simpa only [Nat.add_zero] using allocation 0 (by decide)
        rw [zero]
        decide
      have all : (List.range 5).all (fun j => before.allocOk (before.nalloc + j)) = true := by
        simpa only [List.all_eq_true, List.mem_range] using allocation
      simp only [ite_eq_right first, ite_eq_left all] at properties
      obtain ⟨zf, sf, good, alloc, free, _rest⟩ := properties.2.2
      exact ⟨zf, good.live.hz, alloc, free⟩
  | caller _ edit ih =>
      obtain ⟨z, getZ, alloc⟩ := ih
      obtain ⟨_fresh, _uniq, _globals, _frame, old, next, getOld, getNext, fields⟩ := edit
      have same : old = z := Option.some.inj (getOld.symm.trans getZ)
      subst old
      refine ⟨next, getNext, ?_⟩
      rw [fields]
      exact alloc
  | step previous getZ raw observed ih =>
      obtain ⟨oldZ, getOld, alloc⟩ := ih
      obtain ⟨ds, current, d, config, protocol⟩ := previous.protocol
      have same : current = oldZ := Option.some.inj (protocol.good.live.hz.symm.trans getOld)
      subst current
      have oldEq : oldZ = _ := Option.some.inj (getOld.symm.trans getZ)
      subst oldZ
      obtain ⟨before, next, beforeGet, nextGet, buffers, _header, _snapshot, _used, _bytes, actual⟩ := observed
      have beforeEq : before = _ := Option.some.inj (beforeGet.symm.trans getZ)
      subst before
      obtain ⟨_used, _produced, _rc, computed, z', result, execution, stateA, _buffersA, accountA, _allowed⟩ :=
        protocol.all_scalar_request buffers raw _
      have sameHeap := (Prod.mk.inj (Except.ok.inj (execution.symm.trans actual))).2
      subst computed
      rcases accountA with ⟨_, _, _, _, _, _, _, keepAlloc, keepFree, _, _⟩
      exact ⟨z', stateA.good.live.hz, keepAlloc.trans alloc.1, keepFree.trans alloc.2⟩

/-- Every scoped actual data history, including unfinished/error histories,
can release exactly its five owned allocations with the public end result,
caller frame and allocation counters. No allocator or invariant premise
is added to that history. -/
theorem DefaultDataTrace.cleanup {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) :
    ∃ ds z d after, DGood h r ds z d ∧
      C.run (deflateEnd (some r)) h =
        .ok ((if d.status = BUSY_STATE then Z_DATA_ERROR else Z_OK), after) ∧
      r.get after = some { z with state := none } ∧
      LiveChange h after (fun _ => False) (DeflateOwned ds d) ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨ds, z, d, config, protocol⟩ := history.protocol
  obtain ⟨za, getA, allocators⟩ := history.allocators
  have same : za = z := Option.some.inj (getA.symm.trans protocol.good.live.hz)
  subst za
  obtain ⟨after, run, get, live, frame, count, next⟩ :=
    ZlibF.Spec.Public.DeflateEndProof.deflate_end_public h r ds z d protocol.good allocators.2
  exact ⟨ds, z, d, after, protocol.good, run, get, live, frame, count, next⟩

/-- After each actual scoped data history, the next signed request has
encoding, safety, exact counters and heap frame on one and the same run.
The input snapshot is the current admitted readable caller range, not
a callee contract or a chosen logical encoding input. -/
theorem DefaultDataTrace.next_encoding_contract {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) :
    ∃ ds z d config, DefaultEncodingState h r ds z d config log.input log.output ∧
      ∀ flush, StreamBuffers h r →
        (z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) →
        ∀ input, Bytes h z.next_in z.avail_in.toNat input →
        ∃ used written rc after z' result,
          C.run (deflate (some r) flush) h = .ok (rc, after) ∧
          DefaultEncodingState after r ds z' result config
            (log.input ++ input.take used) (log.output ++ written) ∧
          StreamBuffers after r ∧ DGood after r ds z' result ∧
          StreamAccounting z z' used written.length ∧
          Bytes after z.next_out written.length written ∧
          z'.total_in = z.total_in + UInt64.ofNat used ∧
          z'.total_out = z.total_out + UInt64.ofNat written.length ∧
          (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
          (rc = Z_STREAM_ERROR ↔ flush.toInt < 0 ∨ 5 < flush.toInt ∨ z.next_out = .null ∨
            (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) ∧
          (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
          (rc = Z_STREAM_END → flush = Z_FINISH ∧ result.status = FINISH_STATE ∧
            z'.avail_in = 0 ∧ result.pending = 0 ∧ result.bi_valid = 0) ∧
          (rc = Z_STREAM_END → ZlibF.Spec.Zlib.Valid (log.input ++ input.take used) (log.output ++ written)) ∧
          Shape h after ∧
          BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] ∧
          LiveChange h after (fun _ => False) (fun _ => False) ∧
          after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨ds, z, d, config, state, _ended⟩ := history.encoding
  refine ⟨ds, z, d, config, state, ?_⟩
  intro flush buffers raw input snapshot
  obtain ⟨used, rc, after, z', result, written, run, stateA, buffersA, accountA, bytesA, endedA⟩ :=
    state.scalar_encoding_request buffers raw flush snapshot
  obtain ⟨usedC, writtenC, rcC, afterC, zC, resultC, runC, _protocolC, _buffersC, goodC,
      accountC, bytesC, inC, outC, allowed, errors, invalid, terminal, shape, frame, live, alloc, next⟩ :=
    state.protocol.all_scalar_request_contract flush buffers raw
  obtain ⟨code, heaps⟩ := Prod.mk.inj (Except.ok.inj (runC.symm.trans run))
  subst rcC afterC
  have streams : zC = z' := Option.some.inj (goodC.live.hz.symm.trans stateA.protocol.good.live.hz)
  have states : resultC = result := Option.some.inj (goodC.live.hs.symm.trans stateA.protocol.good.live.hs)
  subst zC resultC
  obtain ⟨usedEq, lengthEq⟩ := stream_accounting_counts_unique accountA accountC
  have writtenEq : written = writtenC := observed_bytes_unique bytesA (by rw [lengthEq]; exact bytesC)
  subst usedC writtenC
  exact ⟨used, written, rc, after, z', result, run, stateA, buffersA, goodC, accountA, bytesA,
    inC, outC, allowed, errors, invalid, terminal, endedA, shape, frame, live, alloc, next⟩

end Zlib.Deflate.Engine.Proofs
