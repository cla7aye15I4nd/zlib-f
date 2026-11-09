import ZlibF.Proof.«deflate.c.engine.generic-all-scalar-history»
import ZlibF.Proof.«deflate.c.engine.observed-history-contract»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false
/-- Actual all-signed histories derive default allocator identity; legal caller
output views add no allocator or representation premise. -/
theorem GenericDefaultDataTrace.all_scalar_allocators {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : GenericDefaultDataTrace r h log) :
    ∃ z, r.get h = some z ∧ DefAlloc z := by
  induction history with
  | init domain actual => exact (DefaultDataTrace.init domain actual).allocators
  | caller _ edit ih =>
      obtain ⟨z, getZ, alloc⟩ := ih
      obtain ⟨_fresh, _uniq, _globals, _frame, old, next, getOld, getNext, fields⟩ := edit
      have same : old = z := Option.some.inj (getOld.symm.trans getZ)
      subst old
      refine ⟨next, getNext, ?_⟩
      rw [fields]
      exact alloc
  | step previous getZ observed ih =>
      obtain ⟨oldZ, getOld, alloc⟩ := ih
      obtain ⟨ds, current, d, config, protocol⟩ := previous.all_scalar_protocol
      have same : current = oldZ := Option.some.inj (protocol.good.live.hz.symm.trans getOld)
      subst current
      have oldEq : oldZ = _ := Option.some.inj (getOld.symm.trans getZ)
      subst oldZ
      obtain ⟨before, next, beforeGet, nextGet, buffers, _header, _snapshot, _used, _bytes, actual⟩ := observed
      have beforeEq : before = _ := Option.some.inj (beforeGet.symm.trans getZ)
      subst before
      obtain ⟨_used, _produced, _rc, computed, z', result, execution, stateA, _buffersA, accountA, _allowed⟩ :=
        protocol.generic_all_scalar_request buffers _
      have sameHeap := (Prod.mk.inj (Except.ok.inj (execution.symm.trans actual))).2
      subst computed
      rcases accountA with ⟨_, _, _, _, _, _, _, keepAlloc, keepFree, _, _⟩
      exact ⟨z', stateA.good.live.hz, keepAlloc.trans alloc.1, keepFree.trans alloc.2⟩


/-- Actual end releases the five owned objects after every signed-call observed history. -/
theorem GenericDefaultDataTrace.all_scalar_cleanup {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : GenericDefaultDataTrace r h log) :
    ∃ ds z d after, DGood h r ds z d ∧
      C.run (deflateEnd (some r)) h =
        .ok ((if d.status = BUSY_STATE then Z_DATA_ERROR else Z_OK), after) ∧
      r.get after = some { z with state := none } ∧
      LiveChange h after (fun _ => False) (DeflateOwned ds d) ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨ds, z, d, config, protocol⟩ := history.all_scalar_protocol
  obtain ⟨za, getA, allocators⟩ := history.all_scalar_allocators
  have same : za = z := Option.some.inj (getA.symm.trans protocol.good.live.hz)
  subst za
  obtain ⟨after, run, get, live, frame, count, next⟩ :=
    ZlibF.Spec.Public.DeflateEndProof.deflate_end_public h r ds z d protocol.good allocators.2
  exact ⟨ds, z, d, after, protocol.good, run, get, live, frame, count, next⟩


end Zlib.Deflate.Engine.Proofs
