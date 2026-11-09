import ZlibF.Proof.«deflate.c.engine.common-initialized-data-history»
import ZlibF.Proof.«deflate.c.engine.common-initialized-storage»
/-! # Actual common-level histories retain library globals and allocator identities -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Initialization establishes default allocators and library tables;
actual ordinary calls preserve them on the same observed heap. Neither
fact is an extra caller assumption on the history. -/
theorem CommonInitializedDataTrace.environment {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonInitializedDataTrace r h log) :
    LibraryGlobals h ∧ ∃ z, r.get h = some z ∧ DefAlloc z := by
  induction history with
  | @init before after version level p domain params low high actual =>
      obtain ⟨zf, sf, state, initial⟩ := common_observed_initialization_encoding_state domain params low high actual
      obtain ⟨zi, si, goodI, allocI, freeI, _level, _strategy, _window, _hash, _wrap, _start,
        _look, _pending, _bits, _header, _totalIn, _totalOut, _message, frame, _live, _owned⟩ := initial
      have same : zi = zf := Option.some.inj (goodI.live.hz.symm.trans state.good.live.hz)
      subst zi
      exact ⟨frame.1.symm.trans domain.2.2.1, zf, state.good.live.hz, allocI, freeI⟩
  | caller _ edit ih =>
      obtain ⟨_globals, z, getZ, allocators⟩ := ih
      have original := edit
      obtain ⟨_fresh, _unique, globalsG, _frame, old, new, oldGet, newGet, fields⟩ := original
      have same : old = z := Option.some.inj (oldGet.symm.trans getZ)
      subst old
      refine ⟨globalsG, new, newGet, ?_⟩
      rw [fields]
      exact allocators
  | step previous get raw flag observed ih =>
      obtain ⟨globals, oldZ, getOld, allocators⟩ := ih
      obtain ⟨ds, z, d, config, state, _ended⟩ := previous.encoding
      have same : z = oldZ := Option.some.inj (state.good.live.hz.symm.trans getOld)
      subst z
      have sameOld : oldZ = _ := Option.some.inj (getOld.symm.trans get)
      subst oldZ
      have original := observed
      obtain ⟨beforeZ, _nextZ, beforeGet, _nextGet, buffers, _active, snapshot, _used, _bytes, actual⟩ := original
      have beforeSame : beforeZ = _ := Option.some.inj (beforeGet.symm.trans get)
      subst beforeZ
      obtain ⟨usedA, rcA, computed, z', result, written, run, stateA, _buffersA, accountA, _bytesA, _validA⟩ :=
        state.ordinary_encoding_request buffers raw _ flag snapshot
      have heaps := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
      subst computed
      have storage := state.ordinary_run_full_storage flag buffers raw actual
      have globalsA : LibraryGlobals _ := storage.2.1.1.symm.trans globals
      rcases accountA with ⟨_, _, _, _, _, _, _, keepAlloc, keepFree, _, _⟩
      exact ⟨globalsA, z', stateA.good.live.hz,
        keepAlloc.trans allocators.1, keepFree.trans allocators.2⟩

/-- End releases exactly the five owned objects after every scoped history,
including unfinished and error-returning histories. -/
theorem CommonInitializedDataTrace.cleanup {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonInitializedDataTrace r h log) :
    ∃ ds z d after, DGood h r ds z d ∧
      C.run (deflateEnd (some r)) h = .ok ((if d.status = BUSY_STATE then Z_DATA_ERROR else Z_OK), after) ∧
      r.get after = some {z with state := none} ∧
      LiveChange h after (fun _ => False) (DeflateOwned ds d) ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨ds, z, d, config, state, _valid⟩ := history.encoding
  obtain ⟨_globals, za, getA, allocators⟩ := history.environment
  have same : za = z := Option.some.inj (getA.symm.trans state.good.live.hz)
  subst za
  obtain ⟨after, run, get, live, frame, count, next⟩ :=
    ZlibF.Spec.Public.DeflateEndProof.deflate_end_public h r ds z d state.good allocators.2
  exact ⟨ds, z, d, after, state.good, run, get, live, frame, count, next⟩

end Zlib.Deflate.Engine.Proofs
