import ZlibF.Proof.«deflate.c.engine.common-encoded-history»
import ZlibF.Proof.«deflate.c.engine.common-request-storage»
import ZlibF.Proof.«deflate.c.engine.common-initial-completes»

/-! # Actual common-level histories retain library globals and allocator identities -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Initialization establishes default allocators and library tables;
actual ordinary calls preserve them on the same observed heap. Neither
fact is an extra caller assumption on the history. -/
theorem CommonDataTrace.environment {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonDataTrace r h log) :
    LibraryGlobals h ∧ ∃ z, r.get h = some z ∧ DefAlloc z := by
  induction history with
  | @first before initialized h after version level p z ob oo flush rc input output used
      domain params low high actual edit get pointer one flagLow flagHigh observed =>
      obtain ⟨zf, sf, start, initial, first⟩ := common_observed_initialization_protocol domain params low high actual
      have allocators : DefAlloc zf := by
        obtain ⟨zi, _si, goodI, allocI, freeI, _rest⟩ := initial
        have same : zi = zf := Option.some.inj (goodI.live.hz.symm.trans start.good.live.hz)
        subst zi
        exact ⟨allocI, freeI⟩
      have header := initial_no_header start initial
      obtain ⟨zg, getG, next⟩ := first h edit
      obtain ⟨zs, startG⟩ := rebuffer_engine_start start edit header
      have sameS : zs = z := Option.some.inj (startG.good.live.hz.symm.trans get)
      have sameG : zg = z := Option.some.inj (getG.symm.trans get)
      subst zs zg
      have allocatorsG : DefAlloc z := by
        obtain ⟨_fresh, _unique, _globals, _frame, old, new, oldGet, newGet, fields⟩ := edit
        have sameOld : old = zf := Option.some.inj (oldGet.symm.trans start.good.live.hz)
        have sameNew : new = z := Option.some.inj (newGet.symm.trans get)
        subst old new
        rw [fields]
        exact allocators
      have original := observed
      obtain ⟨oldZ, _nextZ, oldGet, _nextGet, buffers, _active, snapshot, _used, _bytes, _run⟩ := original
      have oldSame : oldZ = z := Option.some.inj (oldGet.symm.trans get)
      subst oldZ
      have valid := ZlibF.Spec.Public.Proofs.DeflateCore.snapshot_input_valid snapshot
      obtain ⟨computed, z', result, run, protocolA, _buffersA, accountA⟩ :=
        next ob oo pointer one buffers valid flush flagLow flagHigh
      have heaps := (Prod.mk.inj (Except.ok.inj (run.symm.trans _run))).2
      subst computed
      have finishRun : deflate (some r) Z_FINISH h = .ok (Z_OK, after) :=
        (first_common_valid_one_eq_finish startG buffers pointer one valid flush flagLow flagHigh).symm.trans run
      have world := first_common_finish_one_world startG buffers pointer one valid edit.2.2.1 finishRun protocolA.good.live.hs
      rcases accountA with ⟨_, _, _, _, _, _, _, keepAlloc, keepFree, _, _⟩
      exact ⟨world.1, z', protocolA.good.live.hz,
        keepAlloc.trans allocatorsG.1, keepFree.trans allocatorsG.2⟩
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
      have same : z = oldZ := Option.some.inj (state.protocol.good.live.hz.symm.trans getOld)
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
      have storage := state.protocol.ordinary_run_full_storage flag buffers raw actual
      have globalsA : LibraryGlobals _ := storage.2.1.1.symm.trans globals
      rcases accountA with ⟨_, _, _, _, _, _, _, keepAlloc, keepFree, _, _⟩
      exact ⟨globalsA, z', stateA.protocol.good.live.hz,
        keepAlloc.trans allocators.1, keepFree.trans allocators.2⟩

/-- End releases exactly the five owned objects after every scoped history,
including unfinished and error-returning histories. -/
theorem CommonDataTrace.cleanup {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : CommonDataTrace r h log) :
    ∃ ds z d after, DGood h r ds z d ∧
      C.run (deflateEnd (some r)) h = .ok ((if d.status = BUSY_STATE then Z_DATA_ERROR else Z_OK), after) ∧
      r.get after = some {z with state := none} ∧
      LiveChange h after (fun _ => False) (DeflateOwned ds d) ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨ds, z, d, config, state, _valid⟩ := history.encoding
  obtain ⟨_globals, za, getA, allocators⟩ := history.environment
  have same : za = z := Option.some.inj (getA.symm.trans state.protocol.good.live.hz)
  subst za
  obtain ⟨after, run, get, live, frame, count, next⟩ :=
    ZlibF.Spec.Public.DeflateEndProof.deflate_end_public h r ds z d state.protocol.good allocators.2
  exact ⟨ds, z, d, after, state.protocol.good, run, get, live, frame, count, next⟩

end Zlib.Deflate.Engine.Proofs
