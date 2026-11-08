import ZlibF.Spec.Public.DeflateCore
import ZlibF.Proof.«deflate.c.engine.observed-history-contract»
import ZlibF.Proof.«deflate.c.engine.all-scalar-history»

/-! # Existing actual default executions discharge the separated core clauses -/

namespace ZlibF.Spec.Public.Proofs.DeflateCore
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- A public pure call history is exactly an initialized actual scalar
request history. All signed flags and pointer refusals are retained. -/
theorem calls_to_internal {h : Heap} {r : ZStreamRef}
    (history : DeflateCore.Calls r h) :
    ∃ before initialized version, InitDomain before r version ∧
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) before =
        .ok (Z_OK, initialized) ∧
      DefaultScalarRequests r before.nextBlk initialized h := by
  induction history with
  | @init before initialized version domain actual =>
      exact ⟨before, initialized, version, domain, actual, .refl initialized⟩
  | caller _ edit ih =>
      obtain ⟨before, initialized, version, domain, actual, requests⟩ := ih
      exact ⟨before, initialized, version, domain, actual, .rebuffer requests edit⟩
  | step _ getZ buffers raw actual ih =>
      obtain ⟨before, initialized, version, domain, initial, requests⟩ := ih
      exact ⟨before, initialized, version, domain, initial,
        .step requests getZ buffers raw actual⟩

/-- The inverse bridge assumes only an actual successful initialization,
then records the same rebuffering and real returning scalar requests. -/
theorem calls_from_internal {before initialized h : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain before r version)
    (actual : C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) before =
      .ok (Z_OK, initialized))
    (history : DefaultScalarRequests r before.nextBlk initialized h) : DeflateCore.Calls r h := by
  induction history with
  | refl => exact .init domain actual
  | rebuffer _ edit ih => exact .caller ih edit
  | step _ getZ buffers raw actual ih => exact .step ih getZ buffers raw actual

/-- Actual initialization supplies the private boundary for all pure
call histories; it is never a public caller premise. -/
theorem calls_boundary {h : Heap} {r : ZStreamRef}
    (history : DeflateCore.Calls r h) :
    ∃ ds z d config, DefaultFinishBoundary h r ds z d config := by
  obtain ⟨before, initialized, version, domain, actual, requests⟩ := calls_to_internal history
  obtain ⟨fresh, unique, globals, versionValue, z, getZ, allocators, _null⟩ := domain
  obtain ⟨zf, df, initial⟩ := observed_default_init_encoding_state
    fresh unique globals getZ allocators versionValue actual
  obtain ⟨z', d', final⟩ := requests.preserves initial.protocol
  exact ⟨before.nextBlk, z', d', engineConfig df, final⟩

/-- Default allocator identity is established by actual initialization and
retained through every actual returning request, including refusals. -/
theorem calls_allocators {h : Heap} {r : ZStreamRef}
    (history : DeflateCore.Calls r h) : ∃ z, r.get h = some z ∧ DefAlloc z := by
  induction history with
  | init domain actual => exact (DefaultDataTrace.init domain actual).allocators
  | caller _ edit ih =>
      obtain ⟨z, getZ, alloc⟩ := ih
      obtain ⟨_fresh, _unique, _globals, _frame, old, next, getOld, getNext, fields⟩ := edit
      have same : old = z := Option.some.inj (getOld.symm.trans getZ)
      subst old
      refine ⟨next, getNext, ?_⟩
      rw [fields]
      exact alloc
  | step previous getZ buffers raw actual ih =>
      obtain ⟨old, getOld, alloc⟩ := ih
      obtain ⟨ds, z, d, config, boundary⟩ := calls_boundary previous
      have same : z = old := Option.some.inj (boundary.good.live.hz.symm.trans getOld)
      subst z
      have inputSame : old = _ := Option.some.inj (getOld.symm.trans getZ)
      subst old
      obtain ⟨_used, _written, _rc, after, z', result, run, next, _buffers, account, _allowed⟩ :=
        boundary.all_scalar_request buffers raw _
      have sameHeap := (Prod.mk.inj (Except.ok.inj (run.symm.trans actual))).2
      subst after
      rcases account with ⟨_, _, _, _, _, _, _, keepAlloc, keepFree, _, _⟩
      exact ⟨z', next.good.live.hz, keepAlloc.trans alloc.1, keepFree.trans alloc.2⟩

/-- The public ordinary trace and the existing internal observed trace have
identical actual constructors and exact observed logs. -/
theorem to_internal {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DeflateCore.Trace r h log) : DefaultDataTrace r h log := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ getZ raw actual ih => exact .step ih getZ raw actual

/-- No actual signed request or error-returning internal trace is discarded
by the public ordinary trace. -/
theorem from_internal {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DefaultDataTrace r h log) : DeflateCore.Trace r h log := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ getZ raw actual ih => exact .step ih getZ raw actual

theorem trace_iff {h : Heap} {r : ZStreamRef} {log : DataLog} :
    DeflateCore.Trace r h log ↔ DefaultDataTrace r h log :=
  ⟨to_internal, from_internal⟩

/-- Every readable-data history is a pure safety history, while pure
histories also admit null-input refusals that lack a byte snapshot. -/
theorem trace_calls {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DeflateCore.Trace r h log) : DeflateCore.Calls r h := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ getZ raw observed ih =>
      obtain ⟨_before, _next, _getBefore, _getNext, buffers, _header, _input, _used, _output, actual⟩ := observed
      exact .step ih getZ buffers raw actual

/-- This milestone is contained in the unchanged general data trace,
without changing any existing caller domain or public target. -/
theorem public_trace {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : DeflateCore.Trace r h log) :
    DeflateDataTrace Z_DEFAULT_COMPRESSION Z_DEFLATED MAX_WBITS DEF_MEM_LEVEL
      Z_DEFAULT_STRATEGY r h log :=
  (to_internal history).public_trace

/-- Version/parameter refusals and every default allocation outcome are
covered by the existing exact initialization proof, independently of data traces. -/
theorem initialization : DeflateCore.Initialization :=
  DeflateInit.deflateInit_proof Z_DEFAULT_COMPRESSION

/-- The separated successful-history domain has a concrete actual-init
witness. This supplements universal initialization, including its failures. -/
theorem initialized_trace_witness :
    ∃ after, DeflateCore.Trace (.tab 0) after {} ∧ DeflateCore.Calls (.tab 0) after := by
  obtain ⟨after, actual, _initial⟩ := DeflateInit.default_init_witness
  have domain : InitDomain DeflateInit.witnessHeap (.tab 0) (.ref (.blk 1) 0) := by
    refine ⟨DeflateInit.witness_fresh, DeflateInit.witness_uniq, rfl,
      DeflateInit.witness_version, default, ?_, ⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩
    simp [ZStreamRef.get, DeflateInit.witnessHeap]
  exact ⟨after, .init domain actual, .init domain actual⟩

/-- Actual next-call safety, exact counters and public frame are
transported together. Neither the boundary nor a callee contract is assumed
by the new public proposition. -/
theorem requests : DeflateCore.Requests := by
  intro h r history
  obtain ⟨ds, z, d, config, state⟩ := calls_boundary history
  obtain ⟨za, getA, alloc⟩ := calls_allocators history
  have same : za = z := Option.some.inj (getA.symm.trans state.good.live.hz)
  subst za
  refine ⟨ds, z, d, state.good, alloc, ?_⟩
  intro flush buffers raw
  obtain ⟨used, written, rc, after, z', result, run, _boundary, buffersA, goodA,
    account, bytes, inputTotal, outputTotal, allowed, errors, invalid, terminal,
    _shape, frame, live, count, frontier⟩ := state.all_scalar_request_contract flush buffers raw
  exact ⟨used, written, rc, after, z', result, run, buffersA, goodA, account,
    bytes, inputTotal, outputTotal, allowed, errors, invalid, terminal,
    frame, live, count, frontier⟩

/-- Completed-output correctness is separate from the existence of a
completion. No capacity-bound theorem is used. -/
theorem completed_encoding : DeflateCore.CompletedEncoding := by
  intro h r log history ended
  obtain ⟨_ds, _z, _d, _config, _state, valid⟩ := (to_internal history).encoding
  exact valid ended

/-- Actual end execution after every scoped ordinary history releases the
exact owned allocations, including unfinished and error histories. -/
theorem cleanup : DeflateCore.Cleanup := by
  intro h r history
  obtain ⟨ds, z, d, config, boundary⟩ := calls_boundary history
  obtain ⟨za, getA, alloc⟩ := calls_allocators history
  have same : za = z := Option.some.inj (getA.symm.trans boundary.good.live.hz)
  subst za
  obtain ⟨after, run, get, live, frame, count, next⟩ :=
    DeflateEndProof.deflate_end_public h r ds z d boundary.good alloc.2
  exact ⟨ds, z, d, after, boundary.good, run, get, live, frame, count, next⟩

/-- Initialization, next-call totality, completed-output correctness and
cleanup already have separate execution proofs. This theorem asserts no
ordinary-completion result and no deflateBound guarantee. -/
theorem safe_encoding_and_cleanup : DeflateCore.SafeEncodingAndCleanup :=
  ⟨initialization, requests, completed_encoding, cleanup⟩

/-- Every finite legal finishing continuation extends the same ordinary
trace. Its fixed source condition cannot be replaced by a chosen empty input. -/
theorem continuation_trace {r : ZStreamRef} {accepted source : List UInt8}
    {h after : Heap} {log finalLog : DataLog}
    (history : DeflateCore.Trace r h log)
    (continuation : DeflateCore.FinishContinuation r accepted source h log after finalLog) :
    DeflateCore.Trace r after finalLog := by
  induction continuation with
  | refl => exact history
  | caller _ edit ih => exact .caller ih edit
  | step _ getZ raw _positive _protocol _source observed ih =>
      exact .step ih getZ (Or.inr raw) observed

end ZlibF.Spec.Public.Proofs.DeflateCore
