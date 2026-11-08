import ZlibF.Proof.«deflate.c.default-core»
import ZlibF.Proof.«deflate.c.engine.finish-input-progress»

/-! # Actual FINISH observations retain the fixed remaining source -/

namespace ZlibF.Spec.Public.Proofs.DeflateCore
open C ZlibF.Spec ZlibF.Spec.Public
open Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- Finite real continuations compose with the same fixed original source.
Their source and no-new-input guards are retained at every actual step. -/
theorem finish_continuation_trans {r : ZStreamRef} {accepted source : List UInt8}
    {start middle after : Heap} {initial current final : DataLog}
    (first : DeflateCore.FinishContinuation r accepted source start initial middle current)
    (second : DeflateCore.FinishContinuation r accepted source middle current after final) :
    DeflateCore.FinishContinuation r accepted source start initial after final := by
  induction second with
  | refl => exact first
  | caller _ edit ih => exact .caller ih edit
  | step _ get pointer positive protocol remaining observed ih =>
      exact .step ih get pointer positive protocol remaining observed

/-- The log and unread suffix use one cumulative source index. -/
theorem finish_log_source_progress {accepted source : List UInt8} {log : DataLog}
    {consumed used : Nat} (acceptedPrefix : log.input = accepted ++ source.take consumed)
    (written : List UInt8) (rc : Int32) :
    (DeflateCore.advanceLog log Z_FINISH rc (source.drop consumed) written used).input =
      accepted ++ source.take (consumed + used) := by
  change log.input ++ (source.drop consumed).take used = _
  rw [acceptedPrefix, List.append_assoc, ← List.take_add]

/-- A readable input snapshot implies the actual null-input entry guard. -/
theorem snapshot_input_valid {h : Heap} {z : ZStream} {input : List UInt8}
    (snapshot : Bytes h z.next_in z.avail_in.toNat input) :
    z.avail_in ≠ 0 → z.next_in ≠ .null := by
  intro nonzero null
  rcases snapshot with ⟨_pointer, zero, _input⟩ | ⟨_ref, _off, _array, pointer, _get, _fit, _value⟩
  · exact nonzero (UInt32.toNat_inj.mp zero)
  · rw [null] at pointer
    cases pointer

/-- The continuation's quantified FINISH input guard follows from the
actual private state and the unchanged readable snapshot. -/
theorem finish_snapshot_protocol {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {input : List UInt8}
    (good : DGood h r ds z d) (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0) :
    ∀ id state, z.state = some (.deflate id) → h.dstates id = some state →
      state.status = FINISH_STATE → input = [] := by
  intro id state kind live status
  have ids : ds = id := by
    simpa only [good.live.zst, Option.some.injEq, StateRef.deflate.injEq] using kind
  subst id
  have states : state = d := Option.some.inj (live.symm.trans good.live.hs)
  subst state
  have length := caller_bytes_length snapshot
  rw [accepted status] at length
  exact List.eq_nil_iff_length_eq_zero.mpr length

/-- Observe the same actual FINISH run and retain its exact input suffix.
Accounting and output observations are derived from the proved execution,
including when this is the one-byte first-header call. -/
theorem finish_run_observed {h after : Heap} {r : ZStreamRef} {ds ob oo used produced : Nat}
    {z z' : ZStream} {d : DeflateState} {config : EngineConfig} {input : List UInt8} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (actual : deflate (some r) Z_FINISH h = .ok (rc, after)) (get : r.get after = some z')
    (account : StreamAccounting z z' used produced) :
    ∃ written, DataStep .deflate h after r Z_FINISH rc input written used ∧
      StreamAccounting z z' used written.length ∧
      Bytes after z'.next_in z'.avail_in.toNat (input.drop used) := by
  obtain ⟨usedC, written, rcC, afterC, zC, _resultC, actualC, boundaryC, _buffersC, _goodC,
      accountC, bytesC, _inC, _outC, _allowedC, _errorsC, _invalidC, _terminalC,
      _shapeC, _frameC, _liveC, _allocC, _nextC⟩ :=
    boundary.all_scalar_request_contract Z_FINISH buffers (Or.inr ⟨ob, oo, pointer⟩)
  obtain ⟨code, heaps⟩ := Prod.mk.inj (Except.ok.inj (actualC.symm.trans actual))
  subst rcC afterC
  have streams : zC = z' := Option.some.inj (boundaryC.good.live.hz.symm.trans get)
  subst zC
  have usedEq := (stream_accounting_counts_unique accountC account).1
  have accountA : StreamAccounting z z' used written.length := by rw [← usedEq]; exact accountC
  refine ⟨written, ?_, accountA, boundary.finish_retains_input_suffix buffers pointer snapshot actual get account⟩
  refine ⟨z, z', boundary.good.live.hz, get, buffers,
    default_finish_active_header boundary.good boundary.no_header, snapshot, ?_, ?_, actual⟩
  · have count := account.2.2.1
    omega
  · have count := accountC.2.2.2.1
    have length : z.avail_out.toNat - z'.avail_out.toNat = written.length := by omega
    rw [length]
    exact bytesC

/-- One real positive-output FINISH after the header gives an observed
data step, exact unread suffix and a smaller rank whenever unfinished.
It supplies the execution step for the frozen finite-continuation goal;
there is no output-bound query or assumed callee contract. -/
theorem ready_finish_observed {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {input : List UInt8}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (snapshot : Bytes h z.next_in z.avail_in.toNat input)
    (accepted : d.status = FINISH_STATE → z.avail_in = 0) (started : d.status ≠ INIT_STATE) :
    let rank := fun (stream : ZStream) (state : DeflateState) =>
      (state.lookahead.toNat + stream.avail_in.toNat) * 131078 +
        (if state.status = BUSY_STATE then 65541 + state.pending.toNat
         else state.pending.toNat + (if state.wrap = 1 then 4 else 0))
    ∃ used written rc after z' result,
      DataStep .deflate h after r Z_FINISH rc input written used ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      Bytes after z'.next_in z'.avail_in.toNat (input.drop used) ∧
      StreamAccounting z z' used written.length ∧ (rc = Z_OK ∨ rc = Z_STREAM_END) ∧
      (rc = Z_OK → rank z' result < rank z d) ∧
      (result.status = FINISH_STATE → z'.avail_in = 0) ∧ result.status ≠ INIT_STATE ∧
      (rc = Z_STREAM_END → z'.avail_in = 0) := by
  dsimp only
  obtain ⟨used, produced, rc, after, z', result, actual, boundaryA, buffersA, account,
      allowed, progress, emptyA, startedA⟩ :=
    boundary.finish_progress buffers pointer output (snapshot_input_valid snapshot) accepted started
  obtain ⟨usedC, written, rcC, afterC, zC, resultC, actualC, boundaryC, _buffersC, _goodC,
      accountC, bytesC, _inC, _outC, _allowedC, _errorsC, _invalidC, terminalC,
      _shapeC, _frameC, _liveC, _allocC, _nextC⟩ :=
    boundary.all_scalar_request_contract Z_FINISH buffers (Or.inr ⟨ob, oo, pointer⟩)
  obtain ⟨code, heaps⟩ := Prod.mk.inj (Except.ok.inj (actualC.symm.trans actual))
  subst rcC afterC
  have streams : zC = z' := Option.some.inj (boundaryC.good.live.hz.symm.trans boundaryA.good.live.hz)
  have states : resultC = result := Option.some.inj (boundaryC.good.live.hs.symm.trans boundaryA.good.live.hs)
  subst zC resultC
  obtain ⟨usedEq, producedEq⟩ := stream_accounting_counts_unique accountC account
  have accountA : StreamAccounting z z' used written.length := by rw [← usedEq]; exact accountC
  have observed : DataStep .deflate h after r Z_FINISH rc input written used := by
    refine ⟨z, z', boundary.good.live.hz, boundaryA.good.live.hz, buffers,
      default_finish_active_header boundary.good boundary.no_header, snapshot, ?_, ?_, actual⟩
    · have count := account.2.2.1
      omega
    · have count := accountC.2.2.2.1
      have length : z.avail_out.toNat - z'.avail_out.toNat = written.length := by omega
      rw [length]
      exact bytesC
  exact ⟨used, written, rc, after, z', result, observed, boundaryA, buffersA,
    boundary.finish_retains_input_suffix buffers pointer snapshot actual boundaryA.good.live.hz account,
    accountA, allowed, progress, emptyA, startedA, fun ended => (terminalC ended).2.2.1⟩

end ZlibF.Spec.Public.Proofs.DeflateCore
