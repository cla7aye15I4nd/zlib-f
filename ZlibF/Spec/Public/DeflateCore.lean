import ZlibF.Spec.Public.Sequences

/-!
# Default deflate calls, separately from auxiliary APIs and capacity bounds

The scope is the default LP64 allocator and initializer: level 6, window 15,
memory level 8, strategy 0 and the zlib wrapper. Caller output is null or an
ordinary byte allocation. Input retains the public byte-view domain and
separated input/output intervals may share one allocation.

The trace records actual init, rebuffer and deflate calls. It admits every
signed flush and every returning result. Copy, reset, dictionary, priming,
parameter changes and custom headers have separate public specifications.
The unchanged full public targets still require those operations.

The ordinary completion obligation below requires a finite FINISH continuation.
It does not call deflateBound or assume its capacity promise. Its definition is
not a proof of completion. Safety and completed-output correctness are separate
obligations, so neither implies that a FINISH continuation exists.
-/

namespace ZlibF.Spec.Public.DeflateCore
open C ZlibF.Spec
set_option autoImplicit false

/-- The existing raw-output milestone. Input is not restricted to raw blocks. -/
def Output (pointer : BPtr) : Prop :=
  pointer = .null ∨ ∃ block offset, pointer = .ref (.blk block) offset

/-- Observed log updates do not assume accounting or encoding correctness.
The existing capacity-eligibility field is retained only for compatibility
with DataLog; no obligation here uses it. -/
def advanceLog (log : DataLog) (flush rc : Int32) (input output : List UInt8)
    (used : Nat) : DataLog :=
  { log with
    input := log.input ++ input.take used
    output := log.output ++ output
    result := rc
    finished := log.finished || rc == Z_STREAM_END
    boundEligible := log.boundEligible && flush == Z_FINISH }

/-- Pure actual call histories include clean refusals even when input is
null with positive avail_in. No readable input snapshot is required here.
No representation invariant or callee contract is assumed. -/
inductive Calls (r : ZStreamRef) : Heap → Prop
  | init {h after version} : InitDomain h r version →
      C.run (Zlib.Deflate.deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h =
        .ok (Z_OK, after) → Calls r after
  | caller {h after} : Calls r h → Rebuffer h after r → Calls r after
  | step {h after z flush rc} : Calls r h → r.get h = some z →
      StreamBuffers h r → Output z.next_out →
      C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) → Calls r after

/-- Actual default initialization and observed readable data calls. This
encoding trace is not the full safety history: Calls also admits input
pointer refusals without a readable snapshot. No representation
invariant, callee contract, flush restriction or output meaning is assumed. -/
inductive Trace (r : ZStreamRef) : Heap → DataLog → Prop
  | init {h after version} : InitDomain h r version →
      C.run (Zlib.Deflate.deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h =
        .ok (Z_OK, after) → Trace r after {}
  | caller {h after log} : Trace r h log → Rebuffer h after r → Trace r after log
  | step {h after log z flush rc input output used} : Trace r h log →
      r.get h = some z → Output z.next_out →
      DataStep .deflate h after r flush rc input output used →
      Trace r after (advanceLog log flush rc input output used)

/-- Default initialization includes refusals, allocation failures and exact
cleanup. Successful-initialization traces do not replace these cases. -/
def Initialization : Prop :=
  DeflateInitContract
    (fun pointer version size => Zlib.Deflate.deflateInit_ pointer Z_DEFAULT_COMPRESSION version size)
    Z_DEFAULT_COMPRESSION 8 15 8 0

/-- The next ordinary request is total, with exact bytes, return controls,
frame and ownership. Its history contains no assumed callee specification. -/
def Requests : Prop :=
  ∀ h r, Calls r h →
    ∃ ds z d, Zlib.Deflate.Spec.DGood h r ds z d ∧ Zlib.Deflate.Spec.DefAlloc z ∧
      ∀ flush, StreamBuffers h r → Output z.next_out →
          ∃ used written rc after z' result,
            C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) ∧
            StreamBuffers after r ∧ Zlib.Deflate.Spec.DGood after r ds z' result ∧
            StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
            z'.total_in = z.total_in + UInt64.ofNat used ∧
            z'.total_out = z.total_out + UInt64.ofNat written.length ∧
            (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
            (rc = Z_STREAM_ERROR ↔ flush.toInt < 0 ∨ 5 < flush.toInt ∨ z.next_out = .null ∨
              (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ (d.status = FINISH_STATE ∧ flush ≠ Z_FINISH)) ∧
            (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
            (rc = Z_STREAM_END → flush = Z_FINISH ∧ result.status = FINISH_STATE ∧
              z'.avail_in = 0 ∧ result.pending = 0 ∧ result.bi_valid = 0) ∧
            BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b)
              [⟨z.next_out, written.length⟩] ∧
            LiveChange h after (fun _ => False) (fun _ => False) ∧
            after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk

/-- Completed observed output encodes exactly the observed accepted input.
This implication does not assert that an execution will complete. -/
def CompletedEncoding : Prop :=
  ∀ h r log, Trace r h log → log.result = Z_STREAM_END →
    ZlibF.Spec.Zlib.Valid log.input log.output

/-- End releases exactly the five owned objects after any ordinary history,
including an unfinished or error-returning history. -/
def Cleanup : Prop :=
  ∀ h r, Calls r h →
    ∃ ds z d after, Zlib.Deflate.Spec.DGood h r ds z d ∧
      C.run (Zlib.Deflate.deflateEnd (some r)) h =
        .ok ((if d.status = BUSY_STATE then Z_DATA_ERROR else Z_OK), after) ∧
      r.get after = some { z with state := none } ∧
      LiveChange h after (fun _ => False) (DeflateOwned ds d) ∧
      Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk

/-- A finite continuation offers the unaccepted suffix of one fixed input,
uses positive ordinary output room, and records actual FINISH execution.
The caller can rebind or replace buffers without changing private storage. -/
inductive FinishContinuation (r : ZStreamRef) (accepted source : List UInt8) :
    Heap → DataLog → Heap → DataLog → Prop
  | refl (h log) : FinishContinuation r accepted source h log h log
  | caller {start initial h log after} :
      FinishContinuation r accepted source start initial h log → Rebuffer h after r →
      FinishContinuation r accepted source start initial after log
  | step {start initial h log after z rc input output used} :
      FinishContinuation r accepted source start initial h log →
      r.get h = some z → (∃ block offset, z.next_out = .ref (.blk block) offset) →
      0 < z.avail_out.toNat →
      (∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d →
        d.status = FINISH_STATE → input = []) →
      input = source.drop (log.input.length - accepted.length) →
      DataStep .deflate h after r Z_FINISH rc input output used →
      FinishContinuation r accepted source start initial after
        (advanceLog log Z_FINISH rc input output used)

/-- Ordinary streaming completion, without a bound query or a prescribed
whole-output capacity. The caller supplies no fresh input once finishing.
Positive output chunks and the fixed remaining input are enforced by the
continuation, not assumed as an abstract callee contract. -/
def Completes : Prop :=
  ∀ h r log z input, Trace r h log → log.finished = false → r.get h = some z →
    StreamBuffers h r → Output z.next_out → Bytes h z.next_in z.avail_in.toNat input →
    (∀ ds d, z.state = some (.deflate ds) → h.dstates ds = some d →
      d.status = FINISH_STATE → input = []) →
    ∃ after finalLog, FinishContinuation r log.input input h log after finalLog ∧
      finalLog.input = log.input ++ input ∧ finalLog.result = Z_STREAM_END

/-- These clauses can be checked independently. Completion is intentionally
not hidden inside completed-output correctness or the request contract. -/
def SafeEncodingAndCleanup : Prop :=
  Initialization ∧ Requests ∧ CompletedEncoding ∧ Cleanup

/-- The default ordinary milestone additionally needs actual completion.
The independent bound and advanced-operation goals remain unchanged. -/
def Correct : Prop := SafeEncodingAndCleanup ∧ Completes

end ZlibF.Spec.Public.DeflateCore
