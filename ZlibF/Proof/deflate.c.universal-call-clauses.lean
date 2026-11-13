import ZlibF.Proof.«deflate.c.universal-invariant»
import ZlibF.Spec.Public.Streams
import ZlibF.Spec.Public.Queries

/-!
# deflate.c: the clauses of one `deflate` call (definition)

`CallClauses` is the conclusion of the skeleton lemma `deflate_call` (owner of `deflate_call`,
`docs/progress.md`) and the premise the `operation_step` case split uses for `.deflate`. Kept on
`dev` so both use one definition.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- The clauses of `Goal.deflate` after the run, exactly as `Goal.deflate` states them. -/
def GoalClauses (h : Heap) (r : ZStreamRef) (i : Nat) (z : ZStream) (s : DeflateState) (flush : Int32)
    (rc : Int32) (after : Heap) (z' : ZStream) (s' : DeflateState) (used : Nat) (out : List UInt8) : Prop :=
  StreamAccounting z z' used out.length ∧
  Bytes after z.next_out out.length out ∧
  z'.total_in = z.total_in + UInt64.ofNat used ∧
  z'.total_out = z.total_out + UInt64.ofNat out.length ∧
  (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
  (rc = Z_STREAM_ERROR ↔ DeflateRefuses z s flush) ∧
  (flush.toInt < 0 ∨ 5 < flush.toInt → rc = Z_STREAM_ERROR ∧ after = h) ∧
  (rc = Z_STREAM_END → flush = Z_FINISH ∧ s'.status = FINISH_STATE ∧
    z'.avail_in = 0 ∧ s'.pending = 0 ∧ s'.bi_valid = 0) ∧
  (rc = Z_BUF_ERROR → used = 0 ∧
    (out = [] ∨ (s.status = FINISH_STATE ∧ z.avail_in ≠ 0))) ∧
  (¬ DeflateRefuses z s flush → z.avail_out = 0 → rc = Z_BUF_ERROR) ∧
  (¬ DeflateRefuses z s flush → z.avail_out ≠ 0 →
    ¬ (s.status = FINISH_STATE ∧ z.avail_in ≠ 0) →
    (rc = Z_BUF_ERROR ↔ z.avail_in = 0 ∧ s.pending = 0 ∧ flush ≠ Z_FINISH ∧
      deflateRank flush ≤ deflateRank s.last_flush)) ∧
  (flush = Z_FINISH → ¬ DeflateRefuses z s flush → z.avail_out ≠ 0 →
    ¬ (s.status = FINISH_STATE ∧ z.avail_in ≠ 0) →
    rc = Z_STREAM_END ∨ used ≠ 0 ∨ out ≠ []) ∧
  (rc = Z_OK ∨ rc = Z_STREAM_END → z'.msg = z.msg) ∧
  (rc = Z_BUF_ERROR → StaticString after z'.msg (errorText Z_BUF_ERROR.toInt)) ∧
  (rc = Z_STREAM_ERROR → 0 ≤ flush.toInt → flush.toInt ≤ 5 →
    StaticString after z'.msg (errorText Z_STREAM_ERROR.toInt)) ∧
  (z'.data_type = z.data_type ∨
    (z.data_type = Z_UNKNOWN ∧ (z'.data_type = Z_BINARY ∨ z'.data_type = Z_TEXT))) ∧
  BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned i s b) [⟨z.next_out, out.length⟩] ∧
  LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc

/-- The conclusion of the skeleton lemma `deflate_call` beside `DInv`: the clauses of
`Goal.deflate`; that the call keeps the five owned blocks, which the ownership clauses of
`StreamSequenceSafety` need; and that a call with input and output room that returns `Z_OK`
reads or writes a byte, which the termination of the `compress*` loop needs (checked on the
real C: 2.1 million calls, no counterexample). -/
def CallClauses (h : Heap) (r : ZStreamRef) (i : Nat) (z : ZStream) (s : DeflateState) (flush : Int32)
    (rc : Int32) (after : Heap) (z' : ZStream) (s' : DeflateState) (used : Nat) (out : List UInt8) : Prop :=
  GoalClauses h r i z s flush rc after z' s' used out ∧ (∀ b, DeflateOwned i s b ↔ DeflateOwned i s' b) ∧
  (¬ DeflateRefuses z s flush → z.avail_out ≠ 0 → z.avail_in ≠ 0 → s.status ≠ FINISH_STATE →
    rc = Z_OK → used ≠ 0 ∨ out ≠ [])

end Zlib.Deflate.Universal
