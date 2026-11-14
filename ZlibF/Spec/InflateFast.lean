import ZlibF.Proof.«inffast.c.len»

/-!
# Concrete obligations for one fast-decoder iteration

These are internal safety and frame obligations for the actual translated body. The caller must
establish the table and buffer facts from the decoder invariant. They are not callee contracts
assumed by an enclosing theorem, and do not assert format correctness for arbitrary safe tables.
-/

namespace Zlib.Inffast.Spec
open C Zlib.Inffast

/-- The loop's six-byte and 258-byte margins, and the existing concrete heap/table context.
`A` is the current output array, with its original allocation size. No function contract occurs
in this precondition. -/
structure StepPre {α : Bool} (e : Proofs.EnvG α) (c : Ctx) (A : Array UInt8) (l : L) (i o : Nat) : Prop where
  context : Proofs.CtxOK e c
  locals : Proofs.LS e l i o
  outputSize : A.size = e.A0.size
  inputRoom : i + 6 ≤ e.i0 + e.sm0.avail_in.toNat
  outputRoom : o + 258 ≤ e.o0 + e.sm0.avail_out.toNat
  notStopped : l.broke = false
  /-- When input and output share one block, `A` still holds the unread input. -/
  inputFrame : e.InputFrame A i

/-- One actual body execution reads at most six bytes and writes at most 258 bytes. A continuing
iteration writes at least one byte. Only the newly written output interval and the stream's
message/state mode may change; table storage, input and other allocations are framed by `heap`.
This is a safety/progress contract, not the still-required Huffman-format refinement. -/
def StepPost {α : Bool} (e : Proofs.EnvG α) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
    (i o : Nat) (l' : L) (h' : Heap) : Prop :=
  ∃ i' o' A' msg' mode',
    Proofs.LS e l' i' o' ∧
    i ≤ i' ∧ i' ≤ i + 6 ∧ o ≤ o' ∧ o' ≤ o + 258 ∧
    A'.size = A.size ∧ h' = e.heap A' msg' mode' ∧ l'.againL = false ∧
    (∀ j, (j < o ∨ o' ≤ j) → A'[j]? = A[j]?) ∧
    (l'.broke = false → o < o' ∧ msg' = msg ∧ mode' = mode) ∧
    (l'.broke = true → mode' = TYPE ∨ mode' = BAD)

/-- Safety and progress of the actual fast body on every concrete permitted state. -/
def Goal.step_safe : Prop :=
  ∀ (e : Proofs.Env) (c : Ctx) (A : Array UInt8) (msg : BPtr) (mode : UInt32)
      (l : L) (i o : Nat),
    StepPre e c A l i o →
    ∃ l' h', C.run (inflate_fast_body c l) (e.heap A msg mode) = .ok (l', h') ∧
      StepPost e A msg mode i o l' h'

/-- The complete fast call restores normalized bits and exact remaining input/output counts.
Only the produced output interval, stream buffer fields/message, and state bits/mode change.
The internal `Env` table predicates must be established by the main decoder; they do not
assert RFC decoding for arbitrary safe tables. -/
def FastPost {α : Bool} (e : Proofs.EnvG α) (after : Heap) : Prop :=
  ∃ (inputUsed outputUsed bufferedBytes : Nat) (bytes : Array UInt8) (msg : BPtr)
    (mode bits : UInt32) (hold : UInt64),
    inputUsed + bufferedBytes ≤ e.sm0.avail_in.toNat ∧ bufferedBytes ≤ 3 ∧
    outputUsed ≤ e.sm0.avail_out.toNat ∧
    bytes.size = e.A0.size ∧ bits.toNat < 8 ∧ hold.toNat < 2 ^ bits.toNat ∧
    after = e.r.put
      { e.h0 with bytes := upd e.h0.bytes e.ob (some bytes), istates := upd e.h0.istates e.stid (some { e.s0 with mode, bits, hold }) }
      { e.sm0 with next_in := .ref (.blk e.ib) (e.i0 + inputUsed), next_out := .ref (.blk e.ob) (e.o0 + outputUsed), avail_in := UInt32.ofNat (e.sm0.avail_in.toNat - inputUsed), avail_out := UInt32.ofNat (e.sm0.avail_out.toNat - outputUsed), msg } ∧
    (∀ index, (index < e.o0 ∨ e.o0 + outputUsed ≤ index) → bytes[index]? = e.A0[index]?) ∧
    ((mode = e.s0.mode ∧ msg = e.sm0.msg) ∨ (mode = TYPE ∧ msg = e.sm0.msg) ∨ mode = BAD) ∧
    (mode ≠ TYPE → mode ≠ BAD →
      e.sm0.avail_in.toNat - inputUsed < 6 + bufferedBytes ∨
      e.sm0.avail_out.toNat - outputUsed < 258)

/-- Safety, termination, frame and exact register writeback of the actual whole fast decoder.
No body/callee contract is a hypothesis. The complete format-refinement goal is separate. -/
def Goal.fast_safe : Prop :=
  ∀ e : Proofs.Env, ∃ after,
    C.run (inflate_fast e.strm e.start) e.h0 = .ok ((), after) ∧ FastPost e after

end Zlib.Inffast.Spec
