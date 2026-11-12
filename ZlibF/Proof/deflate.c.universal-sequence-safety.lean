import ZlibF.Proof.«deflate.c.universal-ops-header»
import ZlibF.Proof.«deflate.c.universal-ops-copy»
import ZlibF.Proof.«deflate.c.universal-end»

/-!
# deflate.c: safety of every permitted call sequence (composition)

`Goal.deflate_sequence_safety` from the per-operation lemmas, as `inflate.c.sequence-safety`
does for inflate: the invariant `DInv` and the header facts `HeaderInv` hold on every reachable
history (`reachable_inv_of`, by induction on `StreamReachable .deflate`), one more operation is
safe with an exact ledger (`operation_step_of`), and `deflateEnd` frees every block the stream
owns (`end_from_inv`).

The lemmas that are not yet theorems are the fields of `SequenceFacts`, with the statements of
`operation_step_of` and `operation_header_of`: `deflate` itself (`deflate_call` with the
owned-block clause, and its header phase), `deflateSetDictionary` and `deflateParams` (batch B),
`deflateResetKeep` (awaits the positional chain heads), and `plainDictionary`, a caller fact the
history does not yet state. When each lands, its field is discharged and the theorem below
becomes `Goal.deflate_sequence_safety` with no hypothesis.
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The open lemmas of the deflate sequence-safety composition, each with the statement its
owner proves. -/
structure SequenceFacts : Prop where
  deflateCall : ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
    DInv h r ds z d → StreamBuffers h r → ActiveHeader h r → ∀ flush : Int32,
    ∃ rc after z' d' used out,
      C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) ∧
      DInv after r ds z' d' ∧ DispatchCallClauses h r ds z d flush rc after z' d' used out ∧
      (∀ b, DeflateOwned ds d b ↔ DeflateOwned ds d' b)
  stepSetDictionary : ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
    DInv h r ds z d → ∀ (dictionary : BPtr) (dictLength : UInt32),
    CallerRange h r dictionary dictLength.toNat false →
    StepOk h r (.deflateSetDictionary (some r) dictionary dictLength)
  stepParams : ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
    DInv h r ds z d → ∀ (level strategy : Int32), StreamBuffers h r → ActiveHeader h r →
    StepOk h r (.deflateParams (some r) level strategy)
  stepResetKeep : ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
    DInv h r ds z d → StepOk h r (.deflateResetKeep (some r))
  deflateHeader : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {flush rc : Int32}, DInv h r ds z d → HeaderInv d → StreamBuffers h r →
    ActiveHeader h r → C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) →
    DInv after r ds' z' d' → HeaderInv d'
  paramsHeader : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {level strategy rc : Int32}, DInv h r ds z d → HeaderInv d → StreamBuffers h r →
    ActiveHeader h r → C.run (Zlib.Deflate.deflateParams (some r) level strategy) h = .ok (rc, after) →
    DInv after r ds' z' d' → HeaderInv d'
  setDictionaryHeader : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {dictionary : BPtr} {dictLength : UInt32} {rc : Int32}, DInv h r ds z d →
    HeaderInv d → CallerRange h r dictionary dictLength.toNat false →
    C.run (Zlib.Deflate.deflateSetDictionary (some r) dictionary dictLength) h = .ok (rc, after) →
    DInv after r ds' z' d' → HeaderInv d'
  resetKeepHeader : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {rc : Int32}, DInv h r ds z d → HeaderInv d →
    C.run (Zlib.Deflate.deflateResetKeep (some r)) h = .ok (rc, after) →
    DInv after r ds' z' d' → HeaderInv d'
  /-- The buffer of `deflateGetDictionary` is a caller byte block (to be stated by the history). -/
  plainDictionary : ∀ {h : Heap} {r : ZStreamRef} {dictionary : BPtr} {hasDictLength : Bool},
    StreamArguments h r (.deflateGetDictionary (some r) dictionary hasDictLength) →
    ∀ q off, dictionary = .ref q off → ∃ x, q = .blk x

/-- The `plainDictionary` premise of the two case splits, for one call. -/
theorem SequenceFacts.plain (facts : SequenceFacts) {h : Heap} {r : ZStreamRef} {call : Call}
    (args : StreamArguments h r call) :
    ∀ (dictionary : BPtr) (hasDictLength : Bool),
      call = .deflateGetDictionary (some r) dictionary hasDictLength →
      ∀ q off, dictionary = .ref q off → ∃ x, q = .blk x := by
  intro dictionary hasDictLength e
  subst e
  exact facts.plainDictionary args

/-- One operation from `DInv` and `HeaderInv`. -/
theorem SequenceFacts.step (facts : SequenceFacts) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} {call : Call} (inv : DInv h r ds z d) (header : HeaderInv d)
    (operation : StreamOperation .deflate r call) (args : StreamArguments h r call) : StepOk h r call :=
  operation_step_of facts.deflateCall facts.stepSetDictionary facts.stepParams facts.stepResetKeep
    inv header (facts.plain args) operation args

/-- **Every reachable deflate state satisfies the invariant and the header facts.** By induction
on the history. -/
theorem reachable_inv_of (facts : SequenceFacts) {h : Heap} {r : ZStreamRef}
    (reach : StreamReachable .deflate h r) : ∃ ds z d, DInv h r ds z d ∧ HeaderInv d := by
  generalize kind : StreamKind.deflate = k at reach
  induction reach with
  | inflateInit => cases kind
  | deflateInit fresh uniq globals get allocators ver run =>
    exact init2_header fresh uniq globals get allocators ver run
  | rebuffer _ rebuffer _ ih =>
    obtain ⟨ds, z, d, inv, header⟩ := ih kind
    obtain ⟨z', _, inv'⟩ := inv.rebuffer rebuffer
    exact ⟨ds, z', d, inv', header⟩
  | step _ _ operation args run ih =>
    subst kind
    obtain ⟨ds, z, d, inv, header⟩ := ih rfl
    obtain ⟨value', after', run', ⟨ds', z', d', invAfter⟩, -, -⟩ := facts.step inv header operation args
    have same := run.symm.trans run'
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    exact ⟨ds', z', d', invAfter, operation_header_of facts.deflateHeader facts.paramsHeader
      facts.setDictionaryHeader facts.resetKeepHeader inv header (facts.plain args) operation args run
      invAfter⟩
  | inflateCopy => cases kind
  | deflateCopy _ distinct get run ih =>
    obtain ⟨ds, z, d, inv, header⟩ := ih kind
    obtain ⟨ds', z', d', invAfter⟩ := copy_inv inv distinct get run
    exact ⟨ds', z', d', invAfter, copy_header inv header distinct get run invAfter⟩

/-- **Safety of every permitted deflate call sequence** from the open lemmas of `SequenceFacts`. -/
theorem deflate_sequence_safety_of (facts : SequenceFacts) : Goal.deflate_sequence_safety := by
  refine ⟨?_, ?_, ?_⟩
  · intro h r reach
    obtain ⟨ds, z, d, inv, _⟩ := reachable_inv_of facts reach
    exact ⟨ds, z, d, inv.dgood, inv.defAlloc⟩
  · intro h r call reach _fits operation args
    obtain ⟨ds, z, d, inv, header⟩ := reachable_inv_of facts reach
    obtain ⟨value, after, run, ⟨ds', z', d', invAfter⟩, frame, live⟩ := facts.step inv header operation args
    exact ⟨value, after, run, ⟨ds', z', d', invAfter.dgood, invAfter.defAlloc⟩, frame, live⟩
  · intro h r reach
    obtain ⟨ds, z, d, inv, _⟩ := reachable_inv_of facts reach
    exact end_from_inv inv

#print axioms deflate_sequence_safety_of

end Zlib.Deflate.Universal
