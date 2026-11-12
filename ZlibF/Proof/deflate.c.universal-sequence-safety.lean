import ZlibF.Proof.«deflate.c.universal-ops-header»
import ZlibF.Proof.«deflate.c.universal-ops-callfacts»
import ZlibF.Proof.«deflate.c.universal-ops-copy»
import ZlibF.Proof.«deflate.c.universal-end»

/-!
# deflate.c: safety of every permitted call sequence (composition)

`Goal.deflate_sequence_safety` from the per-operation lemmas, as `inflate.c.sequence-safety`
does for inflate: the invariant `DInv`, the header facts `HeaderInv` and the between-calls facts `CallFacts` hold
on every reachable history (`reachable_inv_of`, by induction on `StreamReachable .deflate`), one
more operation is safe with an exact ledger (`operation_step_of`), and `deflateEnd` frees every
block the stream owns (`end_from_inv`).

The lemmas that are not yet theorems are the fields of `SequenceFacts`, with the statements of
`operation_step_of`, `operation_header_of` and `operation_callfacts_of`: `deflate` itself
(`deflate_call` with the owned-block clause, its header phase, and its `CallFacts`),
`deflateSetDictionary` and `deflateParams` (their steps, header facts and `CallFacts`). A direct
`deflateResetKeep` is not a stream operation (`StreamOperation`, `docs/deviations.md`). When each
lands, its field is discharged and the theorem below becomes `Goal.deflate_sequence_safety` with
no hypothesis.
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
    DInv h r ds z d → CallFacts d → ∀ (level strategy : Int32), StreamBuffers h r → ActiveHeader h r →
    StepOk h r (.deflateParams (some r) level strategy)
  deflateHeader : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {flush rc : Int32}, DInv h r ds z d → HeaderInv d → StreamBuffers h r →
    ActiveHeader h r → C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) →
    DInv after r ds' z' d' → HeaderInv d'
  paramsHeader : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {level strategy rc : Int32}, DInv h r ds z d → CallFacts d → HeaderInv d →
    StreamBuffers h r → ActiveHeader h r → C.run (Zlib.Deflate.deflateParams (some r) level strategy) h = .ok (rc, after) →
    DInv after r ds' z' d' → HeaderInv d'
  setDictionaryHeader : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {dictionary : BPtr} {dictLength : UInt32} {rc : Int32}, DInv h r ds z d →
    HeaderInv d → CallerRange h r dictionary dictLength.toNat false →
    C.run (Zlib.Deflate.deflateSetDictionary (some r) dictionary dictLength) h = .ok (rc, after) →
    DInv after r ds' z' d' → HeaderInv d'
  deflateCalls : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {flush rc : Int32}, DInv h r ds z d → HeaderInv d → CallFacts d →
    StreamBuffers h r → ActiveHeader h r → C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) →
    DInv after r ds' z' d' → CallFacts d'
  paramsCalls : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {level strategy rc : Int32}, DInv h r ds z d → HeaderInv d → CallFacts d →
    StreamBuffers h r → ActiveHeader h r →
    C.run (Zlib.Deflate.deflateParams (some r) level strategy) h = .ok (rc, after) →
    DInv after r ds' z' d' → CallFacts d'
  setDictionaryCalls : ∀ {h after : Heap} {r : ZStreamRef} {ds ds' : Nat} {z z' : ZStream}
    {d d' : DeflateState} {dictionary : BPtr} {dictLength : UInt32} {rc : Int32}, DInv h r ds z d →
    HeaderInv d → CallFacts d → CallerRange h r dictionary dictLength.toNat false →
    C.run (Zlib.Deflate.deflateSetDictionary (some r) dictionary dictLength) h = .ok (rc, after) →
    DInv after r ds' z' d' → CallFacts d'

/-- One operation from `DInv`, `HeaderInv` and `CallFacts`. -/
theorem SequenceFacts.step (facts : SequenceFacts) {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream}
    {d : DeflateState} {call : Call} (inv : DInv h r ds z d) (header : HeaderInv d) (calls : CallFacts d)
    (operation : StreamOperation .deflate r call) (args : StreamArguments h r call) : StepOk h r call :=
  operation_step_of facts.deflateCall facts.stepSetDictionary facts.stepParams
    inv header calls operation args

/-- **Every reachable deflate state satisfies the invariant, the header facts and the
between-calls facts.** By induction on the history. -/
theorem reachable_inv_of (facts : SequenceFacts) {h : Heap} {r : ZStreamRef}
    (reach : StreamReachable .deflate h r) : ∃ ds z d, DInv h r ds z d ∧ HeaderInv d ∧ CallFacts d := by
  generalize kind : StreamKind.deflate = k at reach
  induction reach with
  | inflateInit => cases kind
  | deflateInit fresh uniq globals get allocators ver run =>
    obtain ⟨ds, z, d, inv, calls⟩ := init2_inv fresh uniq globals get allocators ver run
    obtain ⟨ds', z', d', inv', header⟩ := init2_header fresh uniq globals get allocators ver run
    obtain ⟨-, -, e⟩ := inv.unique inv'.good
    exact ⟨ds, z, d, inv, e ▸ header, calls⟩
  | rebuffer _ rebuffer _ ih =>
    obtain ⟨ds, z, d, inv, header, calls⟩ := ih kind
    obtain ⟨z', _, inv'⟩ := inv.rebuffer rebuffer
    exact ⟨ds, z', d, inv', header, calls⟩
  | step _ _ operation args run ih =>
    subst kind
    obtain ⟨ds, z, d, inv, header, calls⟩ := ih rfl
    obtain ⟨value', after', run', ⟨ds', z', d', invAfter⟩, -, -⟩ := facts.step inv header calls operation args
    have same := run.symm.trans run'
    simp only [Except.ok.injEq, Prod.mk.injEq] at same
    obtain ⟨-, rfl⟩ := same
    exact ⟨ds', z', d', invAfter, operation_header_of facts.deflateHeader facts.paramsHeader
      facts.setDictionaryHeader inv header calls operation args run invAfter,
      operation_callfacts_of facts.deflateCalls facts.paramsCalls facts.setDictionaryCalls
        inv header calls operation args run invAfter⟩
  | inflateCopy => cases kind
  | deflateCopy _ distinct get run ih =>
    obtain ⟨ds, z, d, inv, header, calls⟩ := ih kind
    obtain ⟨ds', z', d', invAfter⟩ := copy_inv inv distinct get run
    exact ⟨ds', z', d', invAfter, copy_header inv header distinct get run invAfter,
      copy_callfacts inv calls distinct get run invAfter⟩

/-- **Safety of every permitted deflate call sequence** from the open lemmas of `SequenceFacts`. -/
theorem deflate_sequence_safety_of (facts : SequenceFacts) : Goal.deflate_sequence_safety := by
  refine ⟨?_, ?_, ?_⟩
  · intro h r reach
    obtain ⟨ds, z, d, inv, _⟩ := reachable_inv_of facts reach
    exact ⟨ds, z, d, inv.dgood, inv.defAlloc⟩
  · intro h r call reach _fits operation args
    obtain ⟨ds, z, d, inv, header, calls⟩ := reachable_inv_of facts reach
    obtain ⟨value, after, run, ⟨ds', z', d', invAfter⟩, frame, live⟩ := facts.step inv header calls operation args
    exact ⟨value, after, run, ⟨ds', z', d', invAfter.dgood, invAfter.defAlloc⟩, frame, live⟩
  · intro h r reach
    obtain ⟨ds, z, d, inv, _⟩ := reachable_inv_of facts reach
    exact end_from_inv inv

#print axioms deflate_sequence_safety_of

end Zlib.Deflate.Universal
