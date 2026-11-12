import ZlibF.Proof.«deflate.c.universal-ops-prime»
import ZlibF.Proof.«deflate.c.universal-ops-plain-dictionary»
import ZlibF.Spec.Public.Streams

/-!
# deflate.c: the case split of `operation_step` (batch A)

`operation_step` of the deflate skeleton, case by case over `StreamOperation .deflate`. The
operations whose lemma is checked use it: `deflateReset` (`step_reset`), `deflatePrime`
(`step_prime`), `deflateSetHeader`, `deflateTune`, `deflateGetDictionary`, `deflatePending`,
`deflateUsed`, `deflateBound`, `deflateBound_z` (`deflate.c.universal-ops`). The others are
hypotheses of `operation_step_of`, with the statement their owner gives:

* `deflate`: the skeleton's `deflate_call` (owner 2), plus the clause that the call keeps the five
  owned blocks of the state, which the skeleton statement does not give and the allocation ledger
  of `StreamSequenceSafety` needs;
* `deflateSetDictionary`, `deflateParams`: `step_setDictionary`, `step_params` (the latter reads
  the between-calls facts `CallFacts`, a premise here).

A direct `deflateResetKeep` is not a stream operation (`StreamOperation`, `docs/deviations.md`).

The header facts `HeaderInv` (beside `DInv`) are a premise, as in the skeleton's `reachable_inv`;
`step_prime` reads them. The buffer of `deflateGetDictionary` is a caller byte block
(`plain_dictionary_of_args`, from the history's arguments).
-/

namespace Zlib.Deflate.Universal
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Engine.Proofs
open Zlib.Deflate.Proofs
set_option autoImplicit false

/-- The clauses of `Goal.deflate` after the run, as in the skeleton (`CallClauses`). -/
def DispatchCallClauses (h : Heap) (r : ZStreamRef) (i : Nat) (z : ZStream) (s : DeflateState) (flush : Int32)
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

/-- A buffer frame over the first `n` bytes of an output range is one over the first `m ≥ n`, for
a larger set of changed blocks. -/
theorem bufferFrame_widen {h after : Heap} {c1 c2 : Nat → Prop} {p : BPtr} {n m : Nat}
    (frame : BufferFrame h after c1 [⟨p, n⟩]) (le : n ≤ m) (sub : ∀ b, c1 b → c2 b) :
    BufferFrame h after c2 [⟨p, m⟩] := by
  obtain ⟨⟨s, a, g, nb, na, keep⟩, inside⟩ := frame
  have same : restoreRegions h after [⟨p, m⟩] = restoreRegions h after [⟨p, n⟩] := rfl
  refine ⟨?_, ?_⟩
  · rw [same]
    exact ⟨s, a, g, nb, na, fun b live nc => keep b live (fun c => nc (sub b c))⟩
  · intro region mem r off a0 ptr get
    rw [List.mem_singleton] at mem
    subst mem
    obtain ⟨a', get', size, keep'⟩ := inside ⟨p, n⟩ (List.mem_singleton.mpr rfl) r off a0 ptr get
    refine ⟨a', get', size, fun j hj nc => keep' j hj ?_⟩
    rintro ⟨region', mem', cov⟩
    rw [List.mem_singleton] at mem'
    subst mem'
    obtain ⟨o, po, l1, l2⟩ := cov
    exact nc ⟨⟨p, m⟩, List.mem_singleton.mpr rfl, o, po, l1, by simp only at l2 ⊢; omega⟩

/-- **`operation_step` from the open operation lemmas.** Every operation of
`StreamOperation .deflate` keeps the invariant, with the frame and the allocation ledger of
`StreamSequenceSafety`. Hypotheses (not yet theorems): `deflateCall` (the skeleton's `deflate_call`,
owner 2, with the owned-block clause), `stepSetDictionary` and `stepParams`. Premises: the header
facts `header` and the between-calls facts `calls`. -/
theorem operation_step_of
    (deflateCall : ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
      DInv h r ds z d → StreamBuffers h r → ActiveHeader h r → ∀ flush : Int32,
      ∃ rc after z' d' used out,
        C.run (Zlib.Deflate.deflate (some r) flush) h = .ok (rc, after) ∧
        DInv after r ds z' d' ∧ DispatchCallClauses h r ds z d flush rc after z' d' used out ∧
        (∀ b, DeflateOwned ds d b ↔ DeflateOwned ds d' b))
    (stepSetDictionary : ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
      DInv h r ds z d → ∀ (dictionary : BPtr) (dictLength : UInt32),
      CallerRange h r dictionary dictLength.toNat false →
      StepOk h r (.deflateSetDictionary (some r) dictionary dictLength))
    (stepParams : ∀ {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState},
      DInv h r ds z d → CallFacts d → ∀ (level strategy : Int32), StreamBuffers h r → ActiveHeader h r →
      StepOk h r (.deflateParams (some r) level strategy))
    {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState} {call : Call}
    (inv : DInv h r ds z d)
    (header : HeaderInv d) (calls : CallFacts d)
    (operation : StreamOperation .deflate r call) (args : StreamArguments h r call) :
    ∃ value after, call.execute default h = .ok ((value, default), after) ∧
      (∃ ds' z' d', DInv after r ds' z' d') ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
        (StreamWriteRegions h r call) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  show StepOk h r call
  cases call
  all_goals first
    | (exfalso; simp [StreamOperation] at operation; done)
    | skip
  case deflate p flush =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨buffers, header⟩ := args
    obtain ⟨rc, after, z', d', used, out, run, inv', clauses, blocks⟩ := deflateCall inv buffers header flush
    obtain ⟨account, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, frame, live, -⟩ := clauses
    have regions : StreamWriteRegions h r (.deflate (some r) flush) = [⟨z.next_out, z.avail_out.toNat⟩] := by
      simp [StreamWriteRegions, inv.good.live.hz, inv.good.live.zst]
    refine ⟨rc, after, heapCall_run run, ⟨ds, z', d', inv'⟩, ?_, ?_⟩
    · rw [regions]
      exact bufferFrame_widen frame account.2.1
        (fun b c => c.elim Or.inl (fun o => Or.inr (Or.inl ((inv.owned b).2 o))))
    · exact live_same inv inv' (fun b => by simpa [LiveChange] using live b) blocks
  case deflateReset p =>
    simp [StreamOperation] at operation
    subst operation
    exact step_reset inv
  case deflateParams p level strategy =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨buffers, header⟩ := args
    exact stepParams inv calls level strategy buffers header
  case deflatePrime p bits value =>
    simp [StreamOperation] at operation
    subst operation
    exact step_prime inv bits value args header
  case deflateGetDictionary p dictionary hasDictLength =>
    simp [StreamOperation] at operation
    subst operation
    have plain := plain_dictionary_of_args args
    obtain ⟨z1, i, s, get, zst, hs, range, -⟩ := args
    have zz : z1 = z := Option.some.inj (get.symm.trans inv.good.live.hz)
    subst zz
    rw [inv.good.live.zst] at zst
    cases zst
    have ss : s = d := Option.some.inj (hs.symm.trans inv.good.live.hs)
    subst ss
    exact step_getDictionary inv dictionary hasDictLength range plain
  case deflateSetDictionary p dictionary dictLength =>
    simp [StreamOperation] at operation
    subst operation
    exact stepSetDictionary inv dictionary dictLength args
  case deflateSetHeader p head =>
    simp [StreamOperation] at operation
    subst operation
    exact step_setHeader inv head
  case deflateTune p g m n c =>
    simp [StreamOperation] at operation
    subst operation
    exact step_tune inv g m n c
  case deflatePending p hasPending hasBits =>
    simp [StreamOperation] at operation
    subst operation
    exact step_pending inv hasPending hasBits
  case deflateUsed p hasBits =>
    simp [StreamOperation] at operation
    subst operation
    exact step_used inv hasBits
  case deflateBound p n =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨-, live⟩ := args
    exact step_bound inv live n
  case deflateBound_z p n =>
    simp [StreamOperation] at operation
    subst operation
    obtain ⟨-, live⟩ := args
    exact step_bound_z inv live n

end Zlib.Deflate.Universal
