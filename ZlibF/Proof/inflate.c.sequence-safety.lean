import ZlibF.Proof.«inflate.c.reachable»
import ZlibF.Proof.«inflate.c.call-safe»
import ZlibF.Proof.«inflate.c.sync-call-safe»

/-!
# inflate.c: safety of every next call on a reachable stream

The safety part of `Goal.inflate_sequence`: from every reachable history the
next stream operation returns, writes only the caller regions it is given and
the stream's own memory, and changes the allocation ledger exactly by the
stream's own window; `inflateEnd` releases everything the stream owns.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `inflate` from `inflate_call` or `inflate_call_refused`: the written output
prefix lies inside the caller's output region, and the owned blocks are those
of `StreamOwned`. The held-bit bound holds on every reachable history. -/
theorem inflate_call_safe {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    (flush : Int32) (current : InflateInv h r i z s) (held : DecoderHeldBits s)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (arguments : StreamArguments h r (.inflate (some r) flush)) :
    ∃ value after, (Call.inflate (some r) flush).execute default h = .ok ((value, default), after) ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨
          StreamHeaderRecord h r (.inflate (some r) flush) b)
        (StreamWriteRegions h r (.inflate (some r) flush)) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  have caller : CallPremises h r := ⟨platform, arguments.1, arguments.2⟩
  have call : InflateCall h r i z s flush := by
    by_cases refused : z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ s.mode = SYNC
    · exact inflate_call_refused current caller flush refused
    · refine inflate_call current caller flush held
        ⟨fun e => refused (Or.inl e), ?_, fun e => refused (Or.inr (Or.inr e))⟩
      intro e
      exact Classical.byContradiction fun pending => refused (Or.inr (Or.inl ⟨e, pending⟩))
  exact InflateCall.safe current call

/-- Every inflate stream operation other than `inflate` returns with an exact
frame and ledger. -/
theorem operation_safe_other {r : ZStreamRef} {call : Call}
    (operation : StreamOperation .inflate r call) (other : ∀ p f, call ≠ .inflate p f) :
    InflateCallSafe r call := by
  cases call
  all_goals first
    | (exact absurd rfl (other _ _))
    | (rcases operation with ⟨⟨⟩, -⟩; done)
    | (rcases operation with ⟨⟩; done)
    | (obtain ⟨-, rfl⟩ := operation
       first
        | exact inflateReset_call_safe _
        | exact inflateReset2_call_safe _ _
        | exact inflateResetKeep_call_safe _
        | exact inflatePrime_call_safe _ _ _
        | exact inflateGetDictionary_call_safe _ _ _
        | exact inflateSetDictionary_call_safe _ _ _
        | exact inflateGetHeader_call_safe _ _
        | exact inflateSync_call_safe _
        | exact inflateSyncPoint_call_safe _
        | exact inflateMark_call_safe _
        | exact inflateCodesUsed_call_safe _
        | exact inflateValidate_call_safe _ _
        | exact inflateUndermine_call_safe _ _)

/-- Every inflate stream operation returns with an exact frame and ledger. -/
theorem operation_safe {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream} {s : InflateState}
    {call : Call} (operation : StreamOperation .inflate r call)
    (current : InflateInv h r i z s) (held : DecoderHeldBits s)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (arguments : StreamArguments h r call) :
    ∃ value after, call.execute default h = .ok ((value, default), after) ∧
      BufferFrame h after
        (fun b => StreamRoot r b ∨ StreamOwned h r b ∨ StreamHeaderRecord h r call b)
        (StreamWriteRegions h r call) ∧
      LiveChange h after
        (fun b => StreamOwned after r b ∧ ¬ h.live b)
        (fun b => StreamOwned h r b ∧ ¬ StreamOwned after r b) := by
  by_cases isInflate : ∃ p f, call = .inflate p f
  · obtain ⟨p, f, rfl⟩ := isInflate
    obtain ⟨-, rfl⟩ := operation
    exact inflate_call_safe f current held platform arguments
  · exact operation_safe_other operation (fun p f e => isInflate ⟨p, f, e⟩) h i z s current
      platform arguments

/-- The safety part of `Goal.inflate_sequence`: the invariant on every
reachable history, a safe next call with an exact ledger, and an `inflateEnd`
that frees everything the stream owns. -/
theorem inflate_sequence_safety : StreamSequenceSafety .inflate := by
  refine ⟨?_, ?_, ?_⟩
  · intro h r reach
    obtain ⟨i, z, s, current, _⟩ := reachable_invariant_kind reach rfl
    exact ⟨i, z, s, current.good, current.alloc⟩
  · intro h r call reach platform operation arguments
    obtain ⟨i, z, s, current, held⟩ := reachable_invariant_kind reach rfl
    obtain ⟨value, after, run, frame, ledger⟩ :=
      operation_safe operation current held platform arguments
    obtain ⟨i', z', s', next, _⟩ :=
      reachable_invariant_kind (StreamReachable.step reach (fun _ => platform) operation arguments run) rfl
    exact ⟨value, after, run, ⟨i', z', s', next.good, next.alloc⟩, frame, ledger⟩
  · intro h r reach
    obtain ⟨i, z, s, current, _⟩ := reachable_invariant_kind reach rfl
    obtain ⟨rc, after, z', run, ok, get, none, frame, ledger⟩ := inflateEnd_invariant current
    exact ⟨rc, after, z', run, Or.inl ok, get, none, frame, ledger⟩

#print axioms inflate_sequence_safety

end Zlib.Inflate.Proofs
