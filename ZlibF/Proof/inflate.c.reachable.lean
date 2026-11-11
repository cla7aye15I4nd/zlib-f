import ZlibF.Proof.«inflate.c.held-history»
import ZlibF.Proof.«inflate.c.init-invariant»
import ZlibF.Proof.«inflate.c.copy-invariant»
import ZlibF.Proof.«inflate.c.sync-invariant»
import ZlibF.Proof.«inflate.c.call-default»
import ZlibF.Proof.«inflate.c.call-refused»

/-!
# inflate.c: the invariant holds on every reachable history

Initialization establishes `InflateInv` and the held-bit bound `HeldBits`
for every accepted `windowBits`; a caller rebuffer, every stream operation
and `inflateCopy` preserve both.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Preservation of the invariant with the held-bit bound by one actual return. -/
def InflatePreservesHeld (r : ZStreamRef) (call : Call) : Prop :=
  ∀ (h after : Heap) (i : Nat) (z : ZStream) (s : InflateState) (value : call.Result),
    InflateInv h r i z s → HeldBits s → ZlibF.PlatformMemory.ByteObjectsFit h → StreamArguments h r call →
    call.execute default h = .ok ((value, default), after) →
    ∃ z' s', InflateInv after r i z' s' ∧ HeldBits s'

theorem InflatePreserves.held {r : ZStreamRef} {call : Call} (preserves : InflatePreserves r call) :
    InflatePreservesHeld r call := by
  intro h after i z s value current held platform arguments run
  obtain ⟨z', s', next, keep⟩ := preserves h after i z s value current platform arguments run
  exact ⟨z', s', next, keep held⟩

/-- One `inflate` call keeps the invariant and the held-bit bound. -/
theorem inflate_preserves (r : ZStreamRef) (flush : Int32) :
    InflatePreservesHeld r (.inflate (some r) flush) := by
  intro h after i z s value current held platform arguments actual
  have caller : CallPremises h r := ⟨platform, arguments.1, arguments.2⟩
  have call : InflateCall h r i z s flush := by
    by_cases refused : z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0) ∨ s.mode = SYNC
    · exact inflate_call_refused current caller flush refused
    · refine inflate_call current caller flush held ⟨fun e => refused (Or.inl e), ?_, fun e => refused (Or.inr (Or.inr e))⟩
      intro e
      exact Classical.byContradiction fun pending => refused (Or.inr (Or.inl ⟨e, pending⟩))
  obtain ⟨rc, after', z', s', _, _, run, next, _⟩ := call
  have actualRun : C.run (inflate (some r) flush) h = .ok (value, after) := by
    change heapCall (inflate (some r) flush) default h = _ at actual
    exact run_of_heapCall actual
  have same := Except.ok.inj (run.symm.trans actualRun)
  cases same
  exact ⟨z', s', next, inflate_call_held current caller flush held run next.good⟩

/-- Every inflate stream operation preserves the invariant and the held-bit bound. -/
theorem operation_preserves {r : ZStreamRef} {call : Call}
    (operation : StreamOperation .inflate r call) : InflatePreservesHeld r call := by
  cases call
  all_goals first
    | (rcases operation with ⟨⟨⟩, -⟩; done)
    | (rcases operation with ⟨⟩; done)
    | (obtain ⟨-, rfl⟩ := operation
       first
        | exact inflate_preserves _ _
        | exact (inflateReset_preserves _).held
        | exact (inflateReset2_preserves _ _).held
        | exact (inflateResetKeep_preserves _).held
        | exact (inflatePrime_preserves _ _ _).held
        | exact (inflateGetDictionary_preserves _ _ _).held
        | exact (inflateSetDictionary_preserves _ _ _).held
        | exact (inflateGetHeader_preserves _ _).held
        | exact (inflateSync_preserves _).held
        | exact (inflateSyncPoint_preserves _).held
        | exact (inflateMark_preserves _).held
        | exact (inflateCodesUsed_preserves _).held
        | exact (inflateValidate_preserves _ _).held
        | exact (inflateUndermine_preserves _ _).held)

/-- The invariant and the held-bit bound on every reachable history. -/
theorem reachable_invariant_kind {kind : StreamKind} {h : Heap} {r : ZStreamRef}
    (reach : StreamReachable kind h r) :
    kind = .inflate → ∃ i z s, InflateInv h r i z s ∧ HeldBits s := by
  induction reach with
  | inflateInit fresh uniq globals get null value run =>
    intro _
    obtain ⟨z, s, current⟩ := inflateInit2_invariant_of fresh uniq globals get null value run
    exact ⟨_, z, s, current, inflateInit2_held fresh uniq globals get null value run current.good⟩
  | deflateInit => intro kind; cases kind
  | rebuffer _ edit _ ih =>
    intro kind
    obtain ⟨i, z, s, current, held⟩ := ih kind
    obtain ⟨z', next⟩ := rebuffer_invariant current edit
    exact ⟨i, z', s, next, held⟩
  | step _ fits operation arguments run ih =>
    intro kind
    subst kind
    obtain ⟨i, z, s, current, held⟩ := ih rfl
    obtain ⟨z', s', next, held'⟩ :=
      operation_preserves operation _ _ i z s _ current held (fits rfl) arguments run
    exact ⟨i, z', s', next, held'⟩
  | inflateCopy _ distinct get run ih =>
    intro _
    obtain ⟨i, z, s, current, held⟩ := ih rfl
    obtain ⟨i', z', s', next, keep⟩ := inflateCopy_invariant current distinct get run
    exact ⟨i', z', s', next, keep held⟩
  | deflateCopy => intro kind; cases kind

/-- The invariant and the held-bit bound hold for the decoder of every
reachable inflate stream. -/
theorem inflate_reachable_invariant {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} (reach : StreamReachable .inflate h r) (good : Good h r i z s) :
    InflateInv h r i z s ∧ HeldBits s := by
  obtain ⟨i', z', s', current, held⟩ := reachable_invariant_kind reach rfl
  have sameStream : z' = z := Option.some.inj (current.good.live.hz.symm.trans good.live.hz)
  subst sameStream
  have sameIndex : i' = i := by
    have pointer := current.good.live.zst.symm.trans good.live.zst
    cases pointer
    rfl
  subst sameIndex
  have sameState : s' = s := Option.some.inj (current.good.live.hs.symm.trans good.live.hs)
  subst sameState
  exact ⟨current, held⟩

end Zlib.Inflate.Proofs
