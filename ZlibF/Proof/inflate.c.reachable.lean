import ZlibF.Proof.«inflate.c.call-general»
import ZlibF.Proof.«inflate.c.init-invariant»
import ZlibF.Proof.«inflate.c.copy-invariant»

/-!
# inflate.c: the invariant holds on every reachable history (skeleton)

Initialization establishes `InflateInv` for every accepted `windowBits`;
a caller rebuffer, every stream operation and `inflateCopy` preserve it.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-! ## Initialization -/

/-- The premises of `StreamReachable.inflateInit`. -/
structure InitPremises (h : Heap) (r : ZStreamRef) (version : BPtr) : Prop where
  fresh : Fresh h
  uniq : Uniq h
  globals : LibraryGlobals h
  stream : ∃ z, r.get h = some z ∧ DefaultOrNull z
  value : VersionValue h version (some 49)

/-- Every successful initialization establishes the invariant. -/
theorem inflateInit2_invariant {h after : Heap} {r : ZStreamRef} {version : BPtr} {wb : Int32}
    (premises : InitPremises h r version)
    (run : C.run (inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after)) :
    ∃ i z s, InflateInv after r i z s := by
  obtain ⟨z0, get, null⟩ := premises.stream
  obtain ⟨z, s, current⟩ := inflateInit2_invariant_of premises.fresh premises.uniq premises.globals
    get null premises.value run
  exact ⟨h.nextBlk, z, s, current⟩

/-! ## Caller edits and stream operations -/

theorem inflate_preserves (r : ZStreamRef) (flush : Int32) :
    InflatePreserves r (.inflate (some r) flush) := by
  sorry

/-- Every inflate stream operation preserves the invariant. -/
theorem operation_preserves {r : ZStreamRef} {call : Call}
    (operation : StreamOperation .inflate r call) : InflatePreserves r call := by
  cases call
  all_goals first
    | (rcases operation with ⟨⟨⟩, -⟩; done)
    | (rcases operation with ⟨⟩; done)
    | (obtain ⟨-, rfl⟩ := operation
       first
        | exact inflate_preserves _ _
        | exact inflateReset_preserves _
        | exact inflateReset2_preserves _ _
        | exact inflateResetKeep_preserves _
        | exact inflatePrime_preserves _ _ _
        | exact inflateGetDictionary_preserves _ _ _
        | exact inflateSetDictionary_preserves _ _ _
        | exact inflateGetHeader_preserves _ _
        | exact inflateSync_preserves _
        | exact inflateSyncPoint_preserves _
        | exact inflateMark_preserves _
        | exact inflateCodesUsed_preserves _
        | exact inflateValidate_preserves _ _
        | exact inflateUndermine_preserves _ _)

/-! ## Every reachable history -/

theorem reachable_invariant_kind {kind : StreamKind} {h : Heap} {r : ZStreamRef}
    (reach : StreamReachable kind h r) : kind = .inflate → ∃ i z s, InflateInv h r i z s := by
  induction reach with
  | inflateInit fresh uniq globals get null value run =>
    intro _
    exact inflateInit2_invariant ⟨fresh, uniq, globals, ⟨_, get, null⟩, value⟩ run
  | deflateInit => intro kind; cases kind
  | rebuffer _ edit _ ih =>
    intro kind
    obtain ⟨i, z, s, current⟩ := ih kind
    obtain ⟨z', next⟩ := rebuffer_invariant current edit
    exact ⟨i, z', s, next⟩
  | step _ platform operation arguments run ih =>
    intro kind
    subst kind
    obtain ⟨i, z, s, current⟩ := ih rfl
    obtain ⟨z', s', next⟩ :=
      operation_preserves operation _ _ i z s _ current (platform rfl) arguments run
    exact ⟨i, z', s', next⟩
  | inflateCopy _ distinct get run ih =>
    intro _
    obtain ⟨i, z, s, current⟩ := ih rfl
    exact inflateCopy_invariant current distinct get run
  | deflateCopy => intro kind; cases kind

/-- The invariant holds for the decoder of every reachable inflate stream. -/
theorem inflate_reachable_invariant {h : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} (reach : StreamReachable .inflate h r) (good : Good h r i z s) :
    InflateInv h r i z s := by
  obtain ⟨i', z', s', current⟩ := reachable_invariant_kind reach rfl
  exact current.of_good good

end Zlib.Inflate.Proofs
