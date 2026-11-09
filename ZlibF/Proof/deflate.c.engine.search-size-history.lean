import ZlibF.Proof.«deflate.c.engine.fill-size-history»
import ZlibF.Proof.«deflate.c.engine.search-boundary»

/-! # Actual lazy preparation transfers the pending short-match quality -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

def FreshShortQuality (d : DeflateState) : Prop :=
  d.match_length = 3 → d.strstart - d.match_start ≤ TOO_FAR

def PreviousShortQuality (d : DeflateState) : Prop :=
  d.prev_length = 3 → d.strstart - 1 - d.prev_match ≤ TOO_FAR

/-- The real insertion/search prefix writes the two saved lazy fields
from the incoming candidate. The matcher and its filter retain those
fields and both input positions. All lookahead lengths are covered by
actual execution theorems, including the no-insertion path below three. -/
theorem slow_search_run_lazy_fields {h after : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d result : DeflateState} {input : Nat → UInt8}
    {xs : List ZlibF.Math.DeflateSymbols.Symbol} {head : UInt32}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (observed : slowSearch (some (.tab ds)) h = .ok (head, after))
    (live : after.dstates ds = some result) :
    result.prev_length = d.match_length ∧ result.prev_match = d.match_start ∧
      result.strstart = d.strstart ∧ result.block_start = d.block_start := by
  have known : ∃ computed state candidate,
      slowSearch (some (.tab ds)) h = .ok (candidate, computed) ∧ computed.dstates ds = some state ∧
      state.prev_length = d.match_length ∧ state.prev_match = d.match_start ∧
        state.strstart = d.strstart ∧ state.block_start = d.block_start := by
    by_cases three : 3 ≤ d.lookahead.toNat
    · obtain ⟨w, p, q, wa, pa, qa, env, chains⟩ := heap_chains_environment boundary.good boundary.chains
      obtain ⟨w0, wa0, win, get, _view, form⟩ := boundary.data
      have windowEq : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using env.win
      subst w0
      have arrayEq : wa0 = wa := Option.some.inj (get.symm.trans env.wbytes)
      subst wa0
      obtain ⟨key, computed, position, length, run, goodA, _chainsA, _lengthA, _clipped,
        _matching, _bytes, _form, _storage⟩ :=
        slow_search_room_storage boundary.good env chains (Nat.le_refl _) boundary.range three (room three)
          boundary.history.1 (form three)
      exact ⟨computed, _, _, run, goodA.live.hs, rfl, rfl, rfl, rfl⟩
    · obtain ⟨run, goodA, _chains, _storage⟩ := slow_search_fewer_three boundary.good boundary.chains (by omega)
      exact ⟨_, lazyPrepare d, 0, run, goodA.live.hs, rfl, rfl, rfl, rfl⟩
  obtain ⟨computed, state, candidate, run, get, fields⟩ := known
  have heaps : computed = after := (Prod.mk.inj (Except.ok.inj (run.symm.trans observed))).2
  rw [heaps] at get
  have same : state = result := Option.some.inj (get.symm.trans live)
  exact same ▸ fields

/-- Actual search establishes fresh quality from the real TOO_FAR filter
and transfers the earlier pending quality to the previous-match fields.
Its position frame also preserves the unavailable-source floor. These
are internal facts on the actual returned state, not callee contracts. -/
theorem slow_search_run_size_facts {h after : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d result : DeflateState} {input : Nat → UInt8}
    {xs : List ZlibF.Math.DeflateSymbols.Symbol} {head : UInt32}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (candidate : ShortCandidateQuality d) (floor : StoredSourceFloor d)
    (observed : slowSearch (some (.tab ds)) h = .ok (head, after))
    (live : after.dstates ds = some result) :
    FreshShortQuality result ∧ PreviousShortQuality result ∧ StoredSourceFloor result := by
  obtain ⟨other, get, quality⟩ := slow_search_short_quality boundary.good.live.hs observed
  have same : other = result := Option.some.inj (get.symm.trans live)
  subst other
  obtain ⟨length, position, start, block⟩ := slow_search_run_lazy_fields boundary room observed live
  refine ⟨quality, ?_, ?_⟩
  · intro short
    rw [length] at short
    rw [start, position]
    exact candidate short
  · intro negative
    rw [block] at negative
    rw [start]
    exact floor negative

/-- The exact symbol used by a selected match has the quality retained
in the actual saved lazy fields. -/
theorem emitted_match_short_quality {d : DeflateState}
    (previous : PreviousShortQuality d) (large : 3 ≤ d.prev_length.toNat) :
    (emittedMatch d).distance ≠ 0 → (emittedMatch d).value = 0 → (emittedMatch d).distance ≤ 4096 := by
  let retained : DeflateState := { d with match_length := d.prev_length, match_start := d.prev_match }
  exact retained_match_short_quality retained previous large

end Zlib.Deflate.Engine.Proofs
