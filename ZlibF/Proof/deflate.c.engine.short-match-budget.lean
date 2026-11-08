import ZlibF.Proof.«deflate.c.engine.slow-search»
import ZlibF.Proof.«deflate.c.engine.symbol-content»
import ZlibF.Proof.«deflate.c.engine.fill-slide-source»
import ZlibF.Math.DeflateStreamBudget

/-! # Actual short-match filtering supplies a byte-cost premise

These are postconditions of successful real source prefixes. Existing
execution theorems establish those runs. No safety or whole-history
quality invariant is assumed as a callee contract here.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open ZlibF.Math.DeflateBound (shifted_short_distance advanced_short_distance)
set_option autoImplicit false

/-- A retained three-byte match passes the actual unsigned TOO_FAR guard. -/
theorem kept_short_match_distance {d : DeflateState}
    (keep : rejectShort d ≠ true) (short : d.match_length = 3) :
    d.strstart - d.match_start ≤ TOO_FAR := by
  by_cases close : d.strstart - d.match_start ≤ TOO_FAR
  · exact close
  · have far' : d.strstart - d.match_start > TOO_FAR := UInt32.not_le.mp close
    have rejected : rejectShort d = true := by simp [rejectShort, short, MIN_MATCH_u, far']
    exact False.elim (keep rejected)

/-- The actual conditional search and filter retain the short-match bound.
The source caller first resets match_length to two. The theorem uses an
actual successful execution, not an assumed specification of longest_match. -/
theorem slow_find_short_quality {h after : Heap} {ds : Nat} {d : DeflateState} {candidate : UInt32}
    (get : h.dstates ds = some d) (initial : d.match_length = 2)
    (run : slowFind (some (.tab ds)) candidate h = .ok ((), after)) :
    ∃ result, after.dstates ds = some result ∧
      (result.match_length = 3 → result.strstart - result.match_start ≤ TOO_FAR) := by
  by_cases active : (candidate != 0 && d.prev_length < d.max_lazy_match &&
      d.strstart - candidate ≤ d.w_size - MIN_LOOKAHEAD_u) = true
  · unfold slowFind at run
    simp only [bind_app, ldDeflateState_tab get, active, ite_true] at run
    cases search : longest_match (some (.tab ds)) candidate h with
    | error fault => simp [search] at run
    | ok pair =>
      rcases pair with ⟨len, searched⟩
      cases found : searched.dstates ds with
      | none => simp [search, bind_app, wrD_eq, found] at run
      | some old =>
        let dm : DeflateState := { old with match_length := len }
        have write : wr (some (.tab ds)) (fun d => { d with match_length := len }) searched =
            .ok ((), setD searched ds dm) := by simp [wrD_eq, found, dm]
        have read : ldDeflateState (some (.tab ds)) (setD searched ds dm) =
            .ok (dm, setD searched ds dm) := by simp [ldD_eq]
        simp only [search, bind_app, write, read] at run
        change (if rejectShort dm then wr (some (.tab ds)) (fun d => { d with match_length := MIN_MATCH_u - 1 })
          else pure ()) (setD searched ds dm) = _ at run
        by_cases rejected : rejectShort dm = true
        · rw [ite_eq_left rejected] at run
          simp only [wrD_eq, setD, upd_same, MIN_MATCH_u] at run
          cases run
          refine ⟨{ dm with match_length := 3 - 1 }, by simp [setD], ?_⟩
          intro impossible
          change (3 - 1 : UInt32) = 3 at impossible
          exact False.elim ((by decide : (3 - 1 : UInt32) ≠ 3) impossible)
        · rw [ite_eq_right rejected] at run
          cases run
          exact ⟨dm, by simp [setD], kept_short_match_distance rejected⟩
  · unfold slowFind at run
    simp only [bind_app, ldDeflateState_tab get] at run
    rw [ite_eq_right active] at run
    have same : h = after := (Prod.mk.inj (Except.ok.inj run)).2
    subst after
    exact ⟨d, get, fun short => False.elim ((by decide : (2 : UInt32) ≠ 3) (initial.symm.trans short))⟩

/-- The real lazy field reset establishes the search entry length before
the actual successful matcher/filter prefix. -/
theorem prepared_find_short_quality {h after : Heap} {ds : Nat} {d : DeflateState}
    {candidate answer : UInt32} (get : h.dstates ds = some d)
    (run : (do
      wr (some (.tab ds)) lazyPrepare
      slowFind (some (.tab ds)) candidate
      pure candidate) h = .ok (answer, after)) :
    ∃ result, after.dstates ds = some result ∧
      (result.match_length = 3 → result.strstart - result.match_start ≤ TOO_FAR) := by
  have write : wr (some (.tab ds)) lazyPrepare h = .ok ((), setD h ds (lazyPrepare d)) := by
    simp [wrD_eq, get]
  simp only [bind_app, write] at run
  cases find : slowFind (some (.tab ds)) candidate (setD h ds (lazyPrepare d)) with
  | error fault => simp [find] at run
  | ok pair =>
    rcases pair with ⟨unit, found⟩
    have same : found = after :=
      (Prod.mk.inj (Except.ok.inj (by simpa only [find, bind_app, pure_app] using run))).2
    subst after
    have unitEq : unit = () := Subsingleton.elim _ _
    subst unit
    exact slow_find_short_quality (d := lazyPrepare d) (by simp [setD])
      (by simp [lazyPrepare, MIN_MATCH_u]) find

/-- Every actual successful slowSearch, including no-search and failed
lookup cases, establishes the unsigned three-byte-match distance bound. -/
theorem slow_search_short_quality {h after : Heap} {ds : Nat} {d : DeflateState}
    {candidate : UInt32} (get : h.dstates ds = some d)
    (run : slowSearch (some (.tab ds)) h = .ok (candidate, after)) :
    ∃ result, after.dstates ds = some result ∧
      (result.match_length = 3 → result.strstart - result.match_start ≤ TOO_FAR) := by
  unfold slowSearch at run
  simp only [bind_app, rdD_eq, get] at run
  by_cases ready : d.lookahead ≥ MIN_MATCH_u
  · rw [ite_eq_left ready] at run
    simp only [bind_app, rdD_eq, get] at run
    cases inserted : INSERT_STRING (some (.tab ds)) d.strstart h with
    | error fault => simp [inserted] at run
    | ok pair =>
      rcases pair with ⟨head, found⟩
      simp only [inserted] at run
      change (do
        wr (some (.tab ds)) lazyPrepare
        slowFind (some (.tab ds)) head
        pure head) found = .ok (candidate, after) at run
      cases foundGet : found.dstates ds with
      | none => simp [bind_app, wrD_eq, foundGet] at run
      | some old => exact prepared_find_short_quality foundGet run
  · rw [ite_eq_right ready] at run
    change (do
      wr (some (.tab ds)) lazyPrepare
      slowFind (some (.tab ds)) 0
      pure 0) h = .ok (candidate, after) at run
    exact prepared_find_short_quality get run

/-- For an older retained match position, the checked unsigned distance
is the ordinary natural distance used by the stored-symbol cost bound. -/
theorem kept_short_natural_distance {d : DeflateState}
    (keep : rejectShort d ≠ true) (short : d.match_length = 3)
    (older : d.match_start.toNat ≤ d.strstart.toNat) :
    d.strstart.toNat - d.match_start.toNat ≤ 4096 := by
  have bound := kept_short_match_distance keep short
  rw [UInt32.le_iff_toNat_le,
    UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact older)] at bound
  exact bound

/-- The actual sliding record update preserves the pending lazy match
quality, including wrapped pointer positions. -/
theorem slide_short_candidate_quality (d : DeflateState)
    (quality : d.match_length = 3 → d.strstart - 1 - d.match_start ≤ TOO_FAR) :
    (slideState d).match_length = 3 →
      (slideState d).strstart - 1 - (slideState d).match_start ≤ TOO_FAR := by
  intro short
  change (d.strstart - d.w_size) - 1 - (d.match_start - d.w_size) ≤ TOO_FAR
  rw [shifted_short_distance]
  exact quality short

/-- The actual one-byte advance retains a fresh search match as the
next lazy candidate. -/
theorem advance_short_candidate_quality (d : DeflateState)
    (quality : d.match_length = 3 → d.strstart - d.match_start ≤ TOO_FAR) :
    (advanceOne d).match_length = 3 →
      (advanceOne d).strstart - 1 - (advanceOne d).match_start ≤ TOO_FAR := by
  intro short
  change (d.strstart + 1) - 1 - d.match_start ≤ TOO_FAR
  rw [advanced_short_distance]
  exact quality short

/-- The actual deferred-byte update retains the fresh search match
quality for the next source iteration. -/
theorem defer_short_candidate_quality (d : DeflateState)
    (quality : d.match_length = 3 → d.strstart - d.match_start ≤ TOO_FAR) :
    (deferOne d).match_length = 3 →
      (deferOne d).strstart - 1 - (deferOne d).match_start ≤ TOO_FAR := by
  intro short
  change (d.strstart + 1) - 1 - d.match_start ≤ TOO_FAR
  rw [advanced_short_distance]
  exact quality short

/-- The source lazy-field preparation transfers the previous candidate
quality to the fields used by the next match emission. -/
theorem prepare_previous_short_quality (d : DeflateState)
    (quality : d.match_length = 3 → d.strstart - 1 - d.match_start ≤ TOO_FAR) :
    (lazyPrepare d).prev_length = 3 →
      (lazyPrepare d).strstart - 1 - (lazyPrepare d).prev_match ≤ TOO_FAR := quality

/-- The actual retained match symbol satisfies the distance rule
required by the byte-sensitive fixed-code cost. -/
theorem retained_match_short_quality (d : DeflateState)
    (quality : d.match_length = 3 → d.strstart - 1 - d.match_start ≤ TOO_FAR)
    (large : 3 ≤ d.match_length.toNat) :
    (retainedMatchSymbol d).distance ≠ 0 → (retainedMatchSymbol d).value = 0 →
      (retainedMatchSymbol d).distance ≤ 4096 := by
  intro _ zero
  have lengthZero : d.match_length.toNat - 3 = 0 := by
    change (d.match_length - MIN_MATCH_u).toNat = 0 at zero
    rw [UInt32.toNat_sub_of_le d.match_length MIN_MATCH_u
      (by rw [UInt32.le_iff_toNat_le]; exact large)] at zero
    exact zero
  have short : d.match_length = 3 := UInt32.toNat_inj.mp (by change d.match_length.toNat = 3; omega)
  exact UInt32.le_iff_toNat_le.mp (quality short)

/-- The source body value packet preserves the quality of every stored
symbol under the prior pending-match quality. -/
theorem slow_value_short_quality {d : DeflateState} {wa : Array UInt8}
    {xs ys : List ZlibF.Math.DeflateSymbols.Symbol}
    (previous : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (quality : d.match_length = 3 → d.strstart - 1 - d.match_start ≤ TOO_FAR)
    (values : SlowSymbolValueStep d wa xs ys) :
    ∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096 := by
  rcases values with same | ⟨_available, literal⟩ | ⟨large, matched⟩
  · rw [same]
    exact previous
  · rw [literal]
    intro s member nonzero zero
    rcases List.mem_append.mp member with old | fresh
    · exact previous s old nonzero zero
    · have same : s = emittedLiteral d wa := List.mem_singleton.mp fresh
      subst s
      exact False.elim (nonzero rfl)
  · rw [matched]
    intro s member nonzero zero
    rcases List.mem_append.mp member with old | fresh
    · exact previous s old nonzero zero
    · have same : s = retainedMatchSymbol d := List.mem_singleton.mp fresh
      subst s
      exact retained_match_short_quality d quality large nonzero zero

/-- The actual default sliding guard leaves at least 32,506 bytes
before the new cursor. -/
theorem default_slide_start_floor {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d)
    (memory : d.w_size.toNat = 32768)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    32506 ≤ (slideState d).strstart.toNat := by
  have threshold := slide_threshold good
  have lower := UInt32.le_iff_toNat_le.mp taken
  rw [threshold, memory] at lower
  change 32506 ≤ (d.strstart - d.w_size).toNat
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)]
  omega

/-- For a negative block start immediately after the actual default
slide, the zero-credit ledger represents a large enough block. -/
theorem default_slid_negative_block_large {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    (good : DGood h r ds z d) (memory : d.w_size.toNat = 32768)
    (taken : d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (balance : BlockBalance (slideState d) xs 0)
    (negative : (slideState d).block_start.toInt < 0) :
    32506 ≤ ZlibF.Math.DeflateSymbols.represented xs := by
  have floor := default_slide_start_floor good memory taken
  unfold BlockBalance at balance
  omega






end Zlib.Deflate.Engine.Proofs
