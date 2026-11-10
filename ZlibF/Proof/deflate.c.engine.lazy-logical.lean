import ZlibF.Proof.«deflate.c.engine.lazy-history»

/-! # Lazy matches represented by logical input positions

A sliding window may subtract w_size from a match_start below w_size.
Its UInt32 wrap is defined, and the emitted distance remains unchanged.
The byte witness therefore belongs to the logical input, not exclusively
to indices still present in the current window array.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def PastMatch (input : Nat → UInt8) (origin : Nat) (d : DeflateState)
    (position length : UInt32) : Prop :=
  3 ≤ length.toNat →
    1 ≤ d.strstart.toNat ∧ d.match_available ≠ 0 ∧ length.toNat ≤ d.lookahead.toNat + 1 ∧
    ∃ distance : Nat,
      1 ≤ distance ∧ distance ≤ d.w_size.toNat - 262 ∧
      d.strstart - 1 - position = UInt32.ofNat distance ∧
      distance ≤ origin + d.strstart.toNat - 1 ∧
      ∀ j, j < length.toNat →
        input (origin + d.strstart.toNat - 1 - distance + j) =
          input (origin + d.strstart.toNat - 1 + j)

def LazyHistory (input : Nat → UInt8) (origin : Nat) (d : DeflateState) : Prop :=
  d.match_length.toNat ≤ 258 ∧ PastMatch input origin d d.match_start d.match_length

def PreviousHistory (input : Nat → UInt8) (origin : Nat) (d : DeflateState) : Prop :=
  d.prev_length.toNat ≤ 258 ∧ PastMatch input origin d d.prev_match d.prev_length

theorem logical_history_initial {d : DeflateState} (length : d.match_length = 2)
    (input : Nat → UInt8) (origin : Nat) : LazyHistory input origin d := by
  refine ⟨by rw [length]; decide, ?_⟩
  intro large
  rw [length] at large
  change 3 ≤ 2 at large
  omega

theorem initialized_logical_history {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (start : EngineStart h r ds z d)
    (input : Nat → UInt8) : LazyHistory input 0 d :=
  logical_history_initial start.matchLength input 0

theorem logical_prepare_history {d : DeflateState} {input : Nat → UInt8} {origin : Nat}
    (history : LazyHistory input origin d) (key : UInt32) :
    PreviousHistory input origin (lazyPrepare { d with ins_h := key }) := history

/-- A match still represented by window bytes supplies the persistent
logical witness. Subsequent sliding need not retain those source bytes. -/
theorem window_history_logical {d : DeflateState} {wa : Array UInt8}
    {input : Nat → UInt8} {origin : Nat} (history : WindowLazyHistory d wa)
    (view : ∀ i, i < d.strstart.toNat + d.lookahead.toNat → bfn wa i = input (origin + i)) :
    LazyHistory input origin d := by
  refine ⟨history.1, ?_⟩
  intro large
  obtain ⟨start, available, room, earlier, distance, length, bytes⟩ := history.2 large
  let delta := d.strstart.toNat - 1 - d.match_start.toNat
  have ss : (d.strstart - 1).toNat = d.strstart.toNat - 1 := u32_sub_one start
  have exactDistance : (d.strstart - 1 - d.match_start).toNat = delta := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le, ss]; omega), ss]
  have size : delta < 2 ^ 32 := by have := d.strstart.toNat_lt; dsimp only [delta]; omega
  refine ⟨start, available, room, delta, by dsimp only [delta]; omega, distance, ?_, ?_, ?_⟩
  · apply UInt32.toNat_inj.mp
    rw [exactDistance, UInt32.toNat_ofNat', Nat.mod_eq_of_lt size]
  · dsimp only [delta]
    omega
  · intro j hj
    have fitCurrent : d.strstart.toNat - 1 + j < d.strstart.toNat + d.lookahead.toNat := by omega
    have fitSource : d.match_start.toNat + j < d.strstart.toNat + d.lookahead.toNat := by omega
    have sourceIndex : origin + d.strstart.toNat - 1 - delta + j = origin + (d.match_start.toNat + j) := by
      dsimp only [delta]
      omega
    have targetIndex : origin + d.strstart.toNat - 1 + j = origin + (d.strstart.toNat - 1 + j) := by omega
    rw [sourceIndex, targetIndex, ← view _ fitSource, ← view _ fitCurrent]
    exact bytes j hj

/-- Cancellation holds for machine distances even when the stored match
position underflows during sliding. No non-wrapping assumption is made. -/
theorem slide_distance (ss ms shift : UInt32) :
    (ss - shift) - 1 - (ms - shift) = ss - 1 - ms := by
  apply UInt32.toBitVec_inj.mp
  simp only [UInt32.toBitVec_sub]
  generalize ss.toBitVec = a, ms.toBitVec = b, shift.toBitVec = c
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg,
    BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg,
    BitVec.neg_add, BitVec.sub_eq_add_neg, BitVec.neg_neg]
  have cancel : -c + c = 0 := by
    simpa [BitVec.sub_eq_add_neg] using BitVec.sub_add_cancel (0 : BitVec 32) c
  calc
    a + -c + -1 + (-b + c) = (a + -1 + -b) + (-c + c) := by ac_rfl
    _ = a + -1 + -b := by rw [cancel]; exact BitVec.add_zero _

def slideLazyState (d : DeflateState) : DeflateState :=
  { d with strstart := d.strstart - d.w_size, match_start := d.match_start - d.w_size }

/-- The logical lazy witness survives the two actual position updates of
window sliding. Full fill_window also has hash, input and padding work. -/
theorem logical_history_slide {input : Nat → UInt8} {origin : Nat} {d : DeflateState}
    (history : LazyHistory input origin d) (room : d.w_size.toNat + 1 ≤ d.strstart.toNat) :
    LazyHistory input (origin + d.w_size.toNat) (slideLazyState d) := by
  have start : (slideLazyState d).strstart.toNat = d.strstart.toNat - d.w_size.toNat := by
    change (d.strstart - d.w_size).toNat = _
    exact UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; omega)
  refine ⟨history.1, ?_⟩
  intro large
  obtain ⟨_, available, remaining, distance, positive, bound, machine, prior, bytes⟩ := history.2 large
  refine ⟨by rw [start]; omega, available, remaining, distance, positive, bound, ?_, ?_, ?_⟩
  · change (d.strstart - d.w_size) - 1 - (d.match_start - d.w_size) = UInt32.ofNat distance
    rw [slide_distance]
    exact machine
  · change distance ≤ origin + d.w_size.toNat + (slideLazyState d).strstart.toNat - 1
    rw [start]
    omega
  · change ∀ j, j < d.match_length.toNat →
        input (origin + d.w_size.toNat + (slideLazyState d).strstart.toNat - 1 - distance + j) =
          input (origin + d.w_size.toNat + (slideLazyState d).strstart.toNat - 1 + j)
    rw [start]
    have endpoint : origin + d.w_size.toNat + (d.strstart.toNat - d.w_size.toNat) - 1 =
        origin + d.strstart.toNat - 1 := by omega
    rw [endpoint]
    exact bytes

theorem logical_previous_tally_bounds {input : Nat → UInt8} {origin : Nat} {d : DeflateState}
    (history : PreviousHistory input origin d) (selected : 3 ≤ d.prev_length.toNat)
    (window : d.w_size.toNat ≤ 32768) :
    let distance := d.strstart - 1 - d.prev_match
    let length := d.prev_length - MIN_MATCH_u
    1 ≤ distance.toNat ∧ distance.toNat ≤ 32768 ∧
      length.toNat = d.prev_length.toNat - 3 ∧ length.toNat ≤ 255 ∧
      d.prev_length.toNat - 1 ≤ d.lookahead.toNat := by
  obtain ⟨_, _, room, distance, positive, bound, machine, _, _⟩ := history.2 selected
  have exactDistance : (d.strstart - 1 - d.prev_match).toNat = distance := by
    rw [machine, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have len : (d.prev_length - MIN_MATCH_u).toNat = d.prev_length.toNat - 3 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact selected)]
    rfl
  have maximum := history.1
  exact ⟨by rw [exactDistance]; omega, by rw [exactDistance]; omega, len, by rw [len]; omega, by omega⟩

/-- The real match-emission guard and logical history discharge the
inline tally's argument bounds. No callee contract is assumed. The
following consumption and insertion loop is a separate source fragment.
-/
theorem logical_history_tally_call {h : Heap} {r : ZStreamRef} {ds top : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {origin : Nat}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (history : PreviousHistory input origin d)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (strict : d.sym_next.toNat < d.sym_end.toNat) :
    let distance := d.strstart - 1 - d.prev_match
    let length := d.prev_length - MIN_MATCH_u
    ∃ after result,
      tally_dist (some (.tab ds)) distance length h = .ok (d.sym_next + 3 == d.sym_end, after) ∧
      DGood after r ds z result ∧ HeapChains after result top ∧
      length.toNat ≤ 255 ∧ d.prev_length.toNat - 1 ≤ d.lookahead.toNat ∧
      result.strstart = d.strstart ∧ result.lookahead = d.lookahead := by
  have previous : 3 ≤ d.prev_length.toNat := by
    have guard := selected
    simp only [Bool.and_eq_true, decide_eq_true_eq] at guard
    exact UInt32.le_iff_toNat_le.mp guard.1
  have window : d.w_size.toNat ≤ 32768 := by
    rw [good.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) good.inv.wbits_hi
         _ = 32768 := by decide
  have bounds := logical_previous_tally_bounds history previous window
  let distance := d.strstart - 1 - d.prev_match
  let length := d.prev_length - MIN_MATCH_u
  obtain ⟨b, buf, _, run, goodA, chainsA, _⟩ :=
    tally_match_good_chains good chains distance length bounds.1 bounds.2.1 strict
  exact ⟨_, _, run, goodA, chainsA, bounds.2.2.2.1, bounds.2.2.2.2, rfl, rfl⟩

end Zlib.Deflate.Engine.Proofs
