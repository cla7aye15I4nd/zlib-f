import ZlibF.Proof.«deflate.c.engine.short-match-advance»
import ZlibF.Proof.«deflate.c.engine.fill-initial»

/-! # A two-byte remaining match consumes without hash insertion -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- A retained three-byte match with two bytes remaining has one consume
iteration. Its real max_insert guard skips hashing. All word arrays and
byte arrays are unchanged, independently of the pending insertion count. -/
theorem slow_match_two_remaining {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (start : 1 ≤ d.strstart.toNat) (previous : d.prev_length = 3) (lookahead : d.lookahead = 2)
    (hash_head : UInt32) :
    ∃ after, slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u) hash_head h =
      .ok (hash_head, after) ∧ after.bytes = h.bytes ∧ after.words = h.words := by
  let dp := prepareMatch d
  let hp := setD h ds dp
  let db := bumpStart dp
  let hb := setD hp ds db
  let dc := countDown db
  let hc := setD hb ds dc
  let df := finishMatch dc
  let after := setD hc ds df
  let maximum := d.strstart + d.lookahead - MIN_MATCH_u
  have extent := window_extent good win get
  have nonempty : 3 ≤ d.strstart.toNat + d.lookahead.toNat := by
    rw [lookahead]; change 3 ≤ d.strstart.toNat + 2; omega
  have maxNat := max_insert_nat_bounded good win get range nonempty
  have bumpNat : db.strstart.toNat = d.strstart.toNat + 1 := by
    change (d.strstart + 1).toNat = _
    rw [UInt32.toNat_add]
    simp only [show (1 : UInt32).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by rw [lookahead] at range; change d.strstart.toNat + 2 ≤ _ at range; omega)
  have skip : ¬ db.strstart ≤ maximum := by
    rw [UInt32.le_iff_toNat_le, bumpNat]
    change ¬ d.strstart.toNat + 1 ≤ (d.strstart + d.lookahead - MIN_MATCH_u).toNat
    rw [maxNat, lookahead]
    change ¬ d.strstart.toNat + 1 ≤ d.strstart.toNat + 2 - 3
    omega
  have pCount : dp.prev_length = 1 := by change d.prev_length - 2 = 1; rw [previous]; rfl
  have zero : dc.prev_length = 0 := by change dp.prev_length - 1 = 0; rw [pCount]; rfl
  have pState : hp.dstates ds = some dp := setD_dstates_same h ds dp
  have bState : hb.dstates ds = some db := setD_dstates_same hp ds db
  have cState : hc.dstates ds = some dc := setD_dstates_same hb ds dc
  have writeP : wr (some (.tab ds)) prepareMatch h = .ok ((), hp) := by
    simp only [wrD_eq, good.live.hs]
    rfl
  have writeB : wr (some (.tab ds)) bumpStart hp = .ok ((), hb) := by
    simp only [wrD_eq, pState]
    rfl
  have writeC : wr (some (.tab ds)) countDown hb = .ok ((), hc) := by
    simp only [wrD_eq, bState]
    rfl
  have bodyRun : slowMatchBody (some (.tab ds)) maximum hash_head hp = .ok (hash_head, hb) := by
    unfold slowMatchBody
    change (do
      wr (some (.tab ds)) bumpStart
      let ss ← rd (some (.tab ds)) (·.strstart)
      if ss ≤ maximum then INSERT_STRING (some (.tab ds)) ss else pure hash_head) hp = _
    rw [bind_app, writeB]
    simp only [bind_app, rdD_eq, bState, skip, ite_false]
    rfl
  have condRun : slowMatchCond (some (.tab ds)) hash_head hb = .ok ((false, hash_head), hc) := by
    unfold slowMatchCond
    change (do
      wr (some (.tab ds)) countDown
      pure ((← rd (some (.tab ds)) (·.prev_length)) != 0, hash_head)) hb = _
    rw [bind_app, writeC]
    simp only [bind_app, rdD_eq, cState, zero]
    rfl
  have loopRun := do_once bodyRun condRun
  have writeF : wr (some (.tab ds)) finishMatch hc = .ok ((), after) := by
    simp only [wrD_eq, cState]
    rfl
  refine ⟨after, ?_, rfl, rfl⟩
  unfold slowMatchAdvance
  simp only [initial_match_length]
  change (do
    wr (some (.tab ds)) prepareMatch
    let hh ← cdoWhile (slowMatchBody (some (.tab ds)) maximum) (slowMatchCond (some (.tab ds))) hash_head
    wr (some (.tab ds)) finishMatch
    pure hh) h = _
  rw [bind_app, writeP]
  simp only []
  rw [bind_app, loopRun]
  simp only []
  rw [bind_app, writeF]
  rfl

/-- Determinism transfers the no-word-write fact to an established actual
run. The caller does not assume a successful execution contract. -/
theorem slow_match_two_remaining_words {h after : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {hash_head candidate : UInt32}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (start : 1 ≤ d.strstart.toNat) (previous : d.prev_length = 3) (lookahead : d.lookahead = 2)
    (run : slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u) hash_head h =
      .ok (candidate, after)) : after.words = h.words := by
  obtain ⟨other, otherRun, _, words⟩ := slow_match_two_remaining good win get range start previous lookahead hash_head
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [← heaps]
  exact words

end Zlib.Deflate.Engine.Proofs
