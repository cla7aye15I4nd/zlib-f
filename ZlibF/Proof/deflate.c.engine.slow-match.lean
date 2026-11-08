import ZlibF.Proof.«deflate.c.engine.match-advance»
import ZlibF.Proof.«deflate.c.engine.lazy-logical»

/-! # The actual slow match-emission branch without a block flush -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

set_option maxHeartbeats 2000000 in
/-- The actual selected-match branch: legal distance and length follow
from logical lazy history, the real inline tally writes the symbol, and
the complete consumption/insertion loop restores the next boundary.
The strict post-tally room selects the source's non-flushing branch.
No callee execution specification is assumed.
-/
theorem slow_match_before_flush {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    {input : Nat → UInt8} {origin : Nat}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (history : PreviousHistory input origin d)
    (selected : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = true)
    (lookahead : 262 ≤ d.lookahead.toNat)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (space : d.sym_next.toNat + 3 < d.sym_end.toNat)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    ∃ candidate after result,
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ({ st with hash_head := candidate, bflush := false }, after) ∧
      DGood after r ds z result ∧ HeapChains after result result.strstart.toNat ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧
      result.match_available = 0 ∧ result.match_length = 2 ∧ result.prev_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + (d.prev_length.toNat - 1) ∧
      result.lookahead.toNat = d.lookahead.toNat - (d.prev_length.toNat - 1) ∧
      result.strstart.toNat + result.lookahead.toNat = d.strstart.toNat + d.lookahead.toNat ∧
      result.strstart.toNat + result.lookahead.toNat ≤ result.window_size.toNat ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) result.strstart.toNat result.ins_h ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ LazyHistory input origin result := by
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
  obtain ⟨d0, b, buf, trees⟩ := good.trees
  have same : d0 = d := Option.some.inj (trees.base.dstate.symm.trans good.live.hs)
  subst d0
  have room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat := by omega
  let bytes := matchBytes buf d distance.toUInt16 length.toUInt8
  let dt := matchSymbolState d distance length
  let ht := setD (Zlib.Trees.Proofs.Out.setB h b bytes) ds dt
  have goodT : DGood ht r ds z dt := match_good_after good trees distance length room
  have chainsT : HeapChains ht dt (d.strstart.toNat + 1) := by
    obtain ⟨wb, p, q, a, pa, qa, hw, hp, hq, ha, hpa, hqa, H⟩ :=
      pending_write_chains good chains trees.base.pbuf bytes 0
    exact ⟨wb, p, q, a, pa, qa, hw, hp, hq, ha, hpa, hqa, H⟩
  have getT : ht.bytes w = some wa := pending_window_frame good win trees.base.pbuf get bytes dt
  have count : (d.sym_next + 3).toNat = d.sym_next.toNat + 3 := literal_count trees.base room 0
  have flag : (d.sym_next + 3 == d.sym_end) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro eq
    have num := congrArg UInt32.toNat eq
    rw [count] at num
    omega
  have tally : tally_dist (some (.tab ds)) distance length h = .ok (false, ht) := by
    simpa only [flag, ht, dt, bytes, matchSymbolState] using tally_match_run trees.base distance length bounds.1 bounds.2.1 room
  obtain ⟨candidate, after, result, advance, goodA, chainsA, winA, bytesA, availableA, lengthA,
      previousA, startA, lookA, endpoint, rangeA, formA, keep, _⟩ :=
    slow_match_advance goodT chainsT win getT previous history.1 lookahead range form hash_head
  have nextCount : result.sym_next.toNat < result.sym_end.toNat := by
    have next := literal_not_full trees 0 room flag
    have nextEq := keep.2.2.2.2.2.2.2.2.2.2
    have endEq := keep.2.2.2.2.1
    rw [nextEq, endEq]
    exact next
  refine ⟨candidate, after, result, ?_, goodA, chainsA, winA, bytesA, availableA, lengthA,
    previousA, startA, lookA, endpoint, rangeA, formA, nextCount,
    logical_history_initial lengthA input origin⟩
  have advance' : slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u)
      hash_head ht = .ok (candidate, after) := advance
  dsimp only [distance, length] at tally
  unfold slowDecision
  simp only [bind_app, ldDeflateState_tab good.live.hs, selected, if_true, tally]
  change (do
    let head ← slowMatchAdvance (some (.tab ds)) (d.strstart + d.lookahead - MIN_MATCH_u) hash_head
    pure { st with hash_head := head, bflush := false }) ht = _
  rw [bind_app, advance']
  rfl

end Zlib.Deflate.Engine.Proofs
