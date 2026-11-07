import ZlibF.Proof.«deflate.c.engine.match-insert»

/-! # The complete slow match-insertion loop -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

/-- A do-while rank may depend on the actual heap counter. The final
execution theorem supplies the actual source step, not a callee contract. -/
theorem do_heap_rank {σ : Type} {body : σ → M σ} {cond : σ → M (Bool × σ)}
    (Inv : σ → Heap → Prop) (rank : σ → Heap → Nat) (Q : σ → Heap → Prop)
    (step : ∀ s h, Inv s h → ∃ s1 h1 c s2 h2,
      body s h = .ok (s1, h1) ∧ cond s1 h1 = .ok ((c, s2), h2) ∧
      (c = false → Q s2 h2) ∧ (c = true → Inv s2 h2 ∧ rank s2 h2 < rank s h))
    {s : σ} {h : Heap} (initial : Inv s h) (bound : rank s h < fuel) :
    ∃ result after, cdoWhile body cond s h = .ok (result, after) ∧ Q result after := by
  have run : ∀ n s h, Inv s h → rank s h < n →
      ∃ result after, cdoWhile.go body cond n s h = .ok (result, after) ∧ Q result after := by
    intro n
    induction n with
    | zero => intro s h _ hn; omega
    | succ n ih =>
      intro s h inv hn
      obtain ⟨s1, h1, c, s2, h2, bodyRun, condRun, stopped, continued⟩ := step s h inv
      cases c with
      | false => exact ⟨s2, h2, by simp [cdoWhile.go, bodyRun, condRun], stopped rfl⟩
      | true =>
        obtain ⟨next, less⟩ := continued rfl
        obtain ⟨result, after, rest, post⟩ := ih s2 h2 next (by omega)
        exact ⟨result, after, by simp [cdoWhile.go, bodyRun, condRun, rest], post⟩
  exact run fuel s h initial bound

/-- Only the insertion key, current position and loop counter change. -/
def MatchInsertFrame (before after : DeflateState) : Prop :=
  after = { before with strstart := after.strstart, ins_h := after.ins_h, prev_length := after.prev_length }

theorem match_insert_frame_step {before state : DeflateState}
    (frame : MatchInsertFrame before state) (key : UInt32) :
    MatchInsertFrame before (countDown { bumpStart state with ins_h := key }) := by
  unfold MatchInsertFrame at *
  rw [frame]
  rfl

set_option maxHeartbeats 1000000 in
/-- The actual do-while inserts each consumed match position. Its rank
is the positive prev_length counter stored in the real heap. At most 256
iterations run. The returned state has zero counter, the exact consumed
position, unchanged lookahead and a rolling hash ready for the next byte.
-/
theorem slow_match_insert_loop {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (positive : 1 ≤ d.prev_length.toNat) (countBound : d.prev_length.toNat ≤ 256)
    (lookahead : 3 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + d.prev_length.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (max_insert : UInt32) (maximum : d.strstart.toNat + d.prev_length.toNat ≤ max_insert.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (hash_head : UInt32) :
    ∃ candidate after result,
      cdoWhile (slowMatchBody (some (.tab ds)) max_insert) (slowMatchCond (some (.tab ds))) hash_head h =
        .ok (candidate, after) ∧
      DGood after r ds z result ∧ HeapChains after result (result.strstart.toNat + 1) ∧
      result.window = .ref (.blk w) 0 ∧ after.bytes w = some wa ∧ result.prev_length = 0 ∧
      result.strstart.toNat = d.strstart.toNat + d.prev_length.toNat ∧ result.lookahead = d.lookahead ∧
      result.strstart.toNat + 1 + result.lookahead.toNat ≤ result.window_size.toNat ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h ∧
      MatchInsertFrame d result := by
  let total := d.strstart.toNat + d.prev_length.toNat
  let Inv : UInt32 → Heap → Prop := fun _ heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChains heap state (state.strstart.toNat + 1) ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧
    1 ≤ state.prev_length.toNat ∧ state.prev_length.toNat ≤ 256 ∧
    3 ≤ state.lookahead.toNat ∧ state.lookahead = d.lookahead ∧
    state.strstart.toNat + state.prev_length.toNat = total ∧
    state.strstart.toNat + state.prev_length.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat ∧
    state.strstart.toNat + state.prev_length.toNat ≤ max_insert.toNat ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) (state.strstart.toNat + 1) state.ins_h ∧
    MatchInsertFrame d state
  let Q : UInt32 → Heap → Prop := fun _ heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChains heap state (state.strstart.toNat + 1) ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧ state.prev_length = 0 ∧
    state.strstart.toNat = total ∧ state.lookahead = d.lookahead ∧
    state.strstart.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) (state.strstart.toNat + 1) state.ins_h ∧
    MatchInsertFrame d state
  let rank : UInt32 → Heap → Nat := fun _ heap =>
    ((heap.dstates ds).map (fun state => state.prev_length.toNat)).getD 0
  have step : ∀ hh heap, Inv hh heap → ∃ hh1 h1 c hh2 h2,
      slowMatchBody (some (.tab ds)) max_insert hh heap = .ok (hh1, h1) ∧
      slowMatchCond (some (.tab ds)) hh1 h1 = .ok ((c, hh2), h2) ∧
      (c = false → Q hh2 h2) ∧ (c = true → Inv hh2 h2 ∧ rank hh2 h2 < rank hh heap) := by
    intro hh heap inv
    obtain ⟨state, goodS, chainsS, winS, bytesS, posS, boundS, lookS, lookEq, sumS, roomS, maxS, formS, frameS⟩ := inv
    obtain ⟨key, candidate, mid, after, bodyRun, condRun, goodA, chainsA, bytesA, startA, countA, formA⟩ :=
      slow_match_insert_step goodS chainsS winS bytesS posS lookS roomS max_insert maxS formS hh
    let result := countDown { bumpStart state with ins_h := key }
    have sumA : result.strstart.toNat + result.prev_length.toNat = total := by rw [startA, countA]; omega
    have roomA : result.strstart.toNat + result.prev_length.toNat + 1 + result.lookahead.toNat ≤
        result.window_size.toNat := by
      change result.strstart.toNat + result.prev_length.toNat + 1 + state.lookahead.toNat ≤ state.window_size.toNat
      rw [startA, countA]
      omega
    refine ⟨candidate, mid, result.prev_length != 0, candidate, after, bodyRun, condRun, ?_, ?_⟩
    · intro stop
      have zero : result.prev_length = 0 := by simpa only [bne_eq_false_iff_eq] using stop
      refine ⟨result, goodA, chainsA, winS, bytesA, zero, ?_, lookEq, ?_, formA, match_insert_frame_step frameS key⟩
      · have value : result.prev_length.toNat = 0 := by rw [zero]; rfl
        omega
      · have value : result.prev_length.toNat = 0 := by rw [zero]; rfl
        omega
    · intro more
      have nonzero : result.prev_length ≠ 0 := by simpa only [bne_iff_ne] using more
      have positiveA : 1 ≤ result.prev_length.toNat := by
        have ne : result.prev_length.toNat ≠ 0 := by intro eq; exact nonzero (UInt32.toNat_inj.mp eq)
        omega
      refine ⟨⟨result, goodA, chainsA, winS, bytesA, positiveA, ?_, lookS, lookEq, sumA, roomA, ?_, formA, match_insert_frame_step frameS key⟩, ?_⟩
      · rw [countA]
        omega
      · rw [sumA]
        rw [sumS] at maxS
        exact maxS
      · have stateA : after.dstates ds = some result := goodA.live.hs
        simp only [rank, goodS.live.hs, stateA, Option.map_some, Option.getD_some]
        rw [countA]
        omega
  have initial : Inv hash_head h :=
    ⟨d, good, chains, win, get, positive, countBound, lookahead, rfl, rfl, room, maximum, form, rfl⟩
  have fuelBound : rank hash_head h < fuel := by
    simp only [rank, good.live.hs, Option.map_some, Option.getD_some]
    change d.prev_length.toNat < 18446744073709551616
    omega
  obtain ⟨candidate, after, run, result, post⟩ := do_heap_rank Inv rank Q step initial fuelBound
  exact ⟨candidate, after, result, run, post⟩

end Zlib.Deflate.Engine.Proofs
