import ZlibF.Proof.«deflate.c.engine.fill-insert-step»

/-! # The complete deferred-insertion loop and its real heap counter -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

theorem while_heap_rank {σ : Type} {cond : σ → M (Bool × σ)} {body : σ → M σ}
    (Inv : σ → Heap → Prop) (rank : σ → Heap → Nat) (Q : σ → Heap → Prop)
    (step : ∀ s h, Inv s h → ∃ c s1 h1,
      cond s h = .ok ((c, s1), h1) ∧ (c = false → Q s1 h1) ∧
      (c = true → ∃ s2 h2, body s1 h1 = .ok (s2, h2) ∧ Inv s2 h2 ∧ rank s2 h2 < rank s h))
    {s : σ} {h : Heap} (initial : Inv s h) (bound : rank s h < fuel) :
    ∃ result after, cwhile cond body s h = .ok (result, after) ∧ Q result after := by
  have run : ∀ n s h, Inv s h → rank s h < n →
      ∃ result after, cwhile.go cond body n s h = .ok (result, after) ∧ Q result after := by
    intro n
    induction n with
    | zero => intro s h _ hn; omega
    | succ n ih =>
      intro s h inv hn
      obtain ⟨c, s1, h1, condition, stopped, continued⟩ := step s h inv
      cases c with
      | false => exact ⟨s1, h1, by simp [cwhile.go, condition], stopped rfl⟩
      | true =>
        obtain ⟨s2, h2, bodyRun, next, less⟩ := continued rfl
        obtain ⟨result, after, rest, post⟩ := ih s2 h2 next (by omega)
        exact ⟨result, after, by simp [cwhile.go, condition, bodyRun, rest], post⟩
  exact run fuel s h initial bound

def PendingInsertFrame (before after : DeflateState) : Prop :=
  after = { before with ins_h := after.ins_h, insert := after.insert }

theorem pending_insert_frame_step {before state : DeflateState}
    (frame : PendingInsertFrame before state) (key : UInt32) :
    PendingInsertFrame before (pendingInsertState state key) := by
  unfold PendingInsertFrame at *
  rw [frame]
  rfl

set_option maxHeartbeats 2000000 in
/-- The actual source while loop inserts every pending three-byte string.
It stops at insert=0 or exactly two remaining bytes. The counter in the
real heap is its rank. The hash frontier advances with the local cursor,
while strstart and lookahead stay unchanged.
-/
theorem fill_insert_loop_storage {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} (str : UInt32)
    (good : DGood h r ds z d) (chains : HeapChains h d str.toNat)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (cursor : str.toNat + d.insert.toNat = d.strstart.toNat)
    (ready : 3 ≤ d.lookahead.toNat + d.insert.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ final after result,
      cwhile (fillInsertCond (some (.tab ds))) (fillInsertBody (some (.tab ds))) (str, false) h =
        .ok (final, after) ∧
      DGood after r ds z result ∧ HeapChains after result final.1.toNat ∧ after.bytes = h.bytes ∧
      PendingInsertFrame d result ∧ final.1.toNat + result.insert.toNat = d.strstart.toNat ∧
      result.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) final.1.toNat result.ins_h ∧ ByteFrame h after (fun i => i = ds) := by
  let Inv : (UInt32 × Bool) → Heap → Prop := fun pos heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChains heap state pos.1.toNat ∧
    state.window = .ref (.blk w) 0 ∧ heap.bytes w = some wa ∧
    state.strstart.toNat + state.lookahead.toNat ≤ state.window_size.toNat ∧
    pos.1.toNat + state.insert.toNat = state.strstart.toNat ∧
    state.insert.toNat ≤ d.insert.toNat ∧ 2 ≤ state.lookahead.toNat + state.insert.toNat ∧
    pos.2 = decide (state.lookahead.toNat + state.insert.toNat < 3) ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) pos.1.toNat state.ins_h ∧
    PendingInsertFrame d state ∧ heap.bytes = h.bytes ∧ ByteFrame h heap (fun i => i = ds)
  let Q : (UInt32 × Bool) → Heap → Prop := fun pos heap => ∃ state : DeflateState,
    DGood heap r ds z state ∧ HeapChains heap state pos.1.toNat ∧ heap.bytes = h.bytes ∧
    PendingInsertFrame d state ∧ pos.1.toNat + state.insert.toNat = d.strstart.toNat ∧
    state.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) ∧
    InsHForm state.hash_shift state.hash_mask (bfn wa) pos.1.toNat state.ins_h ∧ ByteFrame h heap (fun i => i = ds)
  let rank : (UInt32 × Bool) → Heap → Nat := fun _ heap =>
    ((heap.dstates ds).map (fun state => state.insert.toNat)).getD 0
  have step : ∀ pos heap, Inv pos heap → ∃ c pos1 heap1,
      fillInsertCond (some (.tab ds)) pos heap = .ok ((c, pos1), heap1) ∧
      (c = false → Q pos1 heap1) ∧
      (c = true → ∃ pos2 heap2, fillInsertBody (some (.tab ds)) pos1 heap1 = .ok (pos2, heap2) ∧
        Inv pos2 heap2 ∧ rank pos2 heap2 < rank pos heap) := by
    intro pos heap inv
    obtain ⟨state, goodS, chainsS, winS, getS, rangeS, cursorS, boundS, lowerS, stopS, formS, frameS, bytesS, storageS⟩ := inv
    have startS : state.strstart = d.strstart := congrArg (·.strstart) frameS
    have lookS : state.lookahead = d.lookahead := congrArg (·.lookahead) frameS
    refine ⟨state.insert != 0 && !pos.2, pos, heap, ?_, ?_, ?_⟩
    · simp only [fillInsertCond, bind_app, rdD_eq, goodS.live.hs, pure_app]
    · intro stopped
      have exit : state.insert.toNat = 0 ∨ state.lookahead.toNat + state.insert.toNat < 3 := by
        by_cases zero : state.insert = 0
        · left; rw [zero]; rfl
        · right
          have flag : pos.2 = true := by
            simpa [bne_iff_ne, zero] using stopped
          rw [stopS] at flag
          exact of_decide_eq_true flag
      have count : state.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) := by
        rw [lookS] at lowerS exit
        rcases exit with zero | small <;> omega
      exact ⟨state, goodS, chainsS, bytesS, frameS, by rw [startS] at cursorS; exact cursorS, count, formS, storageS⟩
    · intro continued
      have guard := continued
      simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true] at guard
      have positive : 1 ≤ state.insert.toNat := by
        have ne : state.insert.toNat ≠ 0 := by intro eq; exact guard.1 (UInt32.toNat_inj.mp eq)
        omega
      have readyS : 3 ≤ state.lookahead.toNat + state.insert.toNat := by
        have falseFlag : pos.2 = false := by
          cases bit : pos.2
          · rfl
          · have impossible : False := by simpa [bit] using guard.2
            cases impossible
        have flag : decide (state.lookahead.toNat + state.insert.toNat < 3) = false :=
          stopS.symm.trans falseFlag
        have notLow := of_decide_eq_false flag
        omega
      obtain ⟨key, after, bodyRun, goodA, chainsA, bytesA, next, countA, formA, storageA⟩ :=
        fill_insert_step_storage pos.1 pos.2 goodS chainsS winS getS rangeS cursorS positive readyS formS
      let result := pendingInsertState state key
      let stopped : Bool := decide (result.lookahead + result.insert < MIN_MATCH_u)
      let nextPos := (pos.1 + 1, stopped)
      have cursorA : nextPos.1.toNat + result.insert.toNat = result.strstart.toNat := by
        change (pos.1 + 1).toNat + result.insert.toNat = state.strstart.toNat
        rw [next, countA]
        omega
      have rangeA : result.strstart.toNat + result.lookahead.toNat ≤ result.window_size.toNat := rangeS
      have getA : after.bytes w = some wa := by rw [bytesA]; exact getS
      have sum := pending_sum_nat goodA winS getA rangeA (by omega : result.insert.toNat ≤ result.strstart.toNat)
      change (result.lookahead + result.insert).toNat = result.lookahead.toNat + result.insert.toNat at sum
      have stopA : nextPos.2 = decide (result.lookahead.toNat + result.insert.toNat < 3) := by
        change decide (result.lookahead + result.insert < MIN_MATCH_u) = _
        simp only [UInt32.lt_iff_toNat_lt, sum, show MIN_MATCH_u.toNat = 3 from rfl]
      refine ⟨nextPos, after, bodyRun, ⟨result, goodA, ?_, winS, getA, rangeA, cursorA, ?_, ?_, stopA,
        ?_, pending_insert_frame_step frameS key, bytesA.trans bytesS, storageS.trans storageA⟩, ?_⟩
      · change HeapChains after result (pos.1 + 1).toNat
        rw [next]
        exact chainsA
      · rw [countA]
        omega
      · change 2 ≤ state.lookahead.toNat + result.insert.toNat
        rw [countA]
        omega
      · change InsHForm result.hash_shift result.hash_mask (bfn wa) (pos.1 + 1).toNat result.ins_h
        rw [next]
        exact formA
      · simp only [rank, goodS.live.hs, goodA.live.hs, Option.map_some, Option.getD_some]
        rw [countA]
        omega
  have initial : Inv (str, false) h :=
    ⟨d, good, chains, win, get, range, cursor, Nat.le_refl _, by omega,
      by simp [show ¬ d.lookahead.toNat + d.insert.toNat < 3 by omega], form, rfl, rfl, ByteFrame.refl h _⟩
  have extent := window_extent good win get
  have bound : rank (str, false) h < fuel := by
    simp only [rank, good.live.hs, Option.map_some, Option.getD_some]
    change d.insert.toNat < 18446744073709551616
    omega
  obtain ⟨final, after, run, result, goodA, chainsA, bytesA, frameA, cursorA, countA, formA, storageA⟩ :=
    while_heap_rank Inv rank Q step initial bound
  exact ⟨final, after, result, run, goodA, chainsA, bytesA, frameA, cursorA, countA, formA, storageA⟩

/-- The earlier complete loop statement retains its scope. -/
theorem fill_insert_loop {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} (str : UInt32)
    (good : DGood h r ds z d) (chains : HeapChains h d str.toNat)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (cursor : str.toNat + d.insert.toNat = d.strstart.toNat)
    (ready : 3 ≤ d.lookahead.toNat + d.insert.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) str.toNat d.ins_h) :
    ∃ final after result,
      cwhile (fillInsertCond (some (.tab ds))) (fillInsertBody (some (.tab ds))) (str, false) h =
        .ok (final, after) ∧
      DGood after r ds z result ∧ HeapChains after result final.1.toNat ∧ after.bytes = h.bytes ∧
      PendingInsertFrame d result ∧ final.1.toNat + result.insert.toNat = d.strstart.toNat ∧
      result.insert.toNat = min d.insert.toNat (2 - d.lookahead.toNat) ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) final.1.toNat result.ins_h := by
  obtain ⟨final, after, result, run, goodA, chainsA, bytesA, frameA, cursorA, countA, formA, _⟩ :=
    fill_insert_loop_storage str good chains win get range cursor ready form
  exact ⟨final, after, result, run, goodA, chainsA, bytesA, frameA, cursorA, countA, formA⟩

end Zlib.Deflate.Engine.Proofs
