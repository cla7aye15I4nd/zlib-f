import ZlibF.Proof.«deflate.c.engine.match-consume»

/-! # One actual insertion iteration while consuming a slow match -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def bumpStart (d : DeflateState) : DeflateState := { d with strstart := d.strstart + 1 }
def countDown (d : DeflateState) : DeflateState := { d with prev_length := d.prev_length - 1 }

theorem bump_start_good {h : Heap} {r : ZStreamRef} {ds w top : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d top)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (room : d.strstart.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat) :
    (bumpStart d).strstart.toNat = d.strstart.toNat + 1 ∧
      DGood (setD h ds (bumpStart d)) r ds z (bumpStart d) ∧
      HeapChains (setD h ds (bumpStart d)) (bumpStart d) top ∧
      (bumpStart d).strstart.toNat + (bumpStart d).lookahead.toNat ≤ d.window_size.toNat := by
  have extent := window_extent good win get
  have ss : (bumpStart d).strstart.toNat = d.strstart.toNat + 1 := by
    change (d.strstart + 1).toNat = _
    rw [UInt32.toNat_add]
    simp only [show (1 : UInt32).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have inv : DStInv h ds (bumpStart d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  refine ⟨ss, good.setD' (d' := bumpStart d) rfl good.live.status inv (by trkeep), ?_, ?_⟩
  · obtain ⟨w0, p, q, bytes, pa, qa, win0, prev, head, hw, hp, hq, H⟩ := chains
    exact ⟨w0, p, q, bytes, pa, qa, win0, prev, head, hw, hp, hq,
      chains_mono H (Nat.le_refl top) (by change _ ≤ (bumpStart d).strstart.toNat + d.lookahead.toNat; rw [ss]; omega)⟩
  · change (bumpStart d).strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat
    rw [ss]
    exact room

theorem count_down_good {h : Heap} {r : ZStreamRef} {ds top : Nat}
    {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (chains : HeapChains h d top) :
    DGood (setD h ds (countDown d)) r ds z (countDown d) ∧
      HeapChains (setD h ds (countDown d)) (countDown d) top := by
  have inv : DStInv h ds (countDown d) :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  refine ⟨good.setD' (d' := countDown d) rfl good.live.status inv (by trkeep), ?_⟩
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chains
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩

/-- The loop increments strstart, performs the guarded actual insertion,
then decrements prev_length in its condition. The room and max_insert
facts are loop invariants, not callee execution assumptions. -/
theorem slow_match_insert_step_frame {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (positive : 1 ≤ d.prev_length.toNat) (lookahead : 3 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + d.prev_length.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (max_insert : UInt32) (maximum : d.strstart.toNat + d.prev_length.toNat ≤ max_insert.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (hash_head : UInt32) :
    ∃ key candidate mid after,
      let result := countDown { bumpStart d with ins_h := key }
      slowMatchBody (some (.tab ds)) max_insert hash_head h = .ok (candidate, mid) ∧
      slowMatchCond (some (.tab ds)) candidate mid = .ok ((result.prev_length != 0, candidate), after) ∧
      DGood after r ds z result ∧ HeapChains after result (result.strstart.toNat + 1) ∧
      after.bytes w = some wa ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.prev_length.toNat = d.prev_length.toNat - 1 ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h ∧ after.bytes = h.bytes := by
  have bumped := bump_start_good good chains win get (by omega)
  let hb := setD h ds (bumpStart d)
  have getB : hb.bytes w = some wa := get
  have primed : InsHForm (bumpStart d).hash_shift (bumpStart d).hash_mask (bfn wa)
      (bumpStart d).strstart.toNat (bumpStart d).ins_h := by
    change InsHForm d.hash_shift d.hash_mask (bfn wa) (bumpStart d).strstart.toNat d.ins_h
    rw [bumped.1]
    exact form
  obtain ⟨key, candidate, mid, insert, goodI, chainsI, bytesI, formI⟩ := current_insert
    bumped.2.1 bumped.2.2.1 win getB (by rw [bumped.1]; omega) bumped.2.2.2 lookahead primed
  let di := { bumpStart d with ins_h := key }
  let after := setD mid ds (countDown di)
  have kept := count_down_good goodI chainsI
  have ss : (countDown di).strstart.toNat = d.strstart.toNat + 1 := bumped.1
  have count : (countDown di).prev_length.toNat = d.prev_length.toNat - 1 := u32_sub_one positive
  have write : wr (some (.tab ds)) bumpStart h = .ok ((), hb) := by simp [wrD_eq, good.live.hs, hb]
  have guard : (bumpStart d).strstart ≤ max_insert := by
    rw [UInt32.le_iff_toNat_le, bumped.1]
    omega
  have body : slowMatchBody (some (.tab ds)) max_insert hash_head h = .ok (candidate, mid) := by
    unfold slowMatchBody
    change (do
      wr (some (.tab ds)) bumpStart
      let ss ← rd (some (.tab ds)) (·.strstart)
      if ss ≤ max_insert then INSERT_STRING (some (.tab ds)) ss else pure hash_head) h = _
    rw [bind_app, write]
    have stateB : hb.dstates ds = some (bumpStart d) := bumped.2.1.live.hs
    simp only [bind_app, rdD_eq, stateB, guard, if_true]
    exact insert
  have condition : slowMatchCond (some (.tab ds)) candidate mid =
      .ok (((countDown di).prev_length != 0, candidate), after) := by
    unfold slowMatchCond
    change (do
      wr (some (.tab ds)) countDown
      pure ((← rd (some (.tab ds)) (·.prev_length)) != 0, candidate)) mid = _
    have put : wr (some (.tab ds)) countDown mid = .ok ((), after) := by
      simp [wrD_eq, goodI.live.hs, after, di]
    rw [bind_app, put]
    have stateA : after.dstates ds = some (countDown di) := kept.1.live.hs
    simp only [bind_app, rdD_eq, stateA]
    rfl
  refine ⟨key, candidate, mid, after, body, condition, kept.1, kept.2, ?_, ss, count, ?_, ?_⟩
  · change mid.bytes w = some wa
    rw [bytesI]
    exact getB
  · exact formI
  · exact bytesI


/-- The original step contract; the stronger helper also retains the byte frame. -/
theorem slow_match_insert_step {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (chains : HeapChains h d (d.strstart.toNat + 1))
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (positive : 1 ≤ d.prev_length.toNat) (lookahead : 3 ≤ d.lookahead.toNat)
    (room : d.strstart.toNat + d.prev_length.toNat + 1 + d.lookahead.toNat ≤ d.window_size.toNat)
    (max_insert : UInt32) (maximum : d.strstart.toNat + d.prev_length.toNat ≤ max_insert.toNat)
    (form : InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h)
    (hash_head : UInt32) :
    ∃ key candidate mid after,
      let result := countDown { bumpStart d with ins_h := key }
      slowMatchBody (some (.tab ds)) max_insert hash_head h = .ok (candidate, mid) ∧
      slowMatchCond (some (.tab ds)) candidate mid = .ok ((result.prev_length != 0, candidate), after) ∧
      DGood after r ds z result ∧ HeapChains after result (result.strstart.toNat + 1) ∧
      after.bytes w = some wa ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.prev_length.toNat = d.prev_length.toNat - 1 ∧
      InsHForm result.hash_shift result.hash_mask (bfn wa) (result.strstart.toNat + 1) result.ins_h := by
  obtain ⟨key, candidate, mid, after, body, condition, goodA, chainsA, bytesA, startA, countA, formA, _⟩ :=
    slow_match_insert_step_frame good chains win get positive lookahead room max_insert maximum form hash_head
  exact ⟨key, candidate, mid, after, body, condition, goodA, chainsA, bytesA, startA, countA, formA⟩

end Zlib.Deflate.Engine.Proofs
