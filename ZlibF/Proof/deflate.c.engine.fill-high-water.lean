import ZlibF.Proof.«deflate.c.engine.fill-read-resume»

/-! # Complete high-water padding at an arbitrary window position -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
set_option autoImplicit false

def paddingStart (d : DeflateState) : Nat := max (fillEnd d) d.high_water.toNat
def paddingTarget (d : DeflateState) : Nat := max d.high_water.toNat (min (fillEnd d + 258) d.window_size.toNat)
def paddingCount (d : DeflateState) : Nat := paddingTarget d - paddingStart d
def paddedState (d : DeflateState) : DeflateState := { d with high_water := UInt64.ofNat (paddingTarget d) }
def paddedHeap (h : Heap) (ds w : Nat) (d : DeflateState) (wa : Array UInt8) : Heap :=
  setD { h with bytes := upd h.bytes w (some (fillRange wa (paddingStart d) (paddingCount d) 0)) }
    ds (paddedState d)

theorem padding_bounds (d : DeflateState) (range : fillEnd d ≤ d.window_size.toNat)
    (high : d.high_water.toNat ≤ d.window_size.toNat) :
    fillEnd d ≤ paddingStart d ∧ paddingStart d ≤ paddingTarget d ∧
      paddingStart d + paddingCount d = paddingTarget d ∧
      paddingTarget d ≤ d.window_size.toNat ∧ paddingCount d ≤ 258 ∧
      min (fillEnd d + 258) d.window_size.toNat ≤ paddingTarget d := by
  simp only [paddingCount, paddingStart, paddingTarget]
  omega

def highWaterWrite (s : DeflateStatePtr) (window : BPtr) (start count : UInt64) (bump : Bool) : M Unit := do
  memsetB (← padd window start.toNat) 0 count.toUInt32.toNat
  wr s (fun d => { d with high_water := if bump then d.high_water + count else start + count })

theorem high_water_write {h : Heap} {ds w : Nat} {d : DeflateState} {wa : Array UInt8}
    (state : h.dstates ds = some d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false)
    (start count : UInt64) (bump : Bool) (base : bump = true → start = d.high_water) (fit : start.toNat + count.toNat ≤ wa.size)
    (small : count.toNat < 2 ^ 32) :
    highWaterWrite (some (.tab ds)) d.window start count bump h = .ok ((),
      setD { h with bytes := upd h.bytes w (some (fillRange wa start.toNat count.toNat 0)) }
        ds { d with high_water := start + count }) := by
  have cast : count.toUInt32.toNat = count.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt small]
  have add : padd d.window start.toNat h = .ok (.ref (.blk w) start.toNat, h) := by
    rw [win]
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok (off := 0) (n := start.toNat)
      (show Space.get h (BRef.blk w) = some wa from get) (by omega)
  have fill : memsetB (.ref (.blk w) start.toNat) 0 count.toNat h =
      .ok ((), { h with bytes := upd h.bytes w (some (fillRange wa start.toNat count.toNat 0)) }) :=
    Ptr.fill_ok get writable fit
  unfold highWaterWrite
  rw [bind_app, add]
  simp only [cast]
  rw [bind_app, fill]
  cases bump with
  | false => simp [wrD_eq, state]
  | true => have eq := base rfl; simp [wrD_eq, state, eq]

theorem padded_heap_idle {h : Heap} {ds w : Nat} {d : DeflateState} {wa : Array UInt8}
    (state : h.dstates ds = some d) (get : h.bytes w = some wa)
    (start : paddingStart d = d.high_water.toNat) (target : paddingTarget d = d.high_water.toNat) :
    paddedHeap h ds w d wa = h := by
  have count : paddingCount d = 0 := by simp only [paddingCount, start, target, Nat.sub_self]
  simp only [paddedHeap, count, fillRange, List.range_zero, List.foldl_nil,
    upd_self _ _ _ get, paddedState, target, UInt64.ofNat_toNat]
  exact setD_self state

set_option maxHeartbeats 1200000 in
/-- Actual padding after an arbitrary read or resumption. Both source
zeroing branches and both no-op branches are included. The final extent
is derived from the existing high-water mark and the valid-data endpoint.
-/
theorem fill_high_water_complete {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (good : DGood h r ds z d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false)
    (range : fillEnd d ≤ d.window_size.toNat) :
    fillHighWater (some (.tab ds)) h = .ok ((), paddedHeap h ds w d wa) := by
  have extent := window_extent good win get
  have bounds := padding_bounds d range good.inv.hw
  let curr := d.strstart.toUInt64 + d.lookahead.toUInt64
  have current : curr.toNat = fillEnd d := by
    rw [UInt64.toNat_add, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, Nat.mod_eq_of_lt (by
      dsimp only [fillEnd] at range
      omega)]
    rfl
  have extra : (curr + WIN_INIT_u).toNat = fillEnd d + 258 := by
    rw [UInt64.toNat_add, current]
    change (fillEnd d + 258) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  by_cases active : d.high_water < d.window_size
  · have highLt : d.high_water.toNat < d.window_size.toNat := UInt64.lt_iff_toNat_lt.mp active
    by_cases first : d.high_water < curr
    · have before : d.high_water.toNat < fillEnd d := by simpa only [current] using UInt64.lt_iff_toNat_lt.mp first
      let count := if d.window_size - curr > WIN_INIT_u then WIN_INIT_u else d.window_size - curr
      have left : (d.window_size - curr).toNat = d.window_size.toNat - fillEnd d := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, current]; exact range), current]
      have countNat : count.toNat = min (d.window_size.toNat - fillEnd d) 258 := by
        unfold count
        split
        · rename_i large
          change WIN_INIT_u < d.window_size - curr at large
          rw [UInt64.lt_iff_toNat_lt, left] at large
          change 258 < d.window_size.toNat - fillEnd d at large
          simpa only [show WIN_INIT_u.toNat = 258 from rfl] using (Nat.min_eq_right (by omega)).symm
        · rename_i small
          change ¬ WIN_INIT_u < d.window_size - curr at small
          rw [UInt64.lt_iff_toNat_lt, left] at small
          change ¬ 258 < d.window_size.toNat - fillEnd d at small
          rw [left, Nat.min_eq_left (by omega)]
      have startPlan : paddingStart d = curr.toNat := by unfold paddingStart; omega
      have countPlan : paddingCount d = count.toNat := by unfold paddingCount paddingStart paddingTarget; omega
      have targetPlan : (curr + count) = UInt64.ofNat (paddingTarget d) := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, current, countNat, UInt64.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        unfold paddingTarget
        omega
      have write := high_water_write good.live.hs win get writable curr count false (by intro eq; contradiction)
        (by rw [← startPlan, ← countPlan, bounds.2.2.1, extent.1]; exact bounds.2.2.2.1)
        (by rw [countNat]; omega)
      have run : highWaterWrite (some (.tab ds)) d.window curr count false h =
          .ok ((), paddedHeap h ds w d wa) := by
        simpa only [← startPlan, ← countPlan, targetPlan, paddedHeap, paddedState] using write
      dsimp only [highWaterWrite, curr, count] at run
      dsimp only [curr] at first
      unfold fillHighWater
      simp only [bind_app, ldDeflateState_tab good.live.hs, active, if_true, first]
      by_cases large : d.window_size - (d.strstart.toUInt64 + d.lookahead.toUInt64) > WIN_INIT_u
      all_goals simpa only [large, Bool.false_eq_true, if_true, if_false] using run
    · have after : fillEnd d ≤ d.high_water.toNat := by
        have notlt := first
        rw [UInt64.lt_iff_toNat_lt, current] at notlt
        omega
      by_cases second : d.high_water < curr + WIN_INIT_u
      · have below : d.high_water.toNat < fillEnd d + 258 := by
          simpa only [extra] using UInt64.lt_iff_toNat_lt.mp second
        let initial := curr + WIN_INIT_u - d.high_water
        let left := d.window_size - d.high_water
        let count := if initial > left then left else initial
        have initNat : initial.toNat = fillEnd d + 258 - d.high_water.toNat := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, extra]; omega), extra]
        have leftNat : left.toNat = d.window_size.toNat - d.high_water.toNat := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
        have countNat : count.toNat = min (fillEnd d + 258 - d.high_water.toNat)
            (d.window_size.toNat - d.high_water.toNat) := by
          unfold count
          split
          · rename_i large
            change left < initial at large
            rw [UInt64.lt_iff_toNat_lt, initNat, leftNat] at large
            rw [leftNat, Nat.min_eq_right (by omega)]
          · rename_i small
            change ¬ left < initial at small
            rw [UInt64.lt_iff_toNat_lt, initNat, leftNat] at small
            rw [initNat, Nat.min_eq_left (by omega)]
        have startPlan : paddingStart d = d.high_water.toNat := by unfold paddingStart; omega
        have countPlan : paddingCount d = count.toNat := by unfold paddingCount paddingStart paddingTarget; omega
        have targetPlan : d.high_water + count = UInt64.ofNat (paddingTarget d) := by
          apply UInt64.toNat_inj.mp
          rw [UInt64.toNat_add, countNat, UInt64.toNat_ofNat',
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
          unfold paddingTarget
          omega
        have write := high_water_write good.live.hs win get writable d.high_water count true (by intro _; rfl)
          (by rw [← startPlan, ← countPlan, bounds.2.2.1, extent.1]; exact bounds.2.2.2.1)
          (by rw [countNat]; omega)
        have run : highWaterWrite (some (.tab ds)) d.window d.high_water count true h =
            .ok ((), paddedHeap h ds w d wa) := by
          simpa only [← startPlan, ← countPlan, targetPlan, paddedHeap, paddedState] using write
        dsimp only [highWaterWrite, curr, count, initial, left] at run
        dsimp only [curr] at first second
        unfold fillHighWater
        simp only [bind_app, ldDeflateState_tab good.live.hs, active, if_true, first, if_false, second]
        by_cases large : d.strstart.toUInt64 + d.lookahead.toUInt64 + WIN_INIT_u - d.high_water >
          d.window_size - d.high_water
        all_goals simpa only [large, Bool.false_eq_true, if_true, if_false] using run
      · have past : fillEnd d + 258 ≤ d.high_water.toNat := by
          have notlt := second
          rw [UInt64.lt_iff_toNat_lt, extra] at notlt
          omega
        have startPlan : paddingStart d = d.high_water.toNat := by unfold paddingStart; omega
        have targetPlan : paddingTarget d = d.high_water.toNat := by unfold paddingTarget; omega
        rw [padded_heap_idle good.live.hs get startPlan targetPlan]
        dsimp only [curr] at first second
        unfold fillHighWater
        simp only [bind_app, ldDeflateState_tab good.live.hs, active, if_true, first, if_false, second]
        rfl
  · have full : d.high_water.toNat = d.window_size.toNat := by
      have notlt := active
      rw [UInt64.lt_iff_toNat_lt] at notlt
      have high := good.inv.hw
      omega
    have startPlan : paddingStart d = d.high_water.toNat := by unfold paddingStart; omega
    have targetPlan : paddingTarget d = d.high_water.toNat := by unfold paddingTarget; omega
    rw [padded_heap_idle good.live.hs get startPlan targetPlan]
    unfold fillHighWater
    simp only [bind_app, ldDeflateState_tab good.live.hs, active, if_false]
    rfl

end Zlib.Deflate.Engine.Proofs
