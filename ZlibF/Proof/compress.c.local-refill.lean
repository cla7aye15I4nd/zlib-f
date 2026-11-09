import ZlibF.Proof.«compress.c.local-fill»
import ZlibF.Proof.«deflate.c.engine.fill-resume»

/-! # Real no-slide refills with local private representation

Existing buffered data and caller typed collisions are retained. The real
read, priming, loop exit and padding execute from LocalState. No global
uniqueness premise or called specification is introduced.
-/
namespace ZlibF.Spec.Public.Proofs.CompressLocalRefill
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit
open ZlibF.Spec.Public.Proofs.CompressLocal
open ZlibF.Spec.Public.Proofs.CompressLocalHeader
open ZlibF.Spec.Public.Proofs.CompressLocalFill
open Zlib.Deflate.Proofs.DefaultInit
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
theorem local_window_extent {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa) :
    wa.size = d.window_size.toNat ∧ d.window_size.toNat ≤ 65536 := by
  obtain ⟨w0, p, q, b, blocks⟩ := state.inv.blocks
  have wid : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  subst w0
  obtain ⟨wa0, get0, size⟩ := blocks.wa
  have array : wa0 = wa := Option.some.inj (get0.symm.trans get)
  subst wa0
  have ws : d.w_size.toNat ≤ 32768 := by
    rw [state.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) state.inv.wbits_hi
         _ = 32768 := by decide
  rw [state.inv.wsz]
  exact ⟨size, by omega⟩

theorem local_window_writable {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} (state : LocalState h cutoff r ds z d)
    (win : d.window = .ref (.blk w) 0) : h.ro w = false := by
  obtain ⟨w0, p, q, b, blocks⟩ := state.inv.blocks
  have same : w0 = w := by
    simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
  subst w0
  exact blocks.wro

theorem local_fill_more_nat {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat) :
    (fillMore d).toNat = d.window_size.toNat - (d.strstart.toNat + d.lookahead.toNat) := by
  have extent := local_window_extent state win get
  have first : (d.window_size - d.lookahead.toUInt64).toNat = d.window_size.toNat - d.lookahead.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt32.toNat_toUInt64]; omega),
      UInt32.toNat_toUInt64]
  have second : (d.window_size - d.lookahead.toUInt64 - d.strstart.toUInt64).toNat =
      d.window_size.toNat - (d.strstart.toNat + d.lookahead.toNat) := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, first, UInt32.toNat_toUInt64]; omega),
      first, UInt32.toNat_toUInt64]
    omega
  unfold fillMore
  rw [UInt64.toNat_toUInt32, second, Nat.mod_eq_of_lt (by omega)]

theorem local_fill_room_no_slide {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : d.strstart.toNat + d.lookahead.toNat ≤ d.window_size.toNat)
    (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u)) :
    0 < (fillMore d).toNat ∧ 262 ≤ d.lookahead.toNat + (fillMore d).toNat := by
  have wsUpper : d.w_size.toNat ≤ 32768 := by
    rw [state.inv.wsize]
    calc 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) state.inv.wbits_hi
         _ = 32768 := by decide
  have wsLower : 512 ≤ d.w_size.toNat := by
    rw [state.inv.wsize]
    have power := Nat.pow_le_pow_right (n := 2) (by decide) state.inv.wbits_lo
    exact power
  have sub : (d.w_size - MIN_LOOKAHEAD_u).toNat = d.w_size.toNat - 262 := by
    rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; change 262 ≤ _; omega)]
    rfl
  have threshold : (d.w_size + (d.w_size - MIN_LOOKAHEAD_u)).toNat = 2 * d.w_size.toNat - 262 := by
    rw [UInt32.toNat_add, sub, Nat.mod_eq_of_lt (by omega)]
    omega
  change ¬ d.w_size + (d.w_size - MIN_LOOKAHEAD_u) ≤ d.strstart at noSlide
  rw [UInt32.le_iff_toNat_le, threshold] at noSlide
  rw [local_fill_more_nat state win get range, state.inv.wsz]
  rw [state.inv.wsz] at range
  exact ⟨by omega, by omega⟩

theorem local_resume_read_counts {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) :
    let n := rbLen z.avail_in (fillMore d)
    n.toNat = min z.avail_in.toNat (d.window_size.toNat - fillEnd d) ∧
      (d.lookahead + n).toNat = d.lookahead.toNat + n.toNat ∧
      d.strstart.toNat + (d.lookahead + n).toNat ≤ d.window_size.toNat := by
  have count := rbLen_nat z.avail_in (fillMore d)
  rw [local_fill_more_nat state win get range] at count
  have extent := local_window_extent state win get
  have add : (d.lookahead + rbLen z.avail_in (fillMore d)).toNat =
      d.lookahead.toNat + (rbLen z.avail_in (fillMore d)).toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by dsimp only [fillEnd] at range; omega)]
  exact ⟨count, add, by rw [add]; dsimp only [fillEnd] at count range; omega⟩

theorem local_fill_body_resume_read {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false)
    (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ fillEnd d + (rbLen z.avail_in (fillMore d)).toNat ≤ io ∨
      io + (rbLen z.avail_in (fillMore d)).toNat ≤ fillEnd d) :
    fillBody (some (.tab ds)) d.w_size false h =
      .ok (false, resumeReadHeap h r ds w z d ref io ia wa) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  let hr := r.put { h with bytes := upd h.bytes w (some copied) } z'
  let dr := { d with lookahead := d.lookahead + n }
  let hl := setD hr ds dr
  have counts := local_resume_read_counts state win get range
  have room := local_fill_room_no_slide state win get range short noSlide
  have extent := local_window_extent state win get
  have availPositive : 0 < z.avail_in.toNat := by
    have ne : z.avail_in.toNat ≠ 0 := by intro eq; exact nonempty (UInt32.toNat_inj.mp eq)
    omega
  have count : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
  have nonzero : n ≠ 0 := by
    intro zero
    have num : n.toNat = 0 := by rw [zero]; rfl
    omega
  have windowBound : fillEnd d + n.toNat ≤ wa.size := by
    rw [extent.1]
    have more : (fillMore d).toNat = d.window_size.toNat - fillEnd d := local_fill_more_nat state win get range
    omega
  have read := read_buf_zlib (bo := fillEnd d) state.live.hz state.live.zst state.live.hs wrap pointer input
    get writable (fillMore d) nonzero (by omega) windowBound separate
  have first : padd d.window d.strstart.toNat h = .ok (.ref (.blk w) d.strstart.toNat, h) := by
    rw [win]
    simpa only [OkOn, padd, Nat.zero_add] using Ptr.add_nat_ok (off := 0) (n := d.strstart.toNat)
      (show Space.get h (BRef.blk w) = some wa from get) (by dsimp only [fillEnd] at range; omega)
  have second : padd (.ref (.blk w) d.strstart.toNat : BPtr) d.lookahead.toNat h =
      .ok (.ref (.blk w) (fillEnd d), h) := by
    simpa only [OkOn, padd, fillEnd] using Ptr.add_nat_ok (off := d.strstart.toNat) (n := d.lookahead.toNat)
      (show Space.get h (BRef.blk w) = some wa from get) (by omega : fillEnd d ≤ wa.size)
  have stateR : hr.dstates ds = some d := by simpa [hr] using state.live.hs
  have update : wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead + n }) hr =
      .ok ((), hl) := by simp [wrD_eq, stateR, hl, dr]
  have getL : hl.bytes w = some copied := by simp [hl, hr]
  have shift : d.hash_shift < 32 := by
    rw [UInt32.lt_iff_toNat_lt]
    exact (hash_parameters state.inv).hsh_lt
  have prime := fill_prime_resume (h := hl) (ds := ds) (w := w) (d := dr) (wa := copied)
    (by simp [hl]) win getL insert
    (by change d.strstart.toNat + (d.lookahead + n).toNat ≤ copied.size
        rw [size_copyRange, extent.1]
        exact counts.2.2)
    (by simpa [copied, size_copyRange, extent.1] using extent.2) shift
  unfold fillBody
  simp only [bind_app, ldDeflateState_tab state.live.hs, noSlide, ite_false,
    rdD_eq, state.live.hs, state.live.back, zrd_eq, state.live.hz,
    beq_eq_false_iff_ne.mpr nonempty, Bool.false_eq_true]
  change (do
    let dst ← padd (← padd d.window d.strstart.toNat) d.lookahead.toNat
    let n ← read_buf (some r) dst (fillMore d)
    wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead + n })
    fillPrime (some (.tab ds))
    pure false) h = _
  simp only [bind_app, first, second]
  rw [read]
  change (do
    wr (some (.tab ds)) (fun d => { d with lookahead := d.lookahead + n })
    fillPrime (some (.tab ds))
    pure false) hr = _
  rw [bind_app, update]
  simp only []
  rw [bind_app, prime]
  simp only [pure_app, hl, setD_setD]
  rfl

theorem local_resume_read_state {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (get : h.bytes w = some wa) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    LocalState (resumeReadHeap h r ds w z d ref io ia wa) cutoff r ds z' (resumeReadState d n copied) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let hb := { h with bytes := upd h.bytes w (some copied) }
  have bytesGood : LocalState hb cutoff r ds z d := local_state_bytes_set state w copied wa get (size_copyRange _ _ _ _ _)
  obtain ⟨key, record⟩ := resume_prime_record { d with lookahead := d.lookahead + n } copied
  change resumeReadState d n copied = _ at record
  have inv : DStInv hb ds (resumeReadState d n copied) := by
    rw [record]
    exact { bytesGood.inv with blocks := bytesGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have keep : TrKeep d (resumeReadState d n copied) := by rw [record]; trkeep
  have back : (resumeReadState d n copied).strm = d.strm := by rw [record]
  have status : GoodStatus (resumeReadState d n copied).status := by rw [record]; exact state.live.status
  exact local_state_setZD bytesGood rfl state.live.zalloc state.live.zfree back status inv keep

theorem local_fill_high_water_complete {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (writable : h.ro w = false)
    (range : fillEnd d ≤ d.window_size.toNat) :
    fillHighWater (some (.tab ds)) h = .ok ((), paddedHeap h ds w d wa) := by
  have extent := local_window_extent state win get
  have bounds := padding_bounds d range state.inv.hw
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
      have write := high_water_write state.live.hs win get writable curr count false (by intro eq; contradiction)
        (by rw [← startPlan, ← countPlan, bounds.2.2.1, extent.1]; exact bounds.2.2.2.1)
        (by rw [countNat]; omega)
      have run : highWaterWrite (some (.tab ds)) d.window curr count false h =
          .ok ((), paddedHeap h ds w d wa) := by
        simpa only [← startPlan, ← countPlan, targetPlan, paddedHeap, paddedState] using write
      dsimp only [highWaterWrite, curr, count] at run
      dsimp only [curr] at first
      unfold fillHighWater
      simp only [bind_app, ldDeflateState_tab state.live.hs, active, ite_true, first]
      by_cases large : d.window_size - (d.strstart.toUInt64 + d.lookahead.toUInt64) > WIN_INIT_u
      all_goals simpa only [large, Bool.false_eq_true, ite_true, ite_false] using run
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
        have write := high_water_write state.live.hs win get writable d.high_water count true (by intro _; rfl)
          (by rw [← startPlan, ← countPlan, bounds.2.2.1, extent.1]; exact bounds.2.2.2.1)
          (by rw [countNat]; omega)
        have run : highWaterWrite (some (.tab ds)) d.window d.high_water count true h =
            .ok ((), paddedHeap h ds w d wa) := by
          simpa only [← startPlan, ← countPlan, targetPlan, paddedHeap, paddedState] using write
        dsimp only [highWaterWrite, curr, count, initial, left] at run
        dsimp only [curr] at first second
        unfold fillHighWater
        simp only [bind_app, ldDeflateState_tab state.live.hs, active, ite_true, first, ite_false, second]
        by_cases large : d.strstart.toUInt64 + d.lookahead.toUInt64 + WIN_INIT_u - d.high_water >
          d.window_size - d.high_water
        all_goals simpa only [large, Bool.false_eq_true, ite_true, ite_false] using run
      · have past : fillEnd d + 258 ≤ d.high_water.toNat := by
          have notlt := second
          rw [UInt64.lt_iff_toNat_lt, extra] at notlt
          omega
        have startPlan : paddingStart d = d.high_water.toNat := by unfold paddingStart; omega
        have targetPlan : paddingTarget d = d.high_water.toNat := by unfold paddingTarget; omega
        rw [padded_heap_idle state.live.hs get startPlan targetPlan]
        dsimp only [curr] at first second
        unfold fillHighWater
        simp only [bind_app, ldDeflateState_tab state.live.hs, active, ite_true, first, ite_false, second]
        rfl
  · have full : d.high_water.toNat = d.window_size.toNat := by
      have notlt := active
      rw [UInt64.lt_iff_toNat_lt] at notlt
      have high := state.inv.hw
      omega
    have startPlan : paddingStart d = d.high_water.toNat := by unfold paddingStart; omega
    have targetPlan : paddingTarget d = d.high_water.toNat := by unfold paddingTarget; omega
    rw [padded_heap_idle state.live.hs get startPlan targetPlan]
    unfold fillHighWater
    simp only [bind_app, ldDeflateState_tab state.live.hs, active, ite_false]
    rfl

theorem local_padding_target_small {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) : paddingTarget d < 2 ^ 64 := by
  have extent := local_window_extent state win get
  have bounds := padding_bounds d range state.inv.hw
  omega

theorem local_padded_state {h : Heap} {r : ZStreamRef} {cutoff ds w : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some wa)
    (range : fillEnd d ≤ d.window_size.toNat) :
    LocalState (paddedHeap h ds w d wa) cutoff r ds z (paddedState d) := by
  have bounds := padding_bounds d range state.inv.hw
  have small := local_padding_target_small state win get range
  have high : (paddedState d).high_water.toNat ≤ d.window_size.toNat := by
    change (UInt64.ofNat (paddingTarget d)).toNat ≤ _
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt small]
    exact bounds.2.2.2.1
  let array := fillRange wa (paddingStart d) (paddingCount d) 0
  let hb := { h with bytes := upd h.bytes w (some array) }
  have bytesGood : LocalState hb cutoff r ds z d := local_state_bytes_set state w array wa get (size_fillRange _ _ _ _)
  have inv : DStInv hb ds (paddedState d) :=
    { bytesGood.inv with
      hw := high
      blocks := bytesGood.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have stored := local_state_setZD (d' := paddedState d) (z' := z) bytesGood rfl state.live.zalloc state.live.zfree rfl state.live.status inv (by trkeep)
  rwa [ZStreamRef.put_self bytesGood.live.hz] at stored

theorem local_fill_window_resume_run {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (range : fillEnd d ≤ d.window_size.toNat)
    (short : d.lookahead.toNat < 262)
    (noSlide : ¬ d.strstart ≥ d.w_size + (d.w_size - MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io + z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ fillEnd d + (rbLen z.avail_in (fillMore d)).toNat ≤ io ∨
      io + (rbLen z.avail_in (fillMore d)).toNat ≤ fillEnd d) :
    fill_window (some (.tab ds)) h = .ok ((), resumedFillHeap h r ds w z d ref io ia wa) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let df := resumeReadState d n copied
  let hr := resumeReadHeap h r ds w z d ref io ia wa
  let z' := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
  have goodR : LocalState hr cutoff r ds z' df := local_resume_read_state state get
  have count := local_resume_read_counts state win get range
  have capacity := local_fill_room_no_slide state win get range short noSlide
  obtain ⟨key, fields⟩ := resume_read_record d n copied
  change df = _ at fields
  have look : df.lookahead = d.lookahead + n := by rw [fields]
  have rangeR : fillEnd df ≤ df.window_size.toNat := by
    rw [fields]
    exact count.2.2
  have getR : hr.bytes w = some copied := by simp [hr, resumeReadHeap, n, copied]
  have winR : df.window = .ref (.blk w) 0 := by rw [fields]; exact win
  have next : fillCond (some (.tab ds)) false hr = .ok ((false, false), hr) := by
    have exhausted : df.lookahead < MIN_LOOKAHEAD_u → z'.avail_in = 0 := by
      intro small
      rw [UInt32.lt_iff_toNat_lt, look, count.2.1] at small
      change d.lookahead.toNat + n.toNat < 262 at small
      have nCount : n.toNat = min z.avail_in.toNat (fillMore d).toNat := rbLen_nat _ _
      have all : n = z.avail_in := UInt32.toNat_inj.mp (by omega)
      simp only [z', readStream, all, UInt32.sub_self]
    unfold fillCond
    simp only [bind_app, ldDeflateState_tab goodR.live.hs, Bool.false_eq_true, ite_false, goodR.live.back]
    by_cases small : df.lookahead < MIN_LOOKAHEAD_u
    · simp only [small, ite_true, bind_app, zrd_eq, goodR.live.hz, exhausted small]
      rfl
    · simp only [small, ite_false]
      rfl
  have body : fillBody (some (.tab ds)) d.w_size false h = .ok (false, hr) :=
    local_fill_body_resume_read state win get (local_window_writable state win) range short noSlide insert wrap
      pointer input inputBound nonempty separate
  have loop := do_once body next
  have pad := local_fill_high_water_complete goodR winR getR (local_window_writable goodR winR) rangeR
  rw [fill_window_source]
  simp only [bind_app, rdD_eq, state.live.hs, loop]
  exact pad


/-- Normalize the real read/priming/padding stores into one concrete
window replacement, one stream store and one private-state store. -/
theorem local_resumed_heap_exact (h : Heap) (r : ZStreamRef) (ds w : Nat) (z : ZStream) (d : DeflateState)
    (ref : BRef) (io : Nat) (ia wa : Array UInt8) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    let read := resumeReadState d n copied
    let nextZ := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    resumedFillHeap h r ds w z d ref io ia wa =
      setD (r.put {h with bytes := upd h.bytes w (some (fillRange copied (paddingStart read) (paddingCount read) 0))} nextZ) ds (resumedFillState d n copied) := by
  simp only [resumedFillHeap,paddedHeap,resumeReadHeap,setD_bytes,ZStreamRef.put_bytes,
    setD_bytes_commute,setD_setD,←stream_put_bytes,upd_upd]
  rfl

/-- A value replacement in the window, followed by the actual typed stores,
preserves every other typed lookup. Existing collisions are not excluded. -/
theorem local_refill_stores {h : Heap} {r : ZStreamRef} {ds w : Nat}
    {z nextZ : ZStream} {d nextD : DeflateState} {wa output : Array UInt8}
    (live : DLive h r ds z d) (get : h.bytes w = some wa) :
    let after := setD (r.put {h with bytes := upd h.bytes w (some output)} nextZ) ds nextD
    Shape h after ∧ after.nextBlk = h.nextBlk ∧ after.nalloc = h.nalloc ∧
      Frame h after (fun b => StreamRoot r b ∨ b = ds ∨ b = w) ∧
      after.words = h.words ∧ after.gzheaders = h.gzheaders ∧ after.istates = h.istates ∧ after.ro = h.ro ∧
      (∀ b, b ≠ w → after.bytes b = h.bytes b) ∧
      (∀ b, b ≠ ds → after.dstates b = h.dstates b) ∧
      (∀ b, ¬StreamRoot r b → after.streams b = h.streams b ∧ after.gzstates b = h.gzstates b) := by
  let copied := {h with bytes := upd h.bytes w (some output)}
  have getC : r.get copied = some z := by simpa only [copied,stream_get_bytes] using live.hz
  have shape := ((shape_setB get output).trans (shape_put getC nextZ)).trans
    (shape_setD (by simpa using live.hs) nextD)
  refine ⟨shape,by simp,by simp,?_,by simp,by simp,by simp,by simp,?_,?_,?_⟩
  · refine ⟨by simp,by simp,by simp,by simp,by simp,?_⟩
    intro b _ outside
    have root : ¬StreamRoot r b := fun same => outside (Or.inl same)
    have state : b ≠ ds := fun same => outside (Or.inr (Or.inl same))
    have byte : b ≠ w := fun same => outside (Or.inr (Or.inr same))
    have before : SlotSame h copied b := by simp [SlotSame,copied,upd_ne _ _ _ _ byte]
    exact before.trans ((slot_put_except copied r nextZ b root).trans
      (slot_setD_except (r.put copied nextZ) ds nextD b state))
  · intro b different
    simp [upd_ne _ _ _ _ different]
  · intro b different
    simp [setD,upd_ne _ _ _ _ different]
  · intro b outside
    have slot := slot_put_except copied r nextZ b outside
    exact ⟨slot.2.2.1,slot.2.2.2.2.2.2.1⟩

/-- The complete no-slide resumed call returns actual local representation,
exact input/output counts, a precise typed frame and copied/padded window.
Its old buffered bytes are unrestricted; no deferred insertions are present. -/
theorem local_fill_window_resume {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (state : LocalState h cutoff r ds z d) (win : d.window = .ref (.blk w) 0)
    (get : h.bytes w = some wa) (range : fillEnd d ≤ d.window_size.toNat) (short : d.lookahead.toNat < 262)
    (noSlide : ¬d.strstart ≥ d.w_size+(d.w_size-MIN_LOOKAHEAD_u))
    (insert : d.insert = 0) (wrap : d.wrap = 1)
    (pointer : z.next_in = .ref ref io) (input : Space.get h ref = some ia)
    (inputBound : io+z.avail_in.toNat ≤ ia.size) (nonempty : z.avail_in ≠ 0)
    (separate : BRef.blk w ≠ ref ∨ fillEnd d+(rbLen z.avail_in (fillMore d)).toNat ≤ io ∨
      io+(rbLen z.avail_in (fillMore d)).toNat ≤ fillEnd d) :
    let n := rbLen z.avail_in (fillMore d)
    let copied := copyRange wa ia (fillEnd d) io n.toNat
    let read := resumeReadState d n copied
    let result := resumedFillState d n copied
    let output := fillRange copied (paddingStart read) (paddingCount read) 0
    let nextZ := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat))
    let after := resumedFillHeap h r ds w z d ref io ia wa
    fill_window (some (.tab ds)) h = .ok ((),after) ∧
      LocalState after cutoff r ds nextZ result ∧ StreamAccounting z nextZ n.toNat 0 ∧
      Frame h after (fun b => StreamRoot r b ∨ b = ds ∨ b = w) ∧ Shape h after ∧
      after.bytes w = some output ∧
      n.toNat = min z.avail_in.toNat (d.window_size.toNat-fillEnd d) ∧
      fillEnd result = fillEnd d+n.toNat ∧ result.strstart = d.strstart ∧
      result.status = d.status ∧ result.level = d.level ∧ result.strategy = d.strategy ∧
      min (fillEnd result+258) result.window_size.toNat ≤ result.high_water.toNat ∧
      (∀ i, i < fillEnd d → bfn output i = bfn wa i) := by
  let n := rbLen z.avail_in (fillMore d)
  let copied := copyRange wa ia (fillEnd d) io n.toNat
  let read := resumeReadState d n copied
  let hr := resumeReadHeap h r ds w z d ref io ia wa
  have localR := local_resume_read_state (ref := ref) (io := io) (ia := ia) state get
  have counts := local_resume_read_counts state win get range
  change n.toNat = min z.avail_in.toNat (d.window_size.toNat-fillEnd d) ∧
    (d.lookahead+n).toNat = d.lookahead.toNat+n.toNat ∧
    d.strstart.toNat+(d.lookahead+n).toNat ≤ d.window_size.toNat at counts
  obtain ⟨key,fields⟩ := resume_read_record d n copied
  change read = _ at fields
  have rangeR : fillEnd read ≤ read.window_size.toNat := by rw [fields];exact counts.2.2
  have winR : read.window = .ref (.blk w) 0 := by rw [fields];exact win
  have getR : hr.bytes w = some copied := by simp [hr,resumeReadHeap,n,copied]
  have localA := local_padded_state localR winR getR rangeR
  obtain ⟨shape,_,_,frame,_⟩ := local_refill_stores
    (nextZ := readStream z n ref io (adlerValue z.adler ((ia.toList.drop io).take n.toNat)))
    (nextD := resumedFillState d n copied) (output := fillRange copied (paddingStart read) (paddingCount read) 0) state.live get
  rw [←local_resumed_heap_exact] at shape frame
  have extent := local_window_extent state win get
  have pad := padding_bounds read rangeR localR.inv.hw
  have endpoint : fillEnd read = fillEnd d+n.toNat := by
    rw [fields]
    change d.strstart.toNat+(d.lookahead+n).toNat = d.strstart.toNat+d.lookahead.toNat+n.toNat
    rw [counts.2.1]
    omega
  have readSize : read.window_size = d.window_size := by rw [fields]
  have copyFit : fillEnd d+n.toNat ≤ wa.size := by rw [extent.1];dsimp only [fillEnd] at counts ⊢;omega
  have padFit : paddingStart read+paddingCount read ≤ copied.size := by
    rw [size_copyRange,extent.1]
    have target := pad.2.2.2.1
    rw [readSize] at target
    omega
  have highSmall := local_padding_target_small localR winR getR rangeR
  have padded : min (fillEnd (resumedFillState d n copied)+258) (resumedFillState d n copied).window_size.toNat ≤
      (resumedFillState d n copied).high_water.toNat := by
    change min (fillEnd read+258) read.window_size.toNat ≤ (UInt64.ofNat (paddingTarget read)).toNat
    rw [UInt64.toNat_ofNat',Nat.mod_eq_of_lt highSmall]
    exact pad.2.2.2.2.2
  refine ⟨local_fill_window_resume_run state win get range short noSlide insert wrap pointer input inputBound nonempty separate,
    localA,read_stream_accounting z n ref io _ pointer (by have count := rbLen_nat z.avail_in (fillMore d);omega),frame,shape,
    ?_,counts.1,?_,?_,?_,?_,?_,padded,?_⟩
  · rw [local_resumed_heap_exact]
    simp
  · change fillEnd (paddedState read) = _
    unfold fillEnd paddedState
    rw [fields]
    change d.strstart.toNat+(d.lookahead+n).toNat = d.strstart.toNat+d.lookahead.toNat+n.toNat
    rw [counts.2.1]
    omega
  · change (paddedState read).strstart = _
    rw [fields]
    rfl
  · change (paddedState read).status = _
    rw [fields]
    rfl
  · change (paddedState read).level = _
    rw [fields]
    rfl
  · change (paddedState read).strategy = _
    rw [fields]
    rfl
  · intro i before
    unfold bfn
    rw [Array.getD_eq_getD_getElem?,getElem?_fillRange _ _ _ _ _ padFit]
    have noPad : ¬paddingStart read ≤ i := by
      have start := pad.1
      rw [endpoint] at start
      omega
    simp only [noPad,false_and,ite_false]
    rw [getElem?_copyRange _ _ _ _ _ _ copyFit]
    simp only [show ¬fillEnd d ≤ i by omega,false_and,ite_false]
    simp only [Array.getD_eq_getD_getElem?]


/-- Every old caller slot is preserved pointwise by the actual normalized
resumed heap when the stream, private state and window have fresh keys. -/
theorem local_resumed_old_slots {h : Heap} {r : ZStreamRef} {cutoff ds w io : Nat}
    {z : ZStream} {d : DeflateState} {ref : BRef} {ia wa : Array UInt8}
    (live : DLive h r ds z d) (get : h.bytes w = some wa)
    (stateNew : cutoff ≤ ds) (windowNew : cutoff ≤ w)
    (streamNew : ∀ b, StreamRoot r b → cutoff ≤ b) :
    ∀ b, b < cutoff → SlotSame h (resumedFillHeap h r ds w z d ref io ia wa) b := by
  rw [local_resumed_heap_exact]
  obtain ⟨_,_,_,_,words,headers,istates,ro,bytes,states,streams⟩ := local_refill_stores live get
  intro b old
  have notState : b ≠ ds := by omega
  have notWindow : b ≠ w := by omega
  have notStream : ¬StreamRoot r b := fun root => by have bound := streamNew b root;omega
  obtain ⟨stream,gzstate⟩ := streams b notStream
  exact ⟨bytes b notWindow,(by rw [words]),stream,(by rw [headers]),states b notState,
    (by rw [istates]),gzstate,(by rw [ro])⟩

end ZlibF.Spec.Public.Proofs.CompressLocalRefill
