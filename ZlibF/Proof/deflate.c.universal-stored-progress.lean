import ZlibF.Proof.«deflate.c.universal-call-dispatch»

/-!
# deflate.c, universal engine: progress of `deflate_stored`

`deflate` needs to know that a strategy call with input and output room moves one of the two
cursors (M7 of the `deflate_call` interface), and that a `Z_FINISH` call with output room either
finishes (`finish_done`) or moves a cursor (M8). For the other strategies this is
`StratMeaning.progress`. For `deflate_stored` it is `stored_progress` below.

The argument follows the C. If the copy loop moved a cursor, the rest of the call only moves
cursors further. Otherwise the loop wrote nothing and read nothing, so the keep step is skipped.
A last block of the loop returns `finish_done`. Otherwise the refill reads input, unless the input
is empty or the window is full with `block_start < w_size` (no slide). In those two cases the final
block test passes: with a full window `left > w_size ≥ min_block`; with `Z_FINISH` and no input,
`left < min_block` gives `left ≤ have`. The block's header is at least five pending bytes, so
`flush_pending` writes at least one byte into the free output.

The refill, the final block and its flush are restated from `deflate.c.universal-stored-tail` with
the counts these steps need; the run equalities tie them to the lemmas there.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Universal
set_option autoImplicit false

set_option maxHeartbeats 4000000 in
/-- **The refill of `deflate_stored` reads, unless there is no input or the window is full.**
`stored_refill` with the count of the bytes read: it is not zero, or the input is empty, or the
window holds more than `w_size` bytes after `block_start`. -/
theorem stored_refill_progress {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (level0 : d.level = 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ g zF eF used, storedRefill (some (.tab ds)) (some r) d h = .ok ((), g) ∧ DInv g r ds zF eF ∧
      StreamBuffers g r ∧ StreamAccounting z zF used 0 ∧
      (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧
      (used ≠ 0 ∨ z.avail_in = 0 ∨ (eF.w_size.toNat : Int) ≤ eF.strstart.toNat - eF.block_start.toInt) := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  obtain ⟨w, wa, win, getW, sizeW⟩ := window_block good
  have wsz := good.inv.wsz
  have wsize := good.inv.wsize
  have wbits := good.inv.wbits_hi
  have wbitsLo := good.inv.wbits_lo
  have wpow : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) wbits
  have wpowLo : 2 ^ 9 ≤ 2 ^ d.w_bits.toNat := Nat.pow_le_pow_right (by omega) wbitsLo
  have room := shape.room
  have la : d.lookahead.toNat = 0 := by rw [zero.2.1]; rfl
  have insLe := shape.insert
  have bsHi := shape.blockStart
  have hwLe := shape.highWater
  have hz := good.live.hz
  have state0 := good.live.hs
  have getWv : Space.get h (BRef.blk w) = some wa := getW
  have ro : Space.ro h (BRef.blk w) = false := by
    obtain ⟨w0, p0, q0, b0, blocks⟩ := good.inv.blocks
    have : w0 = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using blocks.win.symm
    subst this; exact blocks.wro
  have hash0 : LevelHash h d := ⟨inv.hashing.chains, inv.hashing.slid⟩
  have readAvail : ∀ H : Heap, r.get H = some z → zrd (some r) (·.avail_in) H = .ok (z.avail_in, H) := by
    intro H hzH; simp [zrd_eq, hzH]
  have have0N : ((d.window_size - d.strstart.toUInt64).toUInt32).toNat = d.window_size.toNat - d.strstart.toNat := by
    rw [UInt64.toNat_toUInt32, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
    simp; omega
  have ssLt := d.strstart.toNat_lt
  have aLt := z.avail_in.toNat_lt
  have hSelf : setD { h with bytes := upd h.bytes w (some wa) } ds d = h := by
    rw [upd_self _ _ _ getW]; exact setD_self state0
  have wsN0 : d.w_size.toUInt64.toInt64.toInt = d.w_size.toNat := u32_toInt64_toInt _
  unfold storedRefill
  simp only [bind_app, readAvail h hz]
  by_cases cond : (decide (z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32) &&
      decide (d.block_start ≥ d.w_size.toUInt64.toInt64)) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at cond
    obtain ⟨more, far⟩ := cond
    have moreN := UInt32.lt_iff_toNat_lt.mp more
    rw [have0N] at moreN
    have wsN : d.w_size.toUInt64.toInt64.toInt = d.w_size.toNat := u32_toInt64_toInt _
    have farN : (d.w_size.toNat : Int) ≤ d.block_start.toInt := by
      have := Int64.le_iff_toInt_le.mp far; rw [wsN] at this; exact this
    have wide : d.w_size.toNat ≤ d.strstart.toNat := by omega
    have slide := stored_slide_run state0 win getWv ro (by omega) wide (by omega) zero.1 bsHi
    obtain ⟨wa1, hwa1⟩ : ∃ x, x = copyRange wa wa 0 d.w_size.toNat (d.strstart - d.w_size).toNat := ⟨_, rfl⟩
    rw [← hwa1] at slide
    have size1 : wa1.size = wa.size := by rw [hwa1, size_copyRange]
    have ssN : (d.strstart - d.w_size).toNat = d.strstart.toNat - d.w_size.toNat :=
      UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr wide)
    have hz1 : r.get (setD (Space.put h (BRef.blk w) wa1) ds (refillSlide d)) = some z := by
      show r.get (Space.put h (BRef.blk w) wa1) = some z
      rw [view_put_stream]; exact hz
    have i1 : (refillSlide d).insert.toNat ≤ d.insert.toNat ∧
        (refillSlide d).insert.toNat ≤ (d.strstart - d.w_size).toNat := by
      show (if d.insert > d.strstart - d.w_size then d.strstart - d.w_size else d.insert).toNat ≤ _ ∧
        (if d.insert > d.strstart - d.w_size then d.strstart - d.w_size else d.insert).toNat ≤ _
      split
      · rename_i gt; have := UInt32.lt_iff_toNat_lt.mp gt; omega
      · rename_i ngt
        have : ¬ (d.strstart - d.w_size).toNat < d.insert.toNat := fun c => ngt (UInt32.lt_iff_toNat_lt.mpr c)
        omega
    have m1 : (refillSlide d).«matches».toNat ≤ 2 := by
      have := shape.slides.1
      show (if d.«matches» < 2 then d.«matches» + 1 else d.«matches»).toNat ≤ 2
      split
      · rename_i lt; have := UInt32.lt_iff_toNat_lt.mp lt; rw [UInt32.toNat_add]; simp at this ⊢; omega
      · omega
    have bs1 : (Int64.ofInt (d.block_start.toInt - d.w_size.toNat)).toInt = d.block_start.toInt - d.w_size.toNat :=
      int64_ofInt_toInt _ (by omega) (by omega)
    have hashE : LevelHash (setD { h with bytes := upd h.bytes w (some wa1) } ds (refillSlide d)) (refillSlide d) :=
      level_hash_slide hash0 zero.2.1 zero.2.1 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
        ⟨d.w_bits.toNat, wsize⟩ (by omega) wide ssN i1.1 (fun _ _ => rfl)
        (fun w' wa' e g' => by
          have : w' = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using e.symm
          subst this
          have : wa' = wa := Option.some.inj (g'.symm.trans getW)
          subst this
          refine ⟨wa1, upd_same _ _ _, fun i lt => ?_⟩
          rw [hwa1, bfn_copyRange _ _ _ _ _ _ (by omega), if_pos (by omega)]
          congr 1; omega)
    have have1N : ((d.window_size - d.strstart.toUInt64).toUInt32 + d.w_size).toNat =
        d.window_size.toNat - d.strstart.toNat + d.w_size.toNat := by
      rw [UInt32.toNat_add, have0N]; omega
    have finishA : ∀ n : UInt32, n.toNat ≤ z.avail_in.toNat →
        n.toNat ≤ d.window_size.toNat - d.strstart.toNat + d.w_size.toNat → 1 ≤ n.toNat →
        ∃ g zF eF used, storedRead (some (.tab ds)) (some r) n (setD (Space.put h (BRef.blk w) wa1) ds (refillSlide d)) =
            .ok ((), g) ∧ DInv g r ds zF eF ∧ StreamBuffers g r ∧ StreamAccounting z zF used 0 ∧
          (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧
          (used ≠ 0 ∨ z.avail_in = 0 ∨ (eF.w_size.toNat : Int) ≤ eF.strstart.toNat - eF.block_start.toInt) := by
      intro n avail fitN one
      have shapeF : Shape (refillRead (refillSlide d) n) := shape_refill shape level0 (d.strstart - d.w_size) (refillSlide d).insert
        (refillSlide d).«matches» (Int64.ofInt (d.block_start.toInt - d.w_size.toNat)) d.high_water n
        (by omega) i1.2 (by rw [bs1]; omega) (by rw [bs1]; omega) hwLe m1 (fun _ => by omega) (by omega)
      obtain ⟨g, zF, run, invG, buffersG, _, acc, _, _, _, _⟩ := refill_finish inv buffers level0 win getW
        (refillSlide d) wa1 size1 ⟨_, _, _, _, _, rfl⟩ hashE n avail
        (by show (d.strstart - d.w_size).toNat + n.toNat ≤ wa.size; omega) (by omega) i1.2 input shapeF
      exact ⟨g, zF, _, n.toNat, run, invG, buffersG, acc, ⟨_, _, _, _, _, rfl⟩, Or.inl (by omega)⟩
    have condT : (decide (z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32) &&
        decide (d.block_start ≥ d.w_size.toUInt64.toInt64)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨more, far⟩
    simp only [condT, ite_true, bind_app, slide, readAvail _ hz1]
    by_cases c2 : (d.window_size - d.strstart.toUInt64).toUInt32 + d.w_size > z.avail_in
    · have c2N := UInt32.lt_iff_toNat_lt.mp c2
      rw [have1N] at c2N
      simp only [c2, decide_true, ite_true]
      exact finishA _ (Nat.le_refl _) (by omega) (by omega)
    · have c2N : ¬ z.avail_in.toNat < ((d.window_size - d.strstart.toUInt64).toUInt32 + d.w_size).toNat :=
        fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
      rw [have1N] at c2N
      simp only [c2, decide_false, Bool.false_eq_true, ite_false]
      exact finishA _ (by rw [have1N]; omega) (by rw [have1N]; exact Nat.le_refl _) (by rw [have1N]; omega)
  · simp only [Bool.not_eq_true] at cond
    have farN : z.avail_in.toNat ≠ 0 → d.window_size.toNat - d.strstart.toNat = 0 →
        d.block_start.toInt < d.w_size.toNat := by
      intro a0 full
      rw [← wsN0]
      refine Int.not_le.mp (fun c => ?_)
      have far : d.block_start ≥ d.w_size.toUInt64.toInt64 := Int64.le_iff_toInt_le.mpr c
      have more : z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32 :=
        UInt32.lt_iff_toNat_lt.mpr (by rw [have0N]; omega)
      have t : (decide (z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32) &&
          decide (d.block_start ≥ d.w_size.toUInt64.toInt64)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨more, far⟩
      rw [t] at cond
      exact absurd cond (by decide)
    simp only [cond, Bool.false_eq_true, ite_false, bind_app, readAvail h hz]
    have finishB : ∀ n : UInt32, n.toNat ≤ z.avail_in.toNat → n.toNat ≤ d.window_size.toNat - d.strstart.toNat →
        (n.toNat ≠ 0 ∨ z.avail_in = 0 ∨
          (n.toNat = 0 ∧ (d.w_size.toNat : Int) ≤ d.strstart.toNat - d.block_start.toInt)) →
        ∃ g zF eF used, storedRead (some (.tab ds)) (some r) n h = .ok ((), g) ∧ DInv g r ds zF eF ∧
          StreamBuffers g r ∧ StreamAccounting z zF used 0 ∧
          (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧
          (used ≠ 0 ∨ z.avail_in = 0 ∨ (eF.w_size.toNat : Int) ≤ eF.strstart.toNat - eF.block_start.toInt) := by
      intro n avail fitN prog
      have same : keepState d d.strstart d.insert d.«matches» d.block_start d.high_water = d := rfl
      have shapeF := shape_refill shape level0 d.strstart d.insert d.«matches» d.block_start d.high_water n
        (by omega) insLe zero.1 bsHi hwLe shape.slides.1 (fun av => by have := shape.available av; omega) (by omega)
      have hashE : LevelHash (setD { h with bytes := upd h.bytes w (some wa) } ds
          (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water))
          (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water) := by
        rw [same, hSelf]; exact hash0
      obtain ⟨g, zF, run, invG, buffersG, _, acc, _, _, _, _⟩ := refill_finish inv buffers level0 win getW
        (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water) wa rfl ⟨_, _, _, _, _, rfl⟩
        hashE n avail (by show d.strstart.toNat + n.toNat ≤ wa.size; omega) (by omega) insLe input shapeF
      rw [same, hSelf] at run
      refine ⟨g, zF, _, n.toNat, run, invG, buffersG, acc, ⟨_, _, _, _, _, rfl⟩, ?_⟩
      rcases prog with p | p | ⟨n0, p⟩
      · exact Or.inl p
      · exact Or.inr (Or.inl p)
      · refine Or.inr (Or.inr ?_)
        have nz : n = 0 := UInt32.toNat_inj.mp (by rw [n0]; rfl)
        subst nz
        show (d.w_size.toNat : Int) ≤ (d.strstart + 0).toNat - d.block_start.toInt
        simpa using p
    by_cases c2 : (d.window_size - d.strstart.toUInt64).toUInt32 > z.avail_in
    · have c2N := UInt32.lt_iff_toNat_lt.mp c2
      rw [have0N] at c2N
      simp only [c2, decide_true, ite_true]
      refine finishB _ (Nat.le_refl _) (by omega) ?_
      by_cases a0 : z.avail_in = 0
      · exact Or.inr (Or.inl a0)
      · exact Or.inl (fun c => a0 (UInt32.toNat_inj.mp (by rw [c]; rfl)))
    · have c2N : ¬ z.avail_in.toNat < ((d.window_size - d.strstart.toUInt64).toUInt32).toNat :=
        fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
      rw [have0N] at c2N
      simp only [c2, decide_false, Bool.false_eq_true, ite_false]
      refine finishB _ (by rw [have0N]; omega) (by rw [have0N]; exact Nat.le_refl _) ?_
      rw [have0N]
      by_cases full : d.window_size.toNat - d.strstart.toNat = 0
      · by_cases a0 : z.avail_in = 0
        · exact Or.inr (Or.inl a0)
        · have aN : z.avail_in.toNat ≠ 0 := fun c => a0 (UInt32.toNat_inj.mp (by rw [c]; rfl))
          have lt := farN aN full
          exact Or.inr (Or.inr ⟨full, by omega⟩)
      · exact Or.inl full


open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff) in
set_option maxHeartbeats 4000000 in
/-- **The final stored block writes output.** `stored_block_flush` with the count of its flush:
the stored header is at least five pending bytes, so with free output `flush_pending` writes. -/
theorem stored_block_progress {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt ≤ 7)
    (low : 0 ≤ d.block_start.toInt) (len : UInt32)
    (span : d.block_start.toInt + len.toNat ≤ d.strstart.toNat) (range : d.strstart.toNat ≤ d.window_size.toNat)
    (room : (d.bi_valid.toInt.toNat + 42) / 8 + len.toNat ≤ d.pending_buf_size.toNat) (lastv : Bool)
    (avail : z.avail_out ≠ 0) :
    ∃ (p : BPtr) (H1 : Heap) (bs : Int64) (H2 after : Heap) (z' : ZStream) (e : DeflateState),
      Ptr.add d.window d.block_start.toInt h = .ok (p, h) ∧
      Zlib.Trees._tr_stored_block (some (.tab ds)) p len.toUInt64 (if lastv then 1 else 0) h = .ok ((), H1) ∧
      ladd d.block_start len.toUInt64.toInt64 H1 = .ok (bs, H1) ∧
      wr (some (.tab ds)) (fun d => { d with block_start := bs }) H1 = .ok ((), H2) ∧
      flush_pending (some r) H2 = .ok ((), after) ∧
      r.get after = some z' ∧ after.dstates ds = some e ∧ z'.avail_out ≠ z.avail_out := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, getB, sizeB⟩ := blocks.ba
  obtain ⟨wa, getW, sizeW⟩ := blocks.wa
  have trees : TreesInvAt h ds d pb buf := Zlib.Deflate.Universal.trees_at_of_good good blocks.pbuf getB
  have bufSize : buf.size = d.pending_buf_size.toNat := trees.base.psize.symm
  have wsz := good.inv.wsz
  have lenLt := len.toNat_lt
  have bsN : (d.block_start.toInt.toNat : Int) = d.block_start.toInt := Int.toNat_of_nonneg low
  have add : Ptr.add d.window d.block_start.toInt h = .ok (.ref (.blk w) d.block_start.toInt.toNat, h) := by
    rw [blocks.win]
    have := Ptr.add_ok (off := 0) (k := d.block_start.toInt) (show Space.get h (BRef.blk w) = some wa from getW)
      (by omega) (by omega)
    have e0 : ((0 : Nat) : Int) + d.block_start.toInt = d.block_start.toInt := by omega
    rw [e0] at this
    exact this
  have lenN : len.toUInt64.toNat = len.toNat := by simp
  obtain ⟨next, r1, run1, trees1, size1, aligned1, pend1, diff1⟩ :=
    Zlib.Trees.Proofs.Out.stored_block_exact (off := d.block_start.toInt.toNat) trees getW (Ne.symm blocks.wb)
      bits len.toUInt64
      (by rw [lenN]; omega) (by rw [pending, UInt64.toNat_zero]; have := trees.base.lit_lo; omega)
      (by rw [pending, lenN, UInt64.toNat_zero]; omega) lastv
  replace run1 : Zlib.Trees._tr_stored_block (some (.tab ds)) (.ref (.blk w) d.block_start.toInt.toNat) len.toUInt64
      (if lastv then 1 else 0) h = .ok ((), setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) := run1
  replace trees1 : TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) ds r1 pb next := trees1
  have good1 := output_bits_good good cursor getB size1 diff1 trees1
  have buffers1 := output_bits_buffers good buffers cursor getB size1 diff1 trees1
  obtain ⟨pp, aa, vv, uu, hr1⟩ := diff1
  have lenI : len.toUInt64.toInt64.toInt = (len.toNat : Int) := Zlib.Deflate.Universal.u32_toInt64_toInt len
  have ssLt := d.strstart.toNat_lt
  have lad := ladd_value d.block_start len.toUInt64.toInt64 (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1)
    (by rw [lenI]; omega) (by rw [lenI]; omega)
  rw [lenI] at lad
  let r2 := { r1 with block_start := Int64.ofInt (d.block_start.toInt + len.toNat) }
  have state1 : (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1).dstates ds = some r1 := setD_dstates_same _ _ _
  have wrt : wr (some (.tab ds)) (fun x => { x with block_start := Int64.ofInt (d.block_start.toInt + len.toNat) })
      (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) = .ok ((), setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r2) := by
    rw [wrD_eq, state1]; dsimp only; rw [setD_setD]
  let H2 := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r2
  have inv2 : DStInv (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds r1) ds r2 :=
    { good1.inv with blocks := good1.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have good2 : DGood H2 r ds z r2 := by
    have g := good1.setD' (d' := r2) rfl good1.live.status inv2 (by trkeep)
    rw [setD_setD] at g; exact g
  have buffers2 : StreamBuffers H2 r := by
    have b := Zlib.Deflate.Universal.state_write_buffers good1 buffers1 (d' := r2) ⟨rfl, rfl, rfl, rfl⟩
      (by have g := good1.setD' (d' := r2) rfl good1.live.status inv2 (by trkeep); exact g)
    rw [setD_setD] at b; exact b
  have trees2 : TreesInvAt H2 ds r2 pb next :=
    ⟨⟨setD_dstates_same _ _ _, trees1.base.wf, trees1.base.static, trees1.base.pbuf, trees1.base.bytes,
      trees1.base.rw, trees1.base.size, trees1.base.psize, trees1.base.sym, trees1.base.lit_lo, trees1.base.lit_hi,
      trees1.base.sym_end, trees1.base.pending_le⟩,
      ⟨trees1.run.ldyn, trees1.run.lstat, trees1.run.ddyn, trees1.run.dstat, trees1.run.bldyn, trees1.run.blstat,
        trees1.run.bi_lo, trees1.run.bi_hi, trees1.run.bi_buf, trees1.run.sym_next_le, trees1.run.sym_next_mod⟩⟩
  have cursor2 : r2.pending_out = r2.pending_buf := by
    show r1.pending_out = r1.pending_buf; rw [hr1]; exact cursor
  have room2 : 8 * r2.pending.toNat + r2.bi_valid.toInt.toNat ≤ 8 * next.size := by
    show 8 * r1.pending.toNat + r1.bi_valid.toInt.toNat ≤ 8 * next.size
    rw [pend1, aligned1, size1, pending, lenN, UInt64.toNat_zero]; simp only [Int.toNat_zero]; omega
  have five : 5 ≤ r2.pending.toNat := by
    show 5 ≤ r1.pending.toNat
    rw [pend1]; omega
  have availN : z.avail_out.toNat ≠ 0 := fun c => avail (UInt32.toNat_inj.mp (by rw [c]; rfl))
  obtain ⟨ob, pointer⟩ := Zlib.Deflate.Universal.output_reference good.live.hz buffers out
  rcases pointer with ⟨oo, pointer⟩ | ⟨oo, pointer⟩
  · obtain ⟨produced, after, z', result, _, _, run, goodA, _, accountA, _, _, count, _⟩ :=
      flush_pending_raw_bits good2 trees2 buffers2 pointer cursor2 room2
    refine ⟨_, _, _, _, after, z', result, add, run1, lad, wrt, run, goodA.live.hz, goodA.live.hs, fun e => ?_⟩
    have a := accountA.2.2.2.1
    rw [e] at a
    have : 1 ≤ produced := by rw [count]; omega
    omega
  · obtain ⟨produced, after, z', result, _, _, run, goodA, _, accountA, _, _, count, _⟩ :=
      flush_pending_foreign_bits_frame good2 trees2 buffers2 pointer cursor2 room2
    refine ⟨_, _, _, _, after, z', result, add, run1, lad, wrt, run, goodA.live.hz, goodA.live.hs, fun e => ?_⟩
    have a := accountA.2.2.2.1
    rw [e] at a
    have : 1 ≤ produced := by rw [count]; omega
    omega


set_option maxHeartbeats 8000000 in
/-- **The final block of `deflate_stored` writes output** when the window holds at least `w_size`
bytes after `block_start`, or for `Z_FINISH` with no input left, given free output. -/
theorem stored_final_progress {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0) (out : z.next_out ≠ .null)
    (level0 : d.level = 0) (flush last0 : Int32) (avail : z.avail_out ≠ 0)
    (enough : (d.w_size.toNat : Int) ≤ d.strstart.toNat - d.block_start.toInt ∨ (flush = Z_FINISH ∧ z.avail_in = 0)) :
    ∃ ret g z', storedFinal (some (.tab ds)) flush (some r) last0 h = .ok (ret, g) ∧ r.get g = some z' ∧
      z'.avail_out ≠ z.avail_out := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  have bits := inv.bi_valid_le
  have hvN := header_bytes_value d.bi_valid bits.1 bits.2
  have room := shape.room
  have wsz := good.inv.wsz
  have wsize := good.inv.wsize
  have wbits := good.inv.wbits_hi
  have wpow : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) wbits
  have la : d.lookahead.toNat = 0 := by rw [zero.2.1]; rfl
  obtain ⟨lsubEq, word, _⟩ := Zlib.Deflate.Universal.Block.flush_length_general (d := d) (by omega)
    shape.blockStart (by omega)
  have lsubRun := congrFun lsubEq h
  have pbs := good.inv.blocks
  obtain ⟨w0, p0, q0, b0, blocks⟩ := pbs
  have psize := blocks.psize
  have lit := good.inv.lit
  have hsize := good.inv.hsize
  have hbits := good.inv.hbits_lo
  have hpow : 2 ^ 8 ≤ 2 ^ d.hash_bits.toNat := Nat.pow_le_pow_right (by omega) hbits
  have PLe : (d.bi_valid.toInt.toNat + 42) / 8 ≤ 6 := by omega
  have hvU : (((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64).toNat = (d.bi_valid.toInt.toNat + 42) / 8 := by
    rw [UInt32.toNat_toUInt64, hvN]
  have pbsLe : (((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64) ≤ d.pending_buf_size := by
    rw [UInt64.le_iff_toNat_le, hvU]; omega
  have HvN : ((MIN (d.pending_buf_size - ((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64) MAX_STORED.toUInt64).toUInt32).toNat ≤
      d.pending_buf_size.toNat - (d.bi_valid.toInt.toNat + 42) / 8 := by
    have sub : (d.pending_buf_size - ((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64).toNat =
        d.pending_buf_size.toNat - (d.bi_valid.toInt.toNat + 42) / 8 := by
      rw [UInt64.toNat_sub_of_le _ _ pbsLe, hvU]
    have m : MAX_STORED.toUInt64.toNat = 65535 := rfl
    unfold MIN
    split
    · rename_i lt
      have lt' := UInt64.lt_iff_toNat_lt.mp lt
      rw [sub, m] at lt'
      rw [UInt64.toNat_toUInt32, m]
      omega
    · rw [UInt64.toNat_toUInt32, sub]
      exact Nat.mod_le _ _
  have hz := good.live.hz
  have readAvail : zrd (some r) (·.avail_in) h = .ok (z.avail_in, h) := by simp [zrd_eq, hz]
  unfold storedFinal
  simp only [bind_app, ldDeflateState_tab good.live.hs, lsubRun, pure_app, readAvail]
  obtain ⟨left, hleft⟩ : ∃ l, l = (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64.toUInt32 :=
    ⟨_, rfl⟩
  rw [← hleft]
  have leftN : left.toNat = ((d.strstart.toNat : Int) - d.block_start.toInt).toNat := by
    rw [hleft, UInt64.toNat_toUInt32, word]
    apply Nat.mod_eq_of_lt
    have := shape.blockStart; have := zero.1; omega
  obtain ⟨Hv, hHv⟩ : ∃ x, x = (MIN (d.pending_buf_size - ((d.bi_valid.toUInt32 + 42) >>> 3).toUInt64)
      MAX_STORED.toUInt64).toUInt32 := ⟨_, rfl⟩
  rw [← hHv]
  rw [← hHv] at HvN
  have lenLe := min_toNat_le left Hv
  have lenLe2 : (MIN left Hv).toNat ≤ Hv.toNat := by
    unfold MIN; split
    · exact Nat.le_refl _
    · rename_i nlt
      have : ¬ Hv.toNat < left.toNat := fun c => nlt (UInt32.lt_iff_toNat_lt.mpr c)
      omega
  have minW : (MIN Hv d.w_size).toNat ≤ d.w_size.toNat := by
    unfold MIN; split
    · exact Nat.le_refl _
    · rename_i nlt
      have : ¬ d.w_size.toNat < Hv.toNat := fun c => nlt (UInt32.lt_iff_toNat_lt.mpr c)
      omega
  have minH : (MIN Hv d.w_size).toNat ≤ Hv.toNat := min_toNat_le Hv d.w_size
  have fn : (Z_FINISH != Z_NO_FLUSH) = true := by decide
  have c : (decide (left ≥ MIN Hv d.w_size) || ((left != 0 || flush == Z_FINISH) && flush != Z_NO_FLUSH &&
      z.avail_in == 0 && decide (left ≤ Hv))) = true := by
    by_cases ge : left ≥ MIN Hv d.w_size
    · simp [ge]
    · have lt : left.toNat < (MIN Hv d.w_size).toNat := by
        have : ¬ (MIN Hv d.w_size).toNat ≤ left.toNat := fun c => ge (UInt32.le_iff_toNat_le.mpr c)
        omega
      rcases enough with wide | ⟨f, a⟩
      · exfalso; rw [leftN] at lt; omega
      · have le : left ≤ Hv := UInt32.le_iff_toNat_le.mpr (by omega)
        subst f
        simp [a, le, fn]
  obtain ⟨p, H1, bs, H2, after, z', e, add, blk, lad, wrt, fl, hzA, hsA, moved⟩ :=
    stored_block_progress good buffers out pend0 (shape.cursor pend0) bits.2 zero.1 (MIN left Hv)
      (by have := shape.blockStart; omega) (by omega) (by omega)
      (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) avail
  by_cases l0 : ((if (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) = true then (1 : Int32) else 0) != 0) = true
  · refine ⟨finish_started, setD after ds { e with bi_used := 8 }, z', ?_, by rw [ZStreamRef.get_setD]; exact hzA, moved⟩
    have wrRun : wr (some (.tab ds)) (fun d => { d with bi_used := 8 }) after =
        .ok ((), setD after ds { e with bi_used := 8 }) := by rw [wrD_eq, hsA]
    simp only [c, ite_true, bind_app, add, blk, lad, wrt, fl]
    simp only [l0, ite_true, bind_app, wrRun]
    rfl
  · simp only [Bool.not_eq_true] at l0
    refine ⟨need_more, after, z', ?_, hzA, moved⟩
    simp only [c, ite_true, bind_app, add, blk, lad, wrt, fl]
    simp only [l0, Bool.false_eq_true, ite_false, bind_app, pure_app]


set_option maxHeartbeats 8000000 in
/-- **Progress of `deflate_stored`** (M7 and M8 of the `deflate_call` interface). With input and
output room, a call moves a cursor. A `Z_FINISH` call with output room returns `finish_done` or
moves a cursor. No premise beyond `DInv` and the checks of `deflate`. -/
theorem stored_progress {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StratIn h r z d) (flush : Int32) (level : d.level = 0)
    {bstate : block_state} {after : Heap} {z' : ZStream}
    (run : C.run (Zlib.Deflate.deflate_stored (some (.tab ds)) flush) h = .ok (bstate, after))
    (hz' : r.get after = some z') :
    (z.avail_in ≠ 0 → z.avail_out ≠ 0 → z'.avail_in ≠ z.avail_in ∨ z'.avail_out ≠ z.avail_out) ∧
    (flush = Z_FINISH → z.avail_out ≠ 0 →
      bstate = finish_done ∨ z'.avail_in ≠ z.avail_in ∨ z'.avail_out ≠ z.avail_out) := by
  have good := inv.good
  have hz := good.live.hz
  have strm := good.live.back
  obtain ⟨st, g, z1, d1, loopRun, step, lastF⟩ := stored_loop inv entry.buffers entry.pending entry.out entry.input
    level flush (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32
    { last := 0, len := 0, left := 0, have_ := 0, all := false, brk := false } rfl
  have readAvail : zrd (some r) (·.avail_in) h = .ok (z.avail_in, h) := by simp [zrd_eq, hz]
  have endRun : storedEnd (some (.tab ds)) flush (some r) (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32
      z.avail_in st g = .ok (bstate, after) := by
    have run' := run
    simp only [C.run, deflate_stored_source, bind_app, ldDeflateState_tab good.live.hs, strm, readAvail,
      loopRun] at run'
    exact run'
  obtain ⟨u1, p1, acc1, _⟩ := step.account
  have level1 : d1.level = 0 := by rw [step.fields]; exact level
  have count : z.avail_in.toNat = z1.avail_in.toNat + u1 := by have := acc1.2.2.1; omega
  have cursor : u1 ≠ 0 → ∃ ref io, z1.next_in = .ref ref io ∧ u1 ≤ io := by
    intro nz
    have nzIn : z.avail_in ≠ 0 := by
      intro e; have := acc1.1; rw [e] at this; simp at this; omega
    obtain ⟨ref, io0, src0⟩ : ∃ ref io, z.next_in = .ref ref io := by
      cases p : z.next_in with
      | null => exact absurd p (entry.input nzIn)
      | ref ref io => exact ⟨ref, io, rfl⟩
    refine ⟨ref, io0 + u1, ?_, by omega⟩
    rw [acc1.2.2.2.2.1, src0]; rfl
  -- the end of the call only moves the cursors further
  obtain ⟨ret, g', z2, d2, u2, p2, endRun2, inv2, _, acc2, meaning, _, _⟩ :=
    stored_end step.inv step.buffers step.pending step.out step.input level1 flush
      (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32 z.avail_in st u1 count cursor lastF
  have e2 := Prod.mk.inj (Except.ok.inj (endRun.symm.trans endRun2))
  have hz2 : r.get g' = some z' := by rw [← e2.2]; exact hz'
  have zEq : z2 = z' := Option.some.inj (inv2.good.live.hz.symm.trans hz2)
  subst zEq
  have doneIn : bstate = finish_done → z2.avail_in = 0 := fun dn => (meaning.done (e2.1.symm.trans dn)).1
  have core : (z.avail_in ≠ 0 ∨ flush = Z_FINISH) → z.avail_out ≠ 0 →
      bstate = finish_done ∨ z2.avail_in ≠ z.avail_in ∨ z2.avail_out ≠ z.avail_out := by
    intro want avail
    have i1 := acc1.2.2.1
    have o1 := acc1.2.2.2.1
    by_cases mv : u1 = 0 ∧ p1 = 0
    · obtain ⟨u0, p0⟩ := mv
      have inEq : z1.avail_in = z.avail_in := UInt32.toNat_inj.mp (by omega)
      have outEq : z1.avail_out = z.avail_out := UInt32.toNat_inj.mp (by omega)
      have inv1 := step.inv
      have hz1 := inv1.good.live.hz
      have readAvail1 : zrd (some r) (·.avail_in) g = .ok (z1.avail_in, g) := by simp [zrd_eq, hz1]
      have u0' : (z.avail_in - z1.avail_in != 0) = false := by rw [inEq]; simp
      have keepRun : (if (z.avail_in - z1.avail_in != 0) = true then
          storedKeep (some (.tab ds)) (some r) (z.avail_in - z1.avail_in) else pure ()) g = .ok ((), g) := by
        simp only [u0', Bool.false_eq_true, ite_false]; rfl
      obtain ⟨hwRun, invH, buffersH, _, _⟩ := high_water_step inv1 step.buffers level1
      obtain ⟨eH, heH⟩ : ∃ x : DeflateState, x = { d1 with high_water :=
          if d1.high_water < d1.strstart.toUInt64 then d1.strstart.toUInt64 else d1.high_water } := ⟨_, rfl⟩
      rw [← heH] at hwRun invH buffersH
      have levelH : eH.level = 0 := by rw [heH]; exact level1
      have pendH : eH.pending = 0 := by rw [heH]; exact step.pending
      have hzH := invH.good.live.hz
      have readAvailH : zrd (some r) (·.avail_in) (setD g ds eH) = .ok (z1.avail_in, setD g ds eH) := by
        simp [zrd_eq, hzH]
      by_cases lastC : (st.last != 0) = true
      · left
        obtain ⟨wrRun, _, _⟩ := bi_used_step invH buffersH levelH
        obtain ⟨X, E⟩ : ∃ X, storedEnd (some (.tab ds)) flush (some r)
            (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32 z.avail_in st g = .ok (finish_done, X) :=
          ⟨_, by
            unfold storedEnd
            simp only [ite_seq]
            simp only [bind_app, readAvail1, keepRun, hwRun]
            simp only [lastC, ite_true, bind_app, wrRun]
            rfl⟩
        exact (Prod.mk.inj (Except.ok.inj (endRun.symm.trans E))).1
      · simp only [Bool.not_eq_true] at lastC
        have lastZ : st.last = 0 := by simpa using lastC
        have early : (flush != Z_NO_FLUSH && flush != Z_FINISH && z1.avail_in == 0 &&
            (eH.strstart.toUInt64.toInt64 == eH.block_start)) = false := by
          rcases want with i | f
          · rw [inEq]; simp [i]
          · subst f; simp
        obtain ⟨g3, zF, eF, used, refillRun, invF, buffersF, accF, ⟨_, _, _, _, _, keF⟩, prog⟩ :=
          stored_refill_progress invH buffersH levelH step.input
        have pendF : eF.pending = 0 := by rw [keF]; exact pendH
        have levelF : eF.level = 0 := by rw [keF]; exact levelH
        have outF := output_valid_after accF step.out
        have oF := accF.2.2.2.1
        have iF := accF.2.2.1
        have endE : ∀ ret4 g4, storedFinal (some (.tab ds)) flush (some r) st.last g3 = .ok (ret4, g4) →
            storedEnd (some (.tab ds)) flush (some r)
              (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32 z.avail_in st g = .ok (ret4, g4) := by
          intro ret4 g4 finalRun
          unfold storedEnd
          simp only [ite_seq]
          simp only [bind_app, readAvail1, keepRun, hwRun]
          simp only [lastC, Bool.false_eq_true, ite_false, bind_app, ldDeflateState_tab invH.good.live.hs, readAvailH]
          simp only [early, Bool.false_eq_true, ite_false]
          simp only [bind_app, refillRun, finalRun]
        by_cases u : used = 0
        · have inF : zF.avail_in = z1.avail_in := UInt32.toNat_inj.mp (by omega)
          have enough : (eF.w_size.toNat : Int) ≤ eF.strstart.toNat - eF.block_start.toInt ∨
              (flush = Z_FINISH ∧ zF.avail_in = 0) := by
            rcases prog with p | p | p
            · exact absurd u p
            · rcases want with i | f
              · exact absurd (inEq.symm.trans p) i
              · exact Or.inr ⟨f, inF.trans p⟩
            · exact Or.inl p
          have oF0 : zF.avail_out.toNat = z1.avail_out.toNat := by omega
          have availF : zF.avail_out ≠ 0 := by
            intro c; apply avail; rw [← outEq, ← UInt32.toNat_inj, ← oF0, c]
          obtain ⟨ret4, g4, z4, finalRun, hz4, moved⟩ :=
            stored_final_progress invF buffersF pendF outF levelF flush st.last availF enough
          have e4 := Prod.mk.inj (Except.ok.inj (endRun.symm.trans (endE ret4 g4 finalRun)))
          have z4Eq : z4 = z2 := Option.some.inj (hz4.symm.trans (by rw [← e4.2]; exact hz'))
          subst z4Eq
          right; right
          intro c
          apply moved
          rw [c, ← outEq]
          exact UInt32.toNat_inj.mp (by omega)
        · obtain ⟨ret4, g4, z4, e4', p4, finalRun, inv4, _, acc4, _⟩ :=
            stored_final invF buffersF pendF outF levelF flush st.last lastZ
          have e4 := Prod.mk.inj (Except.ok.inj (endRun.symm.trans (endE ret4 g4 finalRun)))
          have z4Eq : z4 = z2 := Option.some.inj (inv4.good.live.hz.symm.trans (by rw [← e4.2]; exact hz'))
          subst z4Eq
          right; left
          intro c
          have i4 := acc4.2.2.1
          rw [c] at i4
          omega
    · have i2 := acc2.2.2.1
      have o2 := acc2.2.2.2.1
      right
      by_cases u : u1 = 0
      · have p : p1 ≠ 0 := fun p => mv ⟨u, p⟩
        right; intro c; rw [c] at o2; omega
      · left; intro c; rw [c] at i2; omega
  refine ⟨fun i o => ?_, fun f o => core (Or.inr f) o⟩
  rcases core (Or.inl i) o with dn | p
  · left; rw [doneIn dn]; exact Ne.symm i
  · exact p

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- **M7 and M8 for the dispatch at level 0** (`deflate_stored`), in the form of the progress
clauses of `deflate_call`: with input and output room the call moves a cursor; with `Z_FINISH`
and output room it returns `finish_done` or moves a cursor. -/
theorem dispatch_stored_progress {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    {flush : Int32} {bstate : block_state} {after : Heap} {z' : ZStream}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (out : z.next_out ≠ .null)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (pend : d.pending = 0) (level : d.level = 0)
    (run : dispatch (some (.tab ds)) flush d h = .ok (bstate, after)) (hz : r.get after = some z') :
    (z.avail_in ≠ 0 → z.avail_out ≠ 0 → z'.avail_in ≠ z.avail_in ∨ z'.avail_out ≠ z.avail_out) ∧
    (flush = Z_FINISH → z.avail_out ≠ 0 →
      bstate = finish_done ∨ z'.avail_in ≠ z.avail_in ∨ z'.avail_out ≠ z.avail_out) := by
  have l0 : (d.level == 0) = true := by simp [level]
  have run' : C.run (Zlib.Deflate.deflate_stored (some (.tab ds)) flush) h = .ok (bstate, after) := by
    simp only [dispatch, l0, ite_true] at run; exact run
  exact stored_progress inv ⟨buffers, out, input, pend⟩ flush level run' hz

end Zlib.Deflate.Universal.Call
