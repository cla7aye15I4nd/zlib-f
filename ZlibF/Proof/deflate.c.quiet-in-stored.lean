import ZlibF.Proof.«deflate.c.quiet-strat-in»
import ZlibF.Proof.«deflate.c.quiet-in»

/-!
# deflate.c: `deflate_stored` stops on a full output or an empty input (`StoredStop`)

`stored_stop` proves `StoredStop`, the last open fact of `DeflateQuietIn`, and
`deflate_quiet_in_holds` is `DeflateQuietIn` itself.

The copy loop of `deflate_stored` stops without a last block only with `len < min_block`
(`LoopExit`): either the output room is below a header and `min_block`, or the window data and the
input together are below `min_block`. A loop that read input emptied the window part of the block, so
after the keep step the block is empty. If input is left after the refill, the window is full and
holds at least `w_size` bytes after `block_start`, so the final block of at least `min_block` bytes
fills the output; in the second case the refill reads all the input. A `finish_started` return needs
no input left, and its block covers the room left at the stop; with `Z_FINISH` a final block is
always written, and when it is not the last one it fills the output.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Universal
set_option autoImplicit false

set_option maxHeartbeats 4000000 in
open Zlib.Deflate.Universal in
/-- **The rest of an iteration.** With the header room (`have = avail_out - hv`), a length within
it whose input part is available, and `left = strstart - block_start`, the break test, the
emission and the direct copies keep the loop invariant; a completed iteration consumes output. -/
theorem stored_restS {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st : StoredS) (have_ left len : UInt32)
    (haveEq : have_.toNat + (d.bi_valid.toInt.toNat + 42) / 8 = z.avail_out.toNat)
    (leftEq : (left.toNat : Int) = d.strstart.toNat - d.block_start.toInt)
    (lenHave : len.toNat ≤ have_.toNat)
    (lenIn : (len - directLeft left len).toNat ≤ z.avail_in.toNat)
    (mbPos : 0 < min_block.toNat)
    (lenCase : len.toNat = left.toNat + z.avail_in.toNat ∨ len.toNat = have_.toNat ∨ len.toNat = 65535)
    (mbW : min_block.toNat ≤ d.w_size.toNat) (lenLeA : len.toNat ≤ left.toNat + z.avail_in.toNat) :
    ∃ st' g z' d', storedRest (some (.tab ds)) flush (some r) min_block st have_ left len z h = .ok (st', g) ∧
      StoredStep h g r ds z z' d d' ∧ (st'.brk = false → z'.avail_out.toNat < z.avail_out.toNat) ∧
      (st.last = 0 → st'.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
      (st'.brk = true → g = h ∧ z' = z ∧ d' = d ∧
        ((z.avail_out.toNat : Int) < (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int) + min_block.toNat ∨
          (d.strstart.toNat : Int) - d.block_start.toInt + z.avail_in.toNat < min_block.toNat) ∧
        (flush = Z_FINISH → (z.avail_out.toNat : Int) < (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int) + min_block.toNat ∧
          (z.avail_out.toNat : Int) ≤ (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int) + ((d.strstart.toNat : Int) - d.block_start.toInt) +
            z.avail_in.toNat)) ∧
      (st'.brk = false → Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧
        (z'.avail_in = z.avail_in → Zlib.Deflate.Universal.Quiet.work d' < Zlib.Deflate.Universal.Quiet.work d ∨ st'.last ≠ 0) ∧
        (z'.avail_in.toNat < z.avail_in.toNat → Zlib.Deflate.Universal.Quiet.work d' = 0)) := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  unfold storedRest
  by_cases stop : (len < min_block && ((len == 0 && flush != Z_FINISH) || flush == Z_NO_FLUSH ||
      !(len ≥ left && len - left == z.avail_in))) = true
  · refine ⟨_, h, z, d, by simp only [stop, ite_true]; rfl, ⟨inv, buffers, pend0, out, input, StoredFields.refl d,
      Zlib.Deflate.Universal.Fr.refl inv.good buffers, ⟨fun _ a g => ⟨a, g, rfl⟩, fun _ => rfl⟩⟩,
      fun no => by simp at no, fun zero nz => by exact absurd zero nz, fun _ => ⟨rfl, rfl, rfl, ?_, fun fin => ?_⟩,
      fun no => by simp at no⟩
    all_goals obtain ⟨s1, s2⟩ := Bool.and_eq_true_iff.mp stop
    all_goals have lt1 : len.toNat < min_block.toNat := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true s1)
    all_goals have geo := stored_geom good
    · rcases lenCase with c | c | c
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
      · omega
    rcases lenCase with c | c | c
    · exfalso
      have ge : len ≥ left := UInt32.le_iff_toNat_le.mpr (by omega)
      have sub : len - left = z.avail_in :=
        UInt32.toNat_inj.mp (by rw [UInt32.toNat_sub_of_le _ _ ge]; omega)
      rw [fin, decide_eq_true ge, sub] at s2
      simp [show (Z_FINISH == Z_NO_FLUSH) = false by decide] at s2
    · exact ⟨by omega, by omega⟩
    · omega
  · have stopF : (len < min_block && ((len == 0 && flush != Z_FINISH) || flush == Z_NO_FLUSH ||
        !(len ≥ left && len - left == z.avail_in))) = false := by simpa using stop
    have bits := inv.bi_valid_le
    obtain ⟨after, z1, e, runE, goodE, buffersE, accE, fieldsE, pendE, cursorE, bitsE, staticE, _, sizesE,
        winE, prevE, headE, totE, frE⟩ :=
      stored_emit good buffers out pend0 (shape.cursor pend0) bits.2 good.live.back (by omega) len
        (flush == Z_FINISH && (len ≥ left && len - left == z.avail_in))
    have avail1 : z1.avail_out.toNat + (d.bi_valid.toInt.toNat + 42) / 8 = z.avail_out.toNat := accE.2.2.2.1
    have in1 : z1.avail_in.toNat = z.avail_in.toNat := by have := accE.2.2.1; omega
    have globalsE : LibraryGlobals after := by unfold LibraryGlobals; rw [staticE]; exact inv.globals
    have bsE : e.block_start = d.block_start := by rw [fieldsE]
    have ssE : e.strstart = d.strstart := by rw [fieldsE]
    have wsE : e.window_size = d.window_size := by rw [fieldsE]
    have room := shape.room
    obtain ⟨g, z2, runD, stepD, accD, totD, frD⟩ := stored_direct goodE buffersE globalsE (output_valid_after accE out)
      (input_valid_after accE input) (by rw [bsE]; exact zero.1) left len
      (by rw [bsE, ssE]; omega) (by rw [ssE, wsE]; omega) (by omega) (by omega)
    let e2 := { e with block_start := Int64.ofInt (e.block_start.toInt + (directLeft left len).toNat) }
    have dl := directLeft_le left len
    have fields2 : StoredFields d e2 := by
      show e2 = _
      have f1 : StoredFields d e := by unfold StoredFields; rw [fieldsE]
      exact f1.trans rfl
    have bs2 : e2.block_start.toInt = d.block_start.toInt + (directLeft left len).toNat := by
      show (Int64.ofInt (e.block_start.toInt + (directLeft left len).toNat)).toInt = _
      rw [bsE]
      have := d.strstart.toNat_lt
      exact int64_ofInt_toInt _ (by omega) (by omega)
    have shape2 : Shape e2 := shape_stored shape fields2 level0 (by rw [bs2]; omega) (by rw [bs2]; omega)
      (by show e.bi_valid.toInt ≤ 7; omega) (fun _ => cursorE)
    have account := stream_accounting_trans accE accD
    have invG : DInv g r ds z2 e2 := dinv_stored_keep inv stepD.good fields2 shape2 zero.2.2
      (stepD.static.trans staticE)
      (fun w win => by
        rw [stepD.private_ w (Or.inr (Or.inr (Or.inl (by show e.window = _; rw [fieldsE]; exact win))))]
        exact winE w win)
      (fun p prv => by rw [stepD.words]; exact prevE p prv)
      (fun q hd => by rw [stepD.words]; exact headE q hd)
      account.2.2.2.2.2.2.2.1 account.2.2.2.2.2.2.2.2.1
    let all := decide (len ≥ left) && len - left == z.avail_in
    let last : Int32 := if (flush == Z_FINISH && all) = true then 1 else 0
    have run : (if (decide (len < min_block) && (len == 0 && flush != Z_FINISH || flush == Z_NO_FLUSH || !all)) = true
        then (pure { st with len, left, have_, all, brk := true } : M StoredS)
        else (do
          storedEmit (some (.tab ds)) (some r) len last
          let moved ← storedDirect (some (.tab ds)) (some r) left len
          pure { st with last, len := moved.2, left := moved.1, have_, all, brk := false })) h =
        .ok ({ st with last, len := len - directLeft left len, left := directLeft left len, have_, all, brk := false }, g) := by
      dsimp only [all, last]
      simp only [stopF, Bool.false_eq_true, ite_false, bind_app, runE, runD]
      rfl
    refine ⟨_, g, z2, e2, run, ⟨invG, stepD.buffers, by show e.pending = 0; exact pendE,
      output_valid_after account out, input_valid_after account input, fields2, Zlib.Deflate.Universal.Fr.trans good buffers frE frD,
      sizesE.chain stepD.sizes⟩, fun (_ : false = false) => ?_, fun _ nz => ?_, fun no => by simp at no,
      fun _ => ?_⟩
    · have := account.2.2.2.1
      omega
    · change (if (flush == Z_FINISH && all) = true then (1 : Int32) else 0) ≠ 0 at nz
      have yes : (flush == Z_FINISH && all) = true := by
        cases c : (flush == Z_FINISH && all)
        · rw [c] at nz; exact absurd rfl nz
        · rfl
      simp only [all, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at yes
      obtain ⟨fin, ge, eqIn⟩ := yes
      have dlEq : directLeft left len = left := by
        unfold directLeft; rw [if_neg (by rw [GT.gt, UInt32.lt_iff_toNat_lt]; have := UInt32.le_iff_toNat_le.mp ge; omega)]
      refine ⟨fin, ?_, by show e.bi_valid.toInt = 0; exact bitsE⟩
      have a3 := account.2.2.1
      rw [dlEq, eqIn] at a3
      exact UInt32.toNat_inj.mp (by simp; omega)
    · have l2 : e2.level = 0 := by show e.level = 0; rw [fieldsE]; exact level0
      have ss2 : e2.strstart = d.strstart := ssE
      have w2 := work_l0 l2 shape2
      have w1 := work_l0 level0 shape
      have bsLo := zero.1
      have bsN := Int.toNat_of_nonneg bsLo
      have bs2N : 0 ≤ e2.block_start.toInt := by rw [bs2]; omega
      have bsN2 := Int.toNat_of_nonneg bs2N
      have bsHi := shape.blockStart
      have a3 := account.2.2.1
      have subN : (len - directLeft left len).toNat = len.toNat - (directLeft left len).toNat :=
        UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr dl.1)
      rw [w2, w1, ss2]
      have dlCase : (directLeft left len).toNat = len.toNat ∨ (directLeft left len).toNat = left.toNat := by
        unfold directLeft; split
        · exact Or.inl rfl
        · exact Or.inr rfl
      refine ⟨by omega, fun ea => ?_, fun lt => by rcases dlCase with q | q <;> omega⟩
      have ea' : z2.avail_in.toNat = z.avail_in.toNat := by rw [ea]
      by_cases l0 : len.toNat = 0
      · refine Or.inr ?_
        have lz : len = 0 := UInt32.toNat_inj.mp (by rw [l0]; rfl)
        have mz : decide (len < min_block) = true := decide_eq_true (UInt32.lt_iff_toNat_lt.mpr (by omega))
        rw [mz, Bool.true_and] at stopF
        change (if (flush == Z_FINISH && all) = true then (1 : Int32) else 0) ≠ 0
        have fz : (flush == Z_FINISH) = true := by
          cases c : (flush == Z_FINISH)
          · rw [lz] at stopF; simp [bne, c] at stopF
          · rfl
        have az : all = true := by
          cases c : all
          · dsimp only [all] at c; rw [c] at stopF; simp at stopF
          · rfl
        rw [fz, az]; decide
      · exact Or.inl (by omega)

set_option maxHeartbeats 4000000 in
open Zlib.Deflate.Universal in
/-- **One iteration of the first loop of `deflate_stored`.** -/
theorem stored_iterationS {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st : StoredS) (mbPos : 0 < min_block.toNat)
    (mbW : min_block.toNat ≤ d.w_size.toNat) :
    ∃ st' g z' d', storedBody (some (.tab ds)) flush (some r) min_block st h = .ok (st', g) ∧
      StoredStep h g r ds z z' d d' ∧ (st'.brk = false → z'.avail_out.toNat < z.avail_out.toNat) ∧
      (st.last = 0 → st'.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
      (st'.brk = true → g = h ∧ z' = z ∧ d' = d ∧
        ((z.avail_out.toNat : Int) < (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int) + min_block.toNat ∨
          (d.strstart.toNat : Int) - d.block_start.toInt + z.avail_in.toNat < min_block.toNat) ∧
        (flush = Z_FINISH → (z.avail_out.toNat : Int) < (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int) + min_block.toNat ∧
          (z.avail_out.toNat : Int) ≤ (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int) + ((d.strstart.toNat : Int) - d.block_start.toInt) +
            z.avail_in.toNat)) ∧
      (st'.brk = false → Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧
        (z'.avail_in = z.avail_in → Zlib.Deflate.Universal.Quiet.work d' < Zlib.Deflate.Universal.Quiet.work d ∨ st'.last ≠ 0) ∧
        (z'.avail_in.toNat < z.avail_in.toNat → Zlib.Deflate.Universal.Quiet.work d' = 0)) := by
  have good := inv.good
  have shape := inv.shape
  have zero := shape.levelZero level0
  have bits := inv.bi_valid_le
  have hvN := header_bytes_value d.bi_valid bits.1 bits.2
  unfold storedBody
  simp only [bind_app, ldDeflateState_tab good.live.hs, ldZ_eq, good.live.hz]
  by_cases full : z.avail_out < (d.bi_valid.toUInt32 + 42) >>> 3
  · have fullN : z.avail_out.toNat < ((d.bi_valid.toUInt32 + 42) >>> 3).toNat := UInt32.lt_iff_toNat_lt.mp full
    rw [hvN] at fullN
    have bsHi := shape.blockStart
    refine ⟨_, h, z, d, by simp only [full, decide_true, ite_true]; rfl,
      ⟨inv, buffers, pend0, out, input, StoredFields.refl d,
      Zlib.Deflate.Universal.Fr.refl inv.good buffers, ⟨fun _ a g => ⟨a, g, rfl⟩, fun _ => rfl⟩⟩,
      fun no => by simp at no, fun zero nz => by exact absurd zero nz,
      fun _ => ⟨rfl, rfl, rfl, Or.inl (by omega), fun _ => ⟨by omega, by omega⟩⟩,
      fun no => by simp at no⟩
  · have fullN : ¬ z.avail_out.toNat < ((d.bi_valid.toUInt32 + 42) >>> 3).toNat :=
      fun c => full (UInt32.lt_iff_toNat_lt.mpr c)
    rw [hvN] at fullN
    have room := shape.room
    have ws := good.inv.wsz
    have wsize := good.inv.wsize
    have wbits := good.inv.wbits_hi
    have wpow : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by omega) wbits
    obtain ⟨lsubEq, word, _⟩ := Zlib.Deflate.Universal.Block.flush_length_general (d := d) (by omega)
      shape.blockStart (by omega)
    have lsubRun := congrFun lsubEq h
    have leftN : ((Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64.toUInt32).toNat =
        ((d.strstart.toNat : Int) - d.block_start.toInt).toNat := by
      rw [UInt64.toNat_toUInt32, word]
      apply Nat.mod_eq_of_lt
      omega
    simp only [full, decide_false, Bool.false_eq_true, ite_false, bind_app, lsubRun, pure_app]
    obtain ⟨left, hleft⟩ : ∃ l, l = (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64.toUInt32 :=
      ⟨_, rfl⟩
    rw [← hleft]
    rw [← hleft] at leftN
    have leftEq : (left.toNat : Int) = d.strstart.toNat - d.block_start.toInt := by
      rw [leftN]; have := shape.blockStart; omega
    have haveN : (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat + (d.bi_valid.toInt.toNat + 42) / 8 =
        z.avail_out.toNat := by
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [hvN]; omega)), hvN]
      omega
    have maxN : MAX_STORED.toNat = 65535 := rfl
    have leftLt : left.toNat < 2 ^ 32 := left.toNat_lt
    by_cases c1 : (decide (left < MAX_STORED) && decide (z.avail_in < MAX_STORED - left)) = true
    · have c1N : left.toNat < 65535 ∧ z.avail_in.toNat < 65535 - left.toNat := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at c1
        obtain ⟨a, b⟩ := c1
        have a' := UInt32.lt_iff_toNat_lt.mp a
        have b' := UInt32.lt_iff_toNat_lt.mp b
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))] at b'
        omega
      have sumN : (left + z.avail_in).toNat = left.toNat + z.avail_in.toNat := by
        rw [UInt32.toNat_add]; omega
      simp only [c1, ite_true]
      by_cases c2 : left + z.avail_in > z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3
      · simp only [c2, decide_true, ite_true]
        exact stored_restS inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (Nat.le_refl _) (stored_len_input _ _ _ (by have := UInt32.lt_iff_toNat_lt.mp c2; omega)
            (fun _ => by have := UInt32.lt_iff_toNat_lt.mp c2; omega)) mbPos (Or.inr (Or.inl rfl)) mbW
          (by have := UInt32.lt_iff_toNat_lt.mp c2; rw [sumN] at this; omega)
      · simp only [c2, decide_false, Bool.false_eq_true, ite_false]
        have c2N : ¬ (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat < (left + z.avail_in).toNat :=
          fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
        exact stored_restS inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (by omega) (stored_len_input _ _ _ (by omega) (fun _ => by omega)) mbPos (Or.inl (by rw [sumN])) mbW (by rw [sumN]; omega)
    · simp only [c1, Bool.false_eq_true, ite_false]
      have c1N : ¬ (left.toNat < 65535 ∧ z.avail_in.toNat < 65535 - left.toNat) := by
        intro ⟨a, b⟩
        apply c1
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨UInt32.lt_iff_toNat_lt.mpr (by rw [maxN]; exact a), UInt32.lt_iff_toNat_lt.mpr ?_⟩
        rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by rw [maxN]; omega)), maxN]
        exact b
      by_cases c2 : MAX_STORED > z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3
      · simp only [c2, decide_true, ite_true]
        exact stored_restS inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (Nat.le_refl _) (stored_len_input _ _ _ (by have := UInt32.lt_iff_toNat_lt.mp c2; rw [maxN] at this; omega)
            (fun c => absurd c c1N)) mbPos (Or.inr (Or.inl rfl)) mbW
          (by have := UInt32.lt_iff_toNat_lt.mp c2; rw [maxN] at this; have := c1N; omega)
      · simp only [c2, decide_false, Bool.false_eq_true, ite_false]
        have c2N : ¬ (z.avail_out - (d.bi_valid.toUInt32 + 42) >>> 3).toNat < MAX_STORED.toNat :=
          fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
        rw [maxN] at c2N
        exact stored_restS inv buffers pend0 out input level0 flush min_block _ _ left _ haveN leftEq
          (by rw [maxN]; omega) (stored_len_input _ _ _ (by rw [maxN]; exact Nat.le_refl _) (fun c => absurd c c1N)) mbPos (Or.inr (Or.inr maxN)) mbW
          (by rw [maxN]; have := c1N; omega)

/-- The exit facts of the first loop of `deflate_stored` that stopped without a last block. -/
def LoopExit (flush : Int32) (mb : Nat) (z : ZStream) (d : DeflateState) : Prop :=
  ((z.avail_out.toNat : Int) < (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int) + mb ∨
    (d.strstart.toNat : Int) - d.block_start.toInt + z.avail_in.toNat < mb) ∧
  (flush = Z_FINISH → (z.avail_out.toNat : Int) < (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int) + mb ∧
    (z.avail_out.toNat : Int) ≤ (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int) +
      ((d.strstart.toNat : Int) - d.block_start.toInt) + z.avail_in.toNat)

/-- **The first loop of `deflate_stored`, with its stop**: a stop without a last block leaves
`LoopExit`, and a loop that read input emptied the window part of the block. -/
theorem stored_loopS {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : Zlib.Deflate.Universal.DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (min_block : UInt32) (st0 : StoredS) (start : st0.last = 0)
    (mbPos : 0 < min_block.toNat) (mbW : min_block.toNat ≤ d.w_size.toNat) :
    ∃ st g z' d', cdoWhile (storedBody (some (.tab ds)) flush (some r) min_block)
        (fun st => pure (!st.brk && st.last == 0, st)) st0 h = .ok (st, g) ∧
      StoredStep h g r ds z z' d d' ∧
      (st.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
      (st.last = 0 → LoopExit flush min_block.toNat z' d') ∧
      (z'.avail_in.toNat < z.avail_in.toNat → Zlib.Deflate.Universal.Quiet.work d' = 0) := by
  let W : ZStream → DeflateState → Prop := fun z' d' =>
    Zlib.Deflate.Universal.Quiet.work d' ≤ Zlib.Deflate.Universal.Quiet.work d ∧
    (z'.avail_in.toNat < z.avail_in.toNat → Zlib.Deflate.Universal.Quiet.work d' = 0)
  let P : StoredS → Heap → Prop := fun s g => s.last = 0 ∧ ∃ z' d', StoredStep h g r ds z z' d d' ∧ W z' d'
  let Q : StoredS → Heap → Prop := fun s g => ∃ z' d', StoredStep h g r ds z z' d d' ∧
    (s.last ≠ 0 → flush = Z_FINISH ∧ z'.avail_in = 0 ∧ d'.bi_valid.toInt = 0) ∧
    (s.last = 0 → LoopExit flush min_block.toNat z' d') ∧
    (z'.avail_in.toNat < z.avail_in.toNat → Zlib.Deflate.Universal.Quiet.work d' = 0)
  let μ : StoredS → Heap → Nat := fun _ g => match r.get g with | some z' => z'.avail_out.toNat | none => 0
  have step : ∀ s g, P s g → ∃ s1 g1 c s2 g2, storedBody (some (.tab ds)) flush (some r) min_block s g = .ok (s1, g1) ∧
      (fun st : StoredS => (pure (!st.brk && st.last == 0, st) : M (Bool × StoredS))) s1 g1 = .ok ((c, s2), g2) ∧
      (c = true → P s2 g2 ∧ μ s2 g2 < μ s g) ∧ (c = false → Q s2 g2) := by
    intro s g ⟨l0, z1, d1, now, w1⟩
    have level1 : d1.level = 0 := by rw [now.fields]; exact level0
    have ws1 : d1.w_size = d.w_size := by rw [now.fields]
    obtain ⟨s1, g1, z2, d2, run, next, dec, lastF, brkI, emitI⟩ := stored_iterationS now.inv now.buffers now.pending
      now.out now.input level1 flush min_block s mbPos (by rw [ws1]; exact mbW)
    have total := StoredStep.trans inv.good buffers now next
    have av1 := Zlib.Deflate.Universal.fr_avail now.fr
    have av2 := Zlib.Deflate.Universal.fr_avail next.fr
    have keepK : s1.brk = false → W z2 d2 := by
      intro brk
      obtain ⟨le2, _, k2⟩ := emitI brk
      refine ⟨by have := w1.1; omega, fun lt => ?_⟩
      by_cases l2 : z2.avail_in.toNat < z1.avail_in.toNat
      · exact k2 l2
      · have := w1.2 (by omega); omega
    refine ⟨s1, g1, !s1.brk && s1.last == 0, s1, g1, run, rfl, fun c => ⟨⟨?_, z2, d2, total, ?_⟩, ?_⟩,
      fun c => ?_⟩
    · simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at c
      exact c.2
    · have brk : s1.brk = false := by
        cases e : s1.brk
        · rfl
        · rw [e] at c; simp at c
      exact keepK brk
    · have brk : s1.brk = false := by
        cases e : s1.brk
        · rfl
        · rw [e] at c; simp at c
      show (match r.get g1 with | some z' => z'.avail_out.toNat | none => 0) <
        (match r.get g with | some z' => z'.avail_out.toNat | none => 0)
      rw [next.inv.good.live.hz, now.inv.good.live.hz]
      exact dec brk
    · by_cases b : s1.brk = true
      · obtain ⟨hg, hz, hd, ex1, ex2⟩ := brkI b
        subst hg hz hd
        exact ⟨_, _, total, lastF l0, fun _ => ⟨ex1, ex2⟩, w1.2⟩
      · have b' : s1.brk = false := by simpa using b
        have nz : s1.last ≠ 0 := by
          rw [b'] at c; simpa using c
        exact ⟨z2, d2, total, lastF l0, fun e => absurd e nz, (keepK b').2⟩
  have bound : μ st0 h < fuel := by
    show (match r.get h with | some z' => z'.avail_out.toNat | none => 0) < 2 ^ 64
    rw [inv.good.live.hz]
    have := z.avail_out.toNat_lt
    show z.avail_out.toNat < 2 ^ 64
    omega
  obtain ⟨st, g, run, ⟨z', d', final, lastF, ex, k⟩⟩ := C.cdoWhile_decreasing P Q μ step
    ⟨start, z, d, StoredStep.refl inv buffers pend0 out input, Nat.le_refl _, fun lt => absurd lt (Nat.lt_irrefl _)⟩ bound
  exact ⟨st, g, z', d', run, final, lastF, ex, k⟩

set_option maxHeartbeats 8000000 in
/-- **The refill of the window keeps `DInv`.** -/
theorem stored_refillS {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (level0 : d.level = 0)
    (input : z.avail_in ≠ 0 → z.next_in ≠ .null) :
    ∃ g zF eF used, storedRefill (some (.tab ds)) (some r) d h = .ok ((), g) ∧ DInv g r ds zF eF ∧
      StreamBuffers g r ∧ ByteSizes h g ∧ StreamAccounting z zF used 0 ∧
      (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧ g.static = h.static ∧ g.nalloc = h.nalloc ∧
          Totals z zF used 0 ∧ PrivStep h g r ds d ∧
      ((eF.strstart.toNat : Int) - eF.block_start.toInt = (d.strstart.toNat : Int) - d.block_start.toInt + used) ∧
      (zF.avail_in ≠ 0 → (d.w_size.toNat : Int) ≤ (eF.strstart.toNat : Int) - eF.block_start.toInt) := by
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
            .ok ((), g) ∧ DInv g r ds zF eF ∧ StreamBuffers g r ∧ ByteSizes h g ∧ StreamAccounting z zF used 0 ∧
          (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧ g.static = h.static ∧ g.nalloc = h.nalloc ∧
          Totals z zF used 0 ∧ PrivStep h g r ds d ∧
          ((eF.strstart.toNat : Int) - eF.block_start.toInt = (d.strstart.toNat : Int) - d.block_start.toInt + used) ∧
          used = n.toNat := by
      intro n avail fitN one
      have shapeF : Shape (refillRead (refillSlide d) n) := shape_refill shape level0 (d.strstart - d.w_size) (refillSlide d).insert
        (refillSlide d).«matches» (Int64.ofInt (d.block_start.toInt - d.w_size.toNat)) d.high_water n
        (by omega) i1.2 (by rw [bs1]; omega) (by rw [bs1]; omega) hwLe m1 (fun _ => by omega) (by omega)
      obtain ⟨g, zF, run, invG, buffersG, sizesG, acc, st, na, tot, pv⟩ := refill_finish inv buffers level0 win getW
        (refillSlide d) wa1 size1 ⟨_, _, _, _, _, rfl⟩ hashE n avail
        (by show (d.strstart - d.w_size).toNat + n.toNat ≤ wa.size; omega) (by omega) i1.2 input shapeF
      refine ⟨g, zF, _, n.toNat, run, invG, buffersG, sizesG, acc, ⟨_, _, _, _, _, rfl⟩, st, na, tot, pv, ?_, rfl⟩
      show (((d.strstart - d.w_size) + n).toNat : Int) - (Int64.ofInt (d.block_start.toInt - d.w_size.toNat)).toInt = _
      rw [bs1, UInt32.toNat_add, ssN, Nat.mod_eq_of_lt (by omega)]
      push_cast
      omega
    have condT : (decide (z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32) &&
        decide (d.block_start ≥ d.w_size.toUInt64.toInt64)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨more, far⟩
    simp only [condT, ite_true, bind_app, slide, readAvail _ hz1]
    by_cases c2 : (d.window_size - d.strstart.toUInt64).toUInt32 + d.w_size > z.avail_in
    · have c2N := UInt32.lt_iff_toNat_lt.mp c2
      rw [have1N] at c2N
      simp only [c2, decide_true, ite_true]
      obtain ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, un⟩ := finishA _ (Nat.le_refl _) (by omega) (by omega)
      exact ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, fun nz => absurd (UInt32.toNat_inj.mp (by
        have := a5.2.2.1; rw [un] at this; show _ = 0; omega)) nz⟩
    · have c2N : ¬ z.avail_in.toNat < ((d.window_size - d.strstart.toUInt64).toUInt32 + d.w_size).toNat :=
        fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
      rw [have1N] at c2N
      simp only [c2, decide_false, Bool.false_eq_true, ite_false]
      obtain ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, un⟩ :=
        finishA _ (by rw [have1N]; omega) (by rw [have1N]; exact Nat.le_refl _) (by rw [have1N]; omega)
      refine ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, fun _ => ?_⟩
      rw [have1N] at un
      rw [wk, un]
      omega
  · simp only [Bool.not_eq_true] at cond
    simp only [cond, Bool.false_eq_true, ite_false, bind_app, readAvail h hz]
    have finishB : ∀ n : UInt32, n.toNat ≤ z.avail_in.toNat → n.toNat ≤ d.window_size.toNat - d.strstart.toNat →
        ∃ g zF eF used, storedRead (some (.tab ds)) (some r) n h = .ok ((), g) ∧ DInv g r ds zF eF ∧
          StreamBuffers g r ∧ ByteSizes h g ∧ StreamAccounting z zF used 0 ∧
          (∃ ss ins m bs hw, eF = keepState d ss ins m bs hw) ∧ g.static = h.static ∧ g.nalloc = h.nalloc ∧
          Totals z zF used 0 ∧ PrivStep h g r ds d ∧
          ((eF.strstart.toNat : Int) - eF.block_start.toInt = (d.strstart.toNat : Int) - d.block_start.toInt + used) ∧
          used = n.toNat ∧ (n.toNat = 0 → eF.strstart = d.strstart ∧ eF.block_start = d.block_start) := by
      intro n avail fitN
      have same : keepState d d.strstart d.insert d.«matches» d.block_start d.high_water = d := rfl
      have shapeF := shape_refill shape level0 d.strstart d.insert d.«matches» d.block_start d.high_water n
        (by omega) insLe zero.1 bsHi hwLe shape.slides.1 (fun av => by have := shape.available av; omega) (by omega)
      have hashE : LevelHash (setD { h with bytes := upd h.bytes w (some wa) } ds
          (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water))
          (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water) := by
        rw [same, hSelf]; exact hash0
      obtain ⟨g, zF, run, invG, buffersG, sizesG, acc, st, na, tot, pv⟩ := refill_finish inv buffers level0 win getW
        (keepState d d.strstart d.insert d.«matches» d.block_start d.high_water) wa rfl ⟨_, _, _, _, _, rfl⟩
        hashE n avail (by show d.strstart.toNat + n.toNat ≤ wa.size; omega) (by omega) insLe input shapeF
      rw [same, hSelf] at run
      refine ⟨g, zF, _, n.toNat, run, invG, buffersG, sizesG, acc, ⟨_, _, _, _, _, rfl⟩, st, na, tot, pv, ?_, rfl, fun n0 => by
        have : n = 0 := UInt32.toNat_inj.mp (by rw [n0]; rfl)
        subst this
        exact ⟨by show d.strstart + 0 = d.strstart; simp, rfl⟩⟩
      show ((d.strstart + n).toNat : Int) - d.block_start.toInt = _
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
      push_cast
      omega
    by_cases c2 : (d.window_size - d.strstart.toUInt64).toUInt32 > z.avail_in
    · have c2N := UInt32.lt_iff_toNat_lt.mp c2
      rw [have0N] at c2N
      simp only [c2, decide_true, ite_true]
      obtain ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, un, _⟩ := finishB _ (Nat.le_refl _) (by omega)
      exact ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, fun nz => absurd (UInt32.toNat_inj.mp (by
        have := a5.2.2.1; rw [un] at this; show _ = 0; omega)) nz⟩
    · have c2N : ¬ z.avail_in.toNat < ((d.window_size - d.strstart.toUInt64).toUInt32).toNat :=
        fun c => c2 (UInt32.lt_iff_toNat_lt.mpr c)
      rw [have0N] at c2N
      simp only [c2, decide_false, Bool.false_eq_true, ite_false]
      obtain ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, un, n0⟩ :=
        finishB _ (by rw [have0N]; omega) (by rw [have0N]; exact Nat.le_refl _)
      refine ⟨g, zF, eF, used, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, wk, fun nz => ?_⟩
      rw [have0N] at un
      have zl := a5.2.2.1
      have zN : zF.avail_in.toNat ≠ 0 := fun c => nz (UInt32.toNat_inj.mp (by rw [c]; rfl))
      have nc : ¬ (z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32 ∧
          d.block_start ≥ d.w_size.toUInt64.toInt64) := by
        intro ⟨x, y⟩; rw [decide_eq_true x, decide_eq_true y] at cond; simp at cond
      have gt : z.avail_in > (d.window_size - d.strstart.toUInt64).toUInt32 := by
        rw [GT.gt, UInt32.lt_iff_toNat_lt, have0N]; omega
      have lt : ¬ d.block_start ≥ d.w_size.toUInt64.toInt64 := fun c => nc ⟨gt, c⟩
      have wsN : d.w_size.toUInt64.toInt64.toInt = d.w_size.toNat := u32_toInt64_toInt _
      have hlt : ¬ ((d.w_size.toNat : Int) ≤ d.block_start.toInt) :=
        fun c => lt (Int64.le_iff_toInt_le.mpr (by rw [wsN]; exact c))
      rw [wk, un]
      omega

set_option maxHeartbeats 8000000 in
open Zlib.Deflate.Universal in
/-- The final block of `deflate_stored` with input: it lowers the work term and reads nothing. -/
theorem stored_finalS {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (buffers : StreamBuffers h r) (pend0 : d.pending = 0) (out : z.next_out ≠ .null)
    (level0 : d.level = 0) (flush last0 : Int32) (lastZero : last0 = 0)
    (P1 : z.avail_in ≠ 0 → (d.w_size.toNat : Int) ≤ (d.strstart.toNat : Int) - d.block_start.toInt)
    (P2 : z.avail_in ≠ 0 → z.avail_out.toNat + 1 ≤ (d.bi_valid.toInt.toNat + 42) / 8 + min (d.pending_buf_size.toNat - 5) d.w_size.toNat)
    (P3 : flush = Z_FINISH → z.avail_out.toNat + 1 ≤ (d.bi_valid.toInt.toNat + 42) / 8 + min (d.pending_buf_size.toNat - 5) d.w_size.toNat)
    (P4 : flush = Z_FINISH → z.avail_in = 0 →
      (z.avail_out.toNat : Int) ≤ (((d.bi_valid.toInt.toNat + 42) / 8 : Nat) : Int) + ((d.strstart.toNat : Int) - d.block_start.toInt)) :
    ∃ ret g z' d', storedFinal (some (.tab ds)) flush (some r) last0 h = .ok (ret, g) ∧
      r.get g = some z' ∧ g.dstates ds = some d' ∧ (z'.avail_in = 0 ∨ z'.avail_out = 0) ∧
      (ret = need_more ∨ ret = finish_started →
        z'.avail_out = 0 ∨ (ret = need_more ∧ z'.avail_in = 0 ∧ flush ≠ Z_FINISH)) := by
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
  have geo := stored_geom good
  have hv6 : (d.bi_valid.toInt.toNat + 42) / 8 ≤ 6 := by omega
  have HvEq : Hv.toNat = min (d.pending_buf_size.toNat - (d.bi_valid.toInt.toNat + 42) / 8) 65535 := by
    rw [hHv]
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
    · rename_i nlt
      have nlt' : ¬ 65535 < d.pending_buf_size.toNat - (d.bi_valid.toInt.toNat + 42) / 8 :=
        fun c => nlt (UInt64.lt_iff_toNat_lt.mpr (by rw [sub, m]; exact c))
      rw [UInt64.toNat_toUInt32, sub]
      omega
  have lenEq : (MIN left Hv).toNat = min left.toNat Hv.toNat := min_toNat left Hv
  have mbEq : (MIN Hv d.w_size).toNat = min Hv.toNat d.w_size.toNat := min_toNat Hv d.w_size
  have bsLo := zero.1
  have bsHi := shape.blockStart
  have leftI : (left.toNat : Int) = (d.strstart.toNat : Int) - d.block_start.toInt := by rw [leftN]; omega
  have wd := work_l0 level0 shape
  by_cases c : (decide (left ≥ MIN Hv d.w_size) || ((left != 0 || flush == Z_FINISH) && flush != Z_NO_FLUSH &&
      z.avail_in == 0 && decide (left ≤ Hv))) = true
  · obtain ⟨p, H1, bs, H2, after, z', e, produced, add, blk, lad, wrt, fl, goodA, buffersA, accA, fieldsA, bsA,
        bvA, cursorA, staticA, nallocA, winA, prevA, headA, totA, frA, cntA, remA⟩ :=
      stored_block_flushQ good buffers out pend0 (shape.cursor pend0) bits.2 zero.1 (MIN left Hv)
        (by have := shape.blockStart; omega) (by omega) (by omega)
        (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left)
    have shapeA : Shape e := shape_stored shape fieldsA level0 (by rw [bsA]; omega)
      (by rw [bsA]; have := shape.blockStart; omega) (by omega) cursorA
    have invA : DInv after r ds z' e := dinv_stored_keep inv goodA fieldsA shapeA zero.2.2 staticA winA prevA headA
      accA.2.2.2.2.2.2.2.1 accA.2.2.2.2.2.2.2.2.1
    have levelA : e.level = 0 := by rw [fieldsA]; exact level0
    have outA := accA.2.2.2.1
    have inA : z'.avail_in = z.avail_in := UInt32.toNat_inj.mp (by have := accA.2.2.1; omega)
    have fullA : z.avail_out.toNat ≤ (d.bi_valid.toInt.toNat + 42) / 8 + (MIN left Hv).toNat → z'.avail_out = 0 := by
      intro le
      exact UInt32.toNat_inj.mp (by
        have : z'.avail_out.toNat = 0 := by omega
        rw [this]; rfl)
    have bigA : z.avail_in ≠ 0 → z'.avail_out = 0 := fun nz => by
      have := P1 nz; have := P2 nz
      exact fullA (by omega)
    simp only [c, ite_true, bind_app, add, blk, lad, wrt, fl]
    by_cases l0 : ((if (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) = true then (1 : Int32) else 0) != 0) = true
    · obtain ⟨wrRun, invB, buffersB⟩ := bi_used_step invA buffersA levelA
      have cf : (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) = true := by
        by_cases cf : (flush == Z_FINISH && z.avail_in == 0 && MIN left Hv == left) = true
        · exact cf
        · rw [if_neg cf] at l0; simp at l0
      simp only [Bool.and_eq_true, beq_iff_eq] at cf
      obtain ⟨⟨f, a0⟩, ml⟩ := cf
      have o0 : z'.avail_out = 0 := fullA (by have := P4 f a0; rw [ml]; omega)
      exact ⟨finish_started, _, z', _, by simp only [l0, ite_true, bind_app, wrRun]; rfl, invB.good.live.hz,
        invB.good.live.hs, Or.inr o0, fun _ => Or.inl o0⟩
    · simp only [Bool.not_eq_true] at l0
      have claim1 : z'.avail_in = 0 ∨ z'.avail_out = 0 := by
        by_cases a0 : z.avail_in = 0
        · exact Or.inl (inA.trans a0)
        · exact Or.inr (bigA a0)
      refine ⟨need_more, after, z', e, by simp only [l0, Bool.false_eq_true, ite_false, bind_app, pure_app],
        invA.good.live.hz, invA.good.live.hs, claim1, fun _ => ?_⟩
      by_cases o0 : z'.avail_out = 0
      · exact Or.inl o0
      · have a0 : z.avail_in = 0 := Classical.byContradiction fun nz => o0 (bigA nz)
        refine Or.inr ⟨rfl, inA.trans a0, fun f => o0 ?_⟩
        have hne : MIN left Hv ≠ left := fun e => by
          rw [f, a0, e] at l0; simp at l0
        have hneN : (MIN left Hv).toNat ≠ left.toNat := fun x => hne (UInt32.toNat_inj.mp x)
        have := P3 f
        exact fullA (by omega)
  · simp only [Bool.not_eq_true] at c
    simp only [c, Bool.false_eq_true, ite_false]
    subst lastZero
    have h1 : ¬ (left ≥ MIN Hv d.w_size) := by
      intro ge; rw [decide_eq_true ge] at c; simp at c
    have a1 : ¬ (MIN Hv d.w_size).toNat ≤ left.toNat := fun x => h1 (UInt32.le_iff_toNat_le.mpr x)
    have a0 : z.avail_in = 0 := Classical.byContradiction fun nz => by have := P1 nz; omega
    refine ⟨need_more, h, z, d, by simp [bind_app], good.live.hz, good.live.hs, Or.inl a0,
      fun _ => Or.inr ⟨rfl, a0, fun f => ?_⟩⟩
    have h2 : ¬ (left ≤ Hv) := by
      intro le
      rw [f, a0, decide_eq_true le] at c
      simp [show (Z_FINISH != Z_NO_FLUSH) = true by decide] at c
    have a2 : ¬ left.toNat ≤ Hv.toNat := fun x => h2 (UInt32.le_iff_toNat_le.mpr x)
    omega

set_option maxHeartbeats 8000000 in
open Zlib.Deflate.Universal in
/-- **The end of `deflate_stored` with input** (`storedEnd`): the work term rises by at most the bytes
the refill reads; with no input consumed and input left, it ends as `QEnd` asks. -/
theorem stored_endS {g : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv g r ds z d) (buffers : StreamBuffers g r) (pend0 : d.pending = 0)
    (out : z.next_out ≠ .null) (input : z.avail_in ≠ 0 → z.next_in ≠ .null) (level0 : d.level = 0)
    (flush : Int32) (mb used0 : UInt32) (st : StoredS) (consumed : Nat)
    (count : used0.toNat = z.avail_in.toNat + consumed)
    (cursor : consumed ≠ 0 → ∃ ref io, z.next_in = .ref ref io ∧ consumed ≤ io)
    (lastF : st.last ≠ 0 → flush = Z_FINISH ∧ z.avail_in = 0 ∧ d.bi_valid.toInt = 0)
    (fin0 : st.last = 0 → LoopExit flush (min (d.pending_buf_size.toNat - 5) d.w_size.toNat) z d)
    (K : consumed ≠ 0 → Quiet.work d = 0) :
    ∃ ret g' z' d', storedEnd (some (.tab ds)) flush (some r) mb used0 st g = .ok (ret, g') ∧
      r.get g' = some z' ∧ g'.dstates ds = some d' ∧ (z'.avail_in = 0 ∨ z'.avail_out = 0) ∧
      (ret = need_more ∨ ret = finish_started →
        z'.avail_out = 0 ∨ (ret = need_more ∧ z'.avail_in = 0 ∧ flush ≠ Z_FINISH)) := by
  have good := inv.good
  have hz := good.live.hz
  have readAvail : ∀ H : Heap, r.get H = some z → zrd (some r) (·.avail_in) H = .ok (z.avail_in, H) := by
    intro H hzH; simp [zrd_eq, hzH]
  have usedN : (used0 - z.avail_in).toNat = consumed := by
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by omega))]; omega
  have w0 := work_l0 level0 inv.shape
  obtain ⟨g1, g2, e2, keepRun, hwRun, inv2, buffers2, pend1, level1, bv1, wk2, gz2, keep0, keepK, pbs2, ws2⟩ : ∃ g1 g2 e2,
      (if (used0 - z.avail_in != 0) = true then storedKeep (some (.tab ds)) (some r) (used0 - z.avail_in)
        else pure ()) g = .ok ((), g1) ∧
      wr (some (.tab ds)) (fun d => { d with high_water := if d.high_water < d.strstart.toUInt64 then d.strstart.toUInt64 else d.high_water }) g1 =
        .ok ((), g2) ∧
      DInv g2 r ds z e2 ∧ StreamBuffers g2 r ∧ e2.pending = 0 ∧ e2.level = 0 ∧ e2.bi_valid = d.bi_valid ∧
      Quiet.work e2 ≤ Quiet.work d ∧ e2.gzindex = d.gzindex ∧
      (consumed = 0 → e2.strstart = d.strstart ∧ e2.block_start = d.block_start) ∧
      (consumed ≠ 0 → Quiet.work e2 = 0) ∧
      e2.pending_buf_size = d.pending_buf_size ∧ e2.w_size = d.w_size := by
    by_cases u0 : (used0 - z.avail_in != 0) = true
    · have nz : consumed ≠ 0 := by
        intro c; rw [← usedN] at c; simp at u0; exact u0 (UInt32.toNat_inj.mp (by rw [c]; rfl))
      obtain ⟨ref, io, src, le⟩ := cursor nz
      obtain ⟨ia, inGet, inBound⟩ := caller_input_array good buffers src
      have apartW : ∀ w, d.window = .ref (.blk w) 0 → ref ≠ .blk w :=
        fun w win => Ne.symm (caller_input_window_separate good buffers win src)
      obtain ⟨gm, g2, e2, run, wrun, inv2, buffers2, _, ⟨ss, ins, m, bs, hw, rfl⟩, _, _, privK⟩ :=
        stored_keep inv buffers level0 (used0 - z.avail_in) src inGet (by omega) (by rw [usedN]; exact le)
          apartW (input_not_state good buffers src)
      obtain ⟨v, hv⟩ := keep_last run
      have hs2 := wr_state wrun hv
      have e2eq := Option.some.inj (inv2.good.live.hs.symm.trans hs2)
      have bsEq : (keepState d ss ins m bs hw).block_start = (keepState d ss ins m bs hw).strstart.toUInt64.toInt64 := by
        rw [e2eq]
      have wk : Quiet.work (keepState d ss ins m bs hw) = 0 := by
        rw [work_l0 (show (keepState d ss ins m bs hw).level = 0 from level0) inv2.shape, bsEq, u32_toInt64_toInt]
        simp
      exact ⟨gm, g2, _, by simp only [u0, ite_true, run], wrun, inv2, buffers2, pend0, level0, rfl,
        by rw [wk]; exact Nat.zero_le _, rfl, fun c => absurd c nz, fun _ => wk, rfl, rfl⟩
    · obtain ⟨hwRun, inv2, buffers2, _, _⟩ := high_water_step inv buffers level0
      exact ⟨g, _, _, by simp only [u0, Bool.false_eq_true, ite_false]; rfl, hwRun, inv2, buffers2, pend0, level0, rfl,
        Nat.le_of_eq rfl, rfl, fun _ => ⟨rfl, rfl⟩, fun c => absurd (by rw [← usedN]; simp at u0; rw [u0]; rfl) c, rfl, rfl⟩
  have hz2 := inv2.good.live.hz
  unfold storedEnd
  simp only [ite_seq]
  simp only [bind_app, readAvail g hz, keepRun, hwRun]
  by_cases lastC : (st.last != 0) = true
  · obtain ⟨wrRun, inv3, buffers3⟩ := bi_used_step inv2 buffers2 level1
    have facts := lastF (by simpa using lastC)
    exact ⟨finish_done, _, z, _, by simp only [lastC, ite_true, bind_app, wrRun]; rfl, inv3.good.live.hz,
      inv3.good.live.hs, Or.inl facts.2.1, fun e => by rcases e with e | e <;> exact absurd e (by decide)⟩
  · simp only [Bool.not_eq_true] at lastC
    simp only [lastC, Bool.false_eq_true, ite_false, bind_app, ldDeflateState_tab inv2.good.live.hs, readAvail _ hz2]
    by_cases early : (flush != Z_NO_FLUSH && flush != Z_FINISH && z.avail_in == 0 &&
        (e2.strstart.toUInt64.toInt64 == e2.block_start)) = true
    · have early' := early
      simp only [Bool.and_eq_true, beq_iff_eq] at early'
      refine ⟨block_done, _, z, _, by simp only [early, ite_true]; rfl, hz2, inv2.good.live.hs, Or.inl early'.1.2,
        fun e => by rcases e with e | e <;> exact absurd e (by decide)⟩
    · simp only [Bool.not_eq_true] at early
      simp only [early, Bool.false_eq_true, ite_false]
      have l0 : st.last = 0 := by simpa using lastC
      obtain ⟨g3, z3, e3, u3, refillRun, inv3, buffers3, _, acc3, ⟨_, _, _, _, _, ke3⟩, _, _, tot3, priv3, wk3, R2⟩ :=
        stored_refillS inv2 buffers2 level1 input
      have pend3 : e3.pending = 0 := by rw [ke3]; exact pend1
      have level3 : e3.level = 0 := by rw [ke3]; exact level1
      have a3 := acc3.2.2.1
      have o3 := acc3.2.2.2.1
      have bvE : e3.bi_valid = d.bi_valid := by rw [ke3]; exact bv1
      have pbsE : e3.pending_buf_size = d.pending_buf_size := by rw [ke3]; exact pbs2
      have wsE : e3.w_size = d.w_size := by rw [ke3]; exact ws2
      have w0 := work_l0 level0 inv.shape
      have w2 := work_l0 level1 inv2.shape
      have bs0 := (inv.shape.levelZero level0).1
      have bs2 := (inv2.shape.levelZero level1).1
      have bs0N := Int.toNat_of_nonneg bs0
      have bs2N := Int.toNat_of_nonneg bs2
      have hi0 := inv.shape.blockStart
      have hi2 := inv2.shape.blockStart
      have left2 : (e2.strstart.toNat : Int) - e2.block_start.toInt =
          (d.strstart.toNat : Int) - d.block_start.toInt := by
        by_cases c0 : consumed = 0
        · obtain ⟨s, b⟩ := keep0 c0; rw [s, b]
        · have := keepK c0; have := K c0; omega
      obtain ⟨E1, E2⟩ := fin0 l0
      have geo := stored_geom good
      obtain ⟨ret, g4, z4, e4, finalRun, hz4, hs4, C1, C2⟩ :=
        stored_finalS inv3 buffers3 pend3 (output_valid_after acc3 out) level3 flush st.last (by simpa using lastC)
          (fun nz => by have := R2 nz; rw [ws2] at this; rw [wsE]; exact this)
          (fun nz => by
            rw [bvE, pbsE, wsE]
            have r2 := R2 nz
            rw [ws2] at r2
            have : z3.avail_in.toNat ≠ 0 := fun c => nz (UInt32.toNat_inj.mp (by rw [c]; rfl))
            rcases E1 with e | e <;> omega)
          (fun f => by rw [bvE, pbsE, wsE]; have := (E2 f).1; omega)
          (fun f z0 => by
            rw [bvE]
            have := (E2 f).2
            have : z3.avail_in.toNat = 0 := by rw [z0]; rfl
            omega)
      exact ⟨ret, g4, z4, e4, by simp only [bind_app, refillRun, finalRun], hz4, hs4, C1, C2⟩

set_option maxHeartbeats 4000000 in
/-- **`deflate_stored` stops on a full output or an empty input**, and `need_more` or `finish_started`
with output room left come only with no input left and, for `need_more`, without `Z_FINISH`. -/
theorem stored_runS {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (inv : DInv h r ds z d) (entry : StratIn h r z d) (flush : Int32) (level : d.level = 0) :
    ∃ bstate after z' d', C.run (Zlib.Deflate.deflate_stored (some (.tab ds)) flush) h = .ok (bstate, after) ∧
      r.get after = some z' ∧ after.dstates ds = some d' ∧ (z'.avail_in = 0 ∨ z'.avail_out = 0) ∧
      (bstate = need_more ∨ bstate = finish_started →
        z'.avail_out = 0 ∨ (bstate = need_more ∧ z'.avail_in = 0 ∧ flush ≠ Z_FINISH)) := by
  have good := inv.good
  have hz := good.live.hz
  have strm := good.live.back
  have geo := stored_geom good
  have mbN : ((MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32).toNat =
      min (d.pending_buf_size.toNat - 5) d.w_size.toNat := by
    have sub : (d.pending_buf_size - 5).toNat = d.pending_buf_size.toNat - 5 :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
    have wsN : d.w_size.toUInt64.toNat = d.w_size.toNat := by simp
    unfold MIN
    split
    · rename_i lt
      have lt' := UInt64.lt_iff_toNat_lt.mp lt
      rw [sub, wsN] at lt'
      rw [UInt64.toNat_toUInt32, wsN]
      omega
    · rename_i nlt
      have nlt' : ¬ d.w_size.toNat < d.pending_buf_size.toNat - 5 :=
        fun c => nlt (UInt64.lt_iff_toNat_lt.mpr (by rw [sub, wsN]; exact c))
      rw [UInt64.toNat_toUInt32, sub]
      omega
  obtain ⟨st, g, z1, d1, loopRun, step, lastF, ex, K⟩ := stored_loopS inv entry.buffers entry.pending
    entry.out entry.input level flush (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32
    { last := 0, len := 0, left := 0, have_ := 0, all := false, brk := false } rfl
    (by rw [mbN]; omega) (by rw [mbN]; omega)
  have level1 : d1.level = 0 := by rw [step.fields]; exact level
  obtain ⟨u1, p1, acc1, tot1⟩ := step.account
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
  have pbs1 : d1.pending_buf_size = d.pending_buf_size := by rw [step.fields]
  have ws1 : d1.w_size = d.w_size := by rw [step.fields]
  have readAvail : zrd (some r) (·.avail_in) h = .ok (z.avail_in, h) := by simp [zrd_eq, hz]
  obtain ⟨ret, g', z', d', endRun, hz', hs', C1, C2⟩ :=
    stored_endS step.inv step.buffers step.pending step.out step.input level1 flush
      (MIN (d.pending_buf_size - 5) d.w_size.toUInt64).toUInt32 z.avail_in st u1 count cursor lastF
      (fun l0 => by rw [pbs1, ws1, ← mbN]; exact ex l0) (fun c => K (by omega))
  refine ⟨ret, g', z', d', ?_, hz', hs', C1, C2⟩
  simp only [C.run, deflate_stored_source, bind_app, ldDeflateState_tab good.live.hs, strm, readAvail, loopRun,
    endRun]

end Zlib.Deflate.Engine.Proofs

namespace Zlib.Deflate.Universal.Quiet
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs Zlib.Deflate.Universal.Call
set_option autoImplicit false

/-- **`StoredStop`**: at level 0 the strategy run ends with no input or no output room, and
`need_more` or `finish_started` with room left come only with no input left and, for `need_more`,
without `Z_FINISH`. -/
theorem stored_stop : StoredStop := by
  intro h r ds z d flush b a z1 d1 inv entry l0 run hz1 hs1
  obtain ⟨b', a', z', d', run', hz', hs', C1, C2⟩ := stored_runS inv entry.toIn flush l0
  have runD : dispatch (some (.tab ds)) flush d h = .ok (b', a') := by
    simp only [C.run] at run'
    simp [dispatch, l0, run']
  have e := run.symm.trans runD
  simp only [Except.ok.injEq, Prod.mk.injEq] at e
  obtain ⟨hb, ha⟩ := e
  subst hb ha
  have zE : z' = z1 := Option.some.inj (hz'.symm.trans hz1)
  subst zE
  exact ⟨C1, C2⟩

/-- **`DeflateQuietIn`**, with `StoredStop` proved. -/
theorem deflate_quiet_in_holds :
  ∃ (Φ : Int32 → Heap → ZStreamRef → Nat) (Quiet : Int32 → Heap → ZStreamRef → Prop),
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 → 8 ≤ z.avail_out.toNat →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = 0 → Φ flush after r < Φ flush h r) ∧
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out ≠ 0 → Quiet flush after r) ∧
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      Quiet flush h r → 0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in = 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = z.avail_out) ∧
    (∀ (flush : Int32) (h after : Heap) (r : ZStreamRef) (z z' : ZStream), StreamReachable .deflate h r →
      Rebuffer h after r → r.get h = some z →
      r.get after = some z' → z'.next_in = z.next_in → z'.avail_in = z.avail_in →
      Φ flush after r = Φ flush h r ∧ (Quiet flush h r → Quiet flush after r)) ∧
    -- (B)
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState),
      0 ≤ flush.toInt → flush.toInt ≤ 4 → StreamReachable .deflate h r → r.get h = some z →
      z.state = some (.deflate k) → h.dstates k = some d → d.gzhead = none → Φ flush h r < 2 ^ 62) ∧
    -- (1')
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (value : Int32) (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.next_out ≠ .null → z.avail_in ≠ 0 → 8 ≤ z.avail_out.toNat →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → r.get after = some z' →
      z'.avail_out = 0 → Φ flush after r + 2 ^ 30 * z'.avail_in.toNat < Φ flush h r + 2 ^ 30 * z.avail_in.toNat) ∧
    -- (2')
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState) (value : Int32)
      (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.state = some (.deflate k) → h.dstates k = some d → d.status ≠ FINISH_STATE →
      z.next_out ≠ .null → z.avail_in ≠ 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → value ≠ Z_STREAM_ERROR →
      r.get after = some z' → z'.avail_out ≠ 0 → z'.avail_in = 0 ∧ Quiet flush after r) ∧
    -- (2f)
    (∀ (flush : Int32) (h : Heap) (r : ZStreamRef) (z : ZStream) (k : Nat) (d : DeflateState) (value : Int32)
      (after : Heap) (z' : ZStream),
      0 ≤ flush.toInt → flush.toInt ≤ 4 →
      StreamReachable .deflate h r → StreamBuffers h r → ActiveHeader h r →
      r.get h = some z → z.state = some (.deflate k) → h.dstates k = some d → d.status = FINISH_STATE →
      z.next_out ≠ .null → z.avail_in ≠ 0 → z.avail_out ≠ 0 →
      Call.execute (.deflate (some r) flush) default h = .ok ((value, default), after) → value ≠ Z_STREAM_ERROR →
      r.get after = some z' → z'.avail_out ≠ 0 →
      z'.avail_in = z.avail_in ∧ ∃ d', after.dstates k = some d' ∧ d'.status = FINISH_STATE ∧ d'.pending = 0) :=
  deflate_quiet_in_of stored_stop

end Zlib.Deflate.Universal.Quiet

#print axioms Zlib.Deflate.Universal.Quiet.stored_stop
#print axioms Zlib.Deflate.Universal.Quiet.deflate_quiet_in_holds
