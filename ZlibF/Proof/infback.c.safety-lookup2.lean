import ZlibF.Proof.«infback.c.safety-table»
import ZlibF.Proof.«inflate.c.lookup-subtable»

/-!
# infback.c: the second-level table lookup on the loop invariant

`lookup2_p`: `for (;;) { here = TABLE[last.val + (BITS(last.bits + last.op) >> last.bits)];
if (last.bits + here.bits <= bits) break; PULLBYTE(); }` after a root link `last` whose second
level lies inside the table (`LinkOK`). The table survives `PULLBYTE()`. The result is the
second-level entry the held bits select, and where the loop last pulled a byte (`Pulled2`).
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
open Zlib.Inffast.Spec (LinkOK)
set_option autoImplicit false

/-- The second-level entry that `hold` selects below the link `last`. -/
def subVal (ca : Array Code) (off : Nat) (last : Code) (hold : Nat) : Code :=
  ca.getD (off + last.val.toNat + hold % 2 ^ (last.bits.toNat + last.op.toNat) / 2 ^ last.bits.toNat) default

/-- The body of the second-level lookup loop. -/
def lk2Body (c : BCtx) (dist : Bool) : X Bool := do
  let s ← ldInflateState c.st
  let tab := if dist then s.distcode else s.lencode
  let last := (← get).last
  let b ← BITS (last.bits.toUInt32 + last.op.toUInt32)
  let sh ← shr32 b last.bits.toUInt32
  let here ← Ptr.index tab ((last.val.toUInt32 + sh).toNat : Int)
  modify fun l => { l with here := here }
  if (last.bits.toUInt32 + here.bits.toUInt32) <= (← get).bits then return true
  Zlib.Infback.PULLBYTE c
  return false

theorem lookup2_eq (c : BCtx) (dist : Bool) : Zlib.Infback.lookup2 c dist = xloopBrk (lk2Body c dist) := rfl

/-- One trip of the second-level loop. -/
theorem lk2Body_run (c : BCtx) {i : Nat} (dist : Bool) {h : Heap} {s : InflateState} (l : IL)
    (hc : c.st = some (.tab i)) (hs : h.istates i = some s) {ref : CodeRef} {off : Nat} {ca : Array Code}
    {P : Nat → Code → Prop} (tab : (if dist then s.distcode else s.lencode) = .ref ref off)
    (get : Space.get h ref = some ca) (link : LinkOK P ca off l.last) :
    runX (lk2Body c dist) l h =
      if l.last.bits.toUInt32 + (subVal ca off l.last l.hold.toNat).bits.toUInt32 ≤ l.bits then
        .ok ((.ok true, { l with here := subVal ca off l.last l.hold.toNat }), h)
      else runX (do Zlib.Infback.PULLBYTE c; pure false : X Bool)
        { l with here := subVal ca off l.last l.hold.toNat } h := by
  generalize hlast : l.last = last at link
  let width := last.bits.toUInt32 + last.op.toUInt32
  have widthNat : width.toNat = last.bits.toNat + last.op.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32,
      Nat.mod_eq_of_lt (by have := link.1; have := link.2.2.1; omega)]
  have widthBound : width.toNat < 32 := by rw [widthNat]; have := link.1; have := link.2.2.1; omega
  let mask := l.hold.toUInt32 &&& ((1 : UInt32) <<< width - 1)
  let shifted := mask >>> last.bits.toUInt32
  have maskNat : mask.toNat = l.hold.toNat % 2 ^ width.toNat := BITS_toNat l width widthBound
  have shiftNat : shifted.toNat = subLookupIndex last l := by
    rw [UInt32.toNat_shiftRight, UInt8.toNat_toUInt32,
      Nat.mod_eq_of_lt (by have := link.1; omega), Nat.shiftRight_eq_div_pow]
    rw [maskNat, widthNat]
    rfl
  have indexNat : (last.val.toUInt32 + shifted).toNat = last.val.toNat + subLookupIndex last l := by
    rw [UInt32.toNat_add, UInt16.toNat_toUInt32, shiftNat]
    apply Nat.mod_eq_of_lt
    have valBound := UInt16.toNat_lt last.val
    have powBound : 2 ^ last.op.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) link.2.2.1
    have indexBound := subLookupIndex_lt last l
    omega
  have inside : off + (last.val.toUInt32 + shifted).toNat < ca.size := by
    rw [indexNat]
    have capacity := link.2.2.2.1
    have := subLookupIndex_lt last l
    omega
  have read := Ptr.index_ok (off := off) (i := (last.val.toUInt32 + shifted).toNat) get inside
  have actual : ca[off + (last.val.toUInt32 + shifted).toNat] = subVal ca off last l.hold.toNat := by
    unfold subVal
    rw [Array.getD_eq_getD_getElem?, Nat.add_assoc, ← show last.val.toNat + subLookupIndex last l =
        last.val.toNat + l.hold.toNat % 2 ^ (last.bits.toNat + last.op.toNat) / 2 ^ last.bits.toNat from rfl,
      ← indexNat, Array.getElem?_eq_getElem inside, Option.getD_some]
  have bitsRun := BITS_run l h width widthBound
  have shiftRun : shr32 mask last.bits.toUInt32 h = .ok (shifted, h) := by
    rw [shr32_run _ _ (by rw [UInt8.toNat_toUInt32]; have := link.1; omega)]; rfl
  dsimp only [mask, shifted, width] at read actual shiftRun bitsRun
  unfold lk2Body
  rw [hc]
  have load : ldInflateState (some (.tab i)) h = .ok (s, h) := ldInflateState_tab hs
  simp only [runX_bind, runX_lift_ok load, tab, runX_get, hlast, bitsRun, runX_lift_ok shiftRun,
    runX_lift_ok read, actual, runX_modify]
  by_cases fit : last.bits.toUInt32 + (subVal ca off last l.hold.toNat).bits.toUInt32 ≤ l.bits
  all_goals simp only [fit, ite_true, ite_false, runX_bind, runX_pure]

/-- What the second-level loop did with the bits: none were pulled, or the last byte was pulled
when `bq` bits `hq` were held and the link and the entry they selected needed more than `bq`. -/
def Pulled2 (ca : Array Code) (off : Nat) (last : Code) (l l' : IL) : Prop :=
  (l'.bits = l.bits ∧ l'.hold = l.hold) ∨
  ∃ bq hq, l.bits.toNat ≤ bq ∧ hq < 2 ^ bq ∧ bq < last.bits.toNat + (subVal ca off last hq).bits.toNat ∧
    l'.bits.toNat = bq + 8 ∧ l'.hold.toNat % 2 ^ bq = hq

/-- `PInv` does not read `last`. -/
theorem PInv.withLast {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) (v : Code) :
    PInv c pr h0 h { l with last := v } log :=
  ⟨I.cstrm, I.cst, I.valid, I.winRoot, I.put, I.chunk, I.held, I.bits, I.proto, I.frame, I.live, I.mode,
    I.platform, I.fit, I.chunkBlk⟩

/-- **The second-level lookup on the invariant.** It ends with the second-level entry the held
bits select below the link `l.last`, whose bits with the link's are held, or with `Z_BUF_ERROR`
from `in`. -/
theorem lookup2_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (dist : Bool) {h0 h : Heap} {l : IL} {log : BackLog}
    (I : PInv c pr h0 h l log) {s : InflateState} (hs : h.istates i = some s) {ref : CodeRef} {off : Nat}
    {ca : Array Code} (tab : (if dist then s.distcode else s.lencode) = .ref ref off) (refOk : TabRef i ref)
    (get : Space.get h ref = some ca) {P : Nat → Code → Prop} (link : LinkOK P ca off l.last)
    (sub15 : ∀ j, j < 2 ^ l.last.op.toNat →
      l.last.bits.toNat + (ca.getD (off + l.last.val.toNat + j) default).bits.toNat ≤ 15) :
    ∃ res l' h' log', runX (Zlib.Infback.lookup2 c dist) l h = .ok ((res, l'), h') ∧
      PInv c pr h0 h' l' log' ∧ h'.istates i = h.istates i ∧
      (res = .ok () → l'.put = l.put ∧ l'.left = l.left ∧ l'.last = l.last ∧
        l'.here = subVal ca off l.last l'.hold.toNat ∧
        l.last.bits.toNat + l'.here.bits.toNat ≤ l'.bits.toNat ∧ Ext l l' ∧ Pulled2 ca off l.last l l') ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) ∧
      backMeasure pr h' l' log' ≤ backMeasure pr h l log := by
  have subIdx : ∀ hold : Nat, hold % 2 ^ (l.last.bits.toNat + l.last.op.toNat) / 2 ^ l.last.bits.toNat <
      2 ^ l.last.op.toNat := fun hold => ZlibF.Math.InflateLookup.slice_lt _ _ _
  have subBits : ∀ hold : Nat, l.last.bits.toNat + (subVal ca off l.last hold).bits.toNat ≤ 15 :=
    fun hold => sub15 _ (subIdx hold)
  let start := backMeasure pr h l log
  let Inv : IL → Heap → Prop := fun l1 h1 => ∃ log1, PInv c pr h0 h1 l1 log1 ∧ h1.istates i = h.istates i ∧
    l1.put = l.put ∧ l1.left = l.left ∧ l1.last = l.last ∧ backMeasure pr h1 l1 log1 ≤ start ∧ Ext l l1 ∧
    Pulled2 ca off l.last l l1
  let Q : Except Ex Unit → IL → Heap → Prop := fun res l1 h1 => ∃ log1, PInv c pr h0 h1 l1 log1 ∧
    h1.istates i = h.istates i ∧
    (res = .ok () → l1.put = l.put ∧ l1.left = l.left ∧ l1.last = l.last ∧
      l1.here = subVal ca off l.last l1.hold.toNat ∧
      l.last.bits.toNat + l1.here.bits.toNat ≤ l1.bits.toNat ∧ Ext l l1 ∧ Pulled2 ca off l.last l l1) ∧
    (∀ e, res = .error e → e = Ex.leave ∧ l1.ret = Z_BUF_ERROR) ∧ backMeasure pr h1 l1 log1 ≤ start
  have loop := xwhileBrk_wf (cond := pure true) (body := lk2Body c dist) Inv Q (fun l1 _ => 64 - l1.bits.toNat)
    (by
      intro l1 h1 ⟨log1, I1, ist1, put1, left1, last1, meas1, ext1, pull1⟩
      have hs1 : h1.istates i = some s := ist1.trans hs
      have get1 : Space.get h1 ref = some ca := (refOk.get_eq ist1 (I.static_eq I1)).trans get
      refine ⟨l1, h1, true, rfl, fun _ => ?_, fun x => (nomatch x)⟩
      have run := lk2Body_run c dist l1 I1.cst hs1 tab get1 (by rw [last1]; exact link)
      have sb : l1.last.bits.toNat + (subVal ca off l1.last l1.hold.toNat).bits.toNat ≤ 15 := by
        rw [last1]; exact subBits _
      have addNat : (l1.last.bits.toUInt32 + (subVal ca off l1.last l1.hold.toNat).bits.toUInt32).toNat =
          l1.last.bits.toNat + (subVal ca off l1.last l1.hold.toNat).bits.toNat := by
        rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32]; omega
      by_cases fit : l1.last.bits.toUInt32 + (subVal ca off l1.last l1.hold.toNat).bits.toUInt32 ≤ l1.bits
      · rw [if_pos fit] at run
        refine ⟨.ok true, _, h1, run, log1, I1.withHere _, ist1,
          fun _ => ⟨put1, left1, last1, by show _ = subVal ca off l.last l1.hold.toNat; rw [last1], ?_, ext1, pull1⟩,
          fun e x => (nomatch x), meas1⟩
        have := UInt32.le_iff_toNat_le.mp fit
        rw [addNat] at this
        rw [← last1]
        exact this
      · rw [if_neg fit] at run
        have fit1 : l1.bits.toNat < l1.last.bits.toNat + (subVal ca off l1.last l1.hold.toNat).bits.toNat := by
          have := mt UInt32.le_iff_toNat_le.mpr fit
          rw [addNat] at this
          omega
        have fit' : l1.bits.toNat < l.last.bits.toNat + (subVal ca off l.last l1.hold.toNat).bits.toNat := by
          rw [← last1]; exact fit1
        have I1' := I1.withHere (subVal ca off l1.last l1.hold.toNat)
        obtain ⟨res2, l2, h2, log2, run2, I2, okc, errc, ist2, meas2⟩ :=
          PULLBYTE_p c pr I1' (by show l1.bits.toNat ≤ 31; omega)
        have meas2' : backMeasure pr h2 l2 log2 ≤ start := by
          have : backMeasure pr h1 { l1 with here := subVal ca off l1.last l1.hold.toNat } log1 =
            backMeasure pr h1 l1 log1 := rfl
          omega
        cases res2 with
        | error e =>
          refine ⟨.error e, l2, h2, ?_, log2, I2, ist2.trans ist1, fun x => (nomatch x), errc, meas2'⟩
          rw [run, runX_bind, run2]
        | ok u =>
          cases u
          obtain ⟨bits2, put2, left2, hold2, last2⟩ := okc rfl
          have hold2' : l2.hold.toNat % 2 ^ l1.bits.toNat = l1.hold.toNat := hold2
          have bits2' : l2.bits.toNat = l1.bits.toNat + 8 := bits2
          have hl1 : l1.hold.toNat < 2 ^ l1.bits.toNat := I1.bits.2
          have ext2 : Ext l l2 := by
            obtain ⟨e1, e2⟩ := ext1
            refine ⟨by omega, ?_⟩
            rw [← e2, ← hold2', Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 e1)]
          have pull2 : Pulled2 ca off l.last l l2 :=
            Or.inr ⟨l1.bits.toNat, l1.hold.toNat, ext1.1, hl1, fit', bits2', hold2'⟩
          refine ⟨.ok false, l2, h2, ?_, ⟨log2, I2, ist2.trans ist1, put2.trans put1, left2.trans left1,
            last2.trans last1, meas2', ext2, pull2⟩, ?_⟩
          · rw [run, runX_bind, run2]; rfl
          · show 64 - l2.bits.toNat < 64 - l1.bits.toNat
            have := I1.bits.1
            omega)
    ⟨log, I, rfl, rfl, rfl, rfl, Nat.le_refl _, ⟨Nat.le_refl _, Nat.mod_eq_of_lt I.bits.2⟩, Or.inl ⟨rfl, rfl⟩⟩
    (by unfold fuel; omega)
  obtain ⟨res, l', h', run, log', I', ist, okc, errc, meas⟩ := loop
  exact ⟨res, l', h', log', by rw [lookup2_eq]; exact run, I', ist, okc, errc, meas⟩

end Zlib.Infback.Safety
