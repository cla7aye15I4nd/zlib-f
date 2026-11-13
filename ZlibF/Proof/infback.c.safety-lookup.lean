import ZlibF.Proof.«infback.c.safety-stored»

/-!
# infback.c: the root table lookup on the loop invariant

`lookup1_p`: `for (;;) { here = TABLE[BITS(nb)]; if (here.bits <= bits) break; PULLBYTE(); }`
with a table that is the state's own `codes` array or a static table, whose root has `2^nb`
entries inside the array, `nb ≤ 15`, and whose root entries need at most 15 bits. The table
survives `PULLBYTE()`: the call-back keeps the state record and the static tables. The result
is a root entry of the table, with its bits held.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
set_option autoImplicit false

/-- `PInv` fixes the static tables: every heap it holds of has those of the call. -/
theorem PInv.static_eq {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h h' : Heap} {l l' : IL} {log log' : BackLog} (I : PInv c pr h0 h l log) (I' : PInv c pr h0 h' l' log') :
    h'.static = h.static :=
  I'.frame.1.1.symm.trans I.frame.1.1

/-- A table the decoder reads: the state's own `codes`, or a static table. -/
def TabRef (i : Nat) (ref : CodeRef) : Prop := ref = .istate_codes i ∨ ref = .st_lenfix ∨ ref = .st_distfix

theorem TabRef.get_eq {i : Nat} {ref : CodeRef} (ok : TabRef i ref) {h h' : Heap}
    (ist : h'.istates i = h.istates i) (st : h'.static = h.static) :
    (Space.get h' ref : Option (Array Code)) = Space.get h ref := by
  rcases ok with rfl | rfl | rfl
  · show (h'.istates i).map (·.codes) = (h.istates i).map (·.codes)
    rw [ist]
  · show some h'.static.lenfix = some h.static.lenfix
    rw [st]
  · show some h'.static.distfix = some h.static.distfix
    rw [st]

/-- The body of the lookup loop. -/
def lkBody (c : BCtx) (dist : Bool) : X Bool := do
  let s ← ldInflateState c.st
  let tab := if dist then s.distcode else s.lencode
  let nb := if dist then s.distbits else s.lenbits
  let b ← BITS nb
  let here ← Ptr.index tab (b.toNat : Int)
  modify fun l => { l with here := here }
  if here.bits.toUInt32 <= (← get).bits then return true
  Zlib.Infback.PULLBYTE c
  return false

theorem lookup1_eq (c : BCtx) (dist : Bool) : Zlib.Infback.lookup1 c dist = xloopBrk (lkBody c dist) := rfl

/-- One trip of the lookup loop: the root entry selected by the held bits. -/
theorem lkBody_run (c : BCtx) {i : Nat} (dist : Bool) {h : Heap} {s : InflateState} (l : IL)
    (hc : c.st = some (.tab i)) (hs : h.istates i = some s) {ref : CodeRef} {off : Nat} {ca : Array Code}
    {nb : UInt32} (tab : (if dist then s.distcode else s.lencode) = .ref ref off)
    (hnb : (if dist then s.distbits else s.lenbits) = nb) (get : Space.get h ref = some ca)
    (root : nb.toNat ≤ 15) (size : off + 2 ^ nb.toNat ≤ ca.size) :
    runX (lkBody c dist) l h =
      if (ca.getD (off + l.hold.toNat % 2 ^ nb.toNat) default).bits.toUInt32 ≤ l.bits then
        .ok ((.ok true, { l with here := ca.getD (off + l.hold.toNat % 2 ^ nb.toNat) default }), h)
      else runX (do Zlib.Infback.PULLBYTE c; pure false : X Bool)
        { l with here := ca.getD (off + l.hold.toNat % 2 ^ nb.toNat) default } h := by
  have root' : nb.toNat < 32 := by omega
  let mask := l.hold.toUInt32 &&& ((1 : UInt32) <<< nb - 1)
  have value : mask.toNat = l.hold.toNat % 2 ^ nb.toNat := BITS_toNat l nb root'
  have inside : off + mask.toNat < ca.size := by
    have := Nat.mod_lt l.hold.toNat (Nat.two_pow_pos nb.toNat)
    omega
  have read := Ptr.index_ok (off := off) (i := mask.toNat) get inside
  have actual : ca[off + mask.toNat] = ca.getD (off + l.hold.toNat % 2 ^ nb.toNat) default := by
    rw [← value, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
  dsimp only [mask] at read actual
  unfold lkBody
  rw [hc]
  have load : ldInflateState (some (.tab i)) h = .ok (s, h) := ldInflateState_tab hs
  simp only [runX_bind, runX_lift_ok load, tab, hnb, BITS_run l h nb root', runX_modify, runX_get,
    runX_lift_ok read, actual]
  by_cases fit : (ca.getD (off + l.hold.toNat % 2 ^ nb.toNat) default).bits.toUInt32 ≤ l.bits
  all_goals simp only [fit, ite_true, ite_false, runX_bind, runX_pure]

/-- `PInv` does not read `here`. -/
theorem PInv.withHere {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) (v : Code) :
    PInv c pr h0 h { l with here := v } log :=
  ⟨I.cstrm, I.cst, I.valid, I.winRoot, I.put, I.chunk, I.held, I.bits, I.proto, I.frame, I.live, I.mode,
    I.platform, I.fit, I.chunkBlk⟩

/-- What the lookup loop did with the bits: none were pulled, or the last byte was pulled when
`bp` bits `hp` were held and the entry they selected needed more than `bp` bits. -/
def Pulled (ca : Array Code) (off nb : Nat) (l l' : IL) : Prop :=
  (l'.bits = l.bits ∧ l'.hold = l.hold) ∨
  ∃ bp hp, l.bits.toNat ≤ bp ∧ hp < 2 ^ bp ∧ bp < (ca.getD (off + hp % 2 ^ nb) default).bits.toNat ∧
    l'.bits.toNat = bp + 8 ∧ l'.hold.toNat % 2 ^ bp = hp

/-- The registers `l'` extend the bits of `l`. -/
def Ext (l l' : IL) : Prop := l.bits.toNat ≤ l'.bits.toNat ∧ l'.hold.toNat % 2 ^ l.bits.toNat = l.hold.toNat

/-- **The root lookup on the invariant.** It ends with the root entry the held bits select, whose
bits are held, or with `Z_BUF_ERROR` from `in`. The state record does not change. -/
theorem lookup1_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (dist : Bool) {h0 h : Heap} {l : IL} {log : BackLog}
    (I : PInv c pr h0 h l log) {s : InflateState} (hs : h.istates i = some s) {ref : CodeRef} {off : Nat}
    {ca : Array Code} {nb : UInt32} (tab : (if dist then s.distcode else s.lencode) = .ref ref off)
    (hnb : (if dist then s.distbits else s.lenbits) = nb) (refOk : TabRef i ref)
    (get : Space.get h ref = some ca) (root : nb.toNat ≤ 15) (size : off + 2 ^ nb.toNat ≤ ca.size)
    (entries : ∀ j, j < 2 ^ nb.toNat → (ca.getD (off + j) default).bits.toNat ≤ 15) :
    ∃ res l' h' log', runX (Zlib.Infback.lookup1 c dist) l h = .ok ((res, l'), h') ∧
      PInv c pr h0 h' l' log' ∧ h'.istates i = h.istates i ∧
      (res = .ok () → l'.put = l.put ∧ l'.left = l.left ∧
        l'.here = ca.getD (off + l'.hold.toNat % 2 ^ nb.toNat) default ∧
        l'.here.bits.toNat ≤ l'.bits.toNat ∧ Ext l l' ∧ Pulled ca off nb.toNat l l') ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) ∧
      backMeasure pr h' l' log' ≤ backMeasure pr h l log := by
  let start := backMeasure pr h l log
  let Inv : IL → Heap → Prop := fun l1 h1 => ∃ log1, PInv c pr h0 h1 l1 log1 ∧ h1.istates i = h.istates i ∧
    l1.put = l.put ∧ l1.left = l.left ∧ backMeasure pr h1 l1 log1 ≤ start ∧ Ext l l1 ∧ Pulled ca off nb.toNat l l1
  let Q : Except Ex Unit → IL → Heap → Prop := fun res l1 h1 => ∃ log1, PInv c pr h0 h1 l1 log1 ∧
    h1.istates i = h.istates i ∧
    (res = .ok () → l1.put = l.put ∧ l1.left = l.left ∧
      l1.here = ca.getD (off + l1.hold.toNat % 2 ^ nb.toNat) default ∧
      l1.here.bits.toNat ≤ l1.bits.toNat ∧ Ext l l1 ∧ Pulled ca off nb.toNat l l1) ∧
    (∀ e, res = .error e → e = Ex.leave ∧ l1.ret = Z_BUF_ERROR) ∧ backMeasure pr h1 l1 log1 ≤ start
  have loop := xwhileBrk_wf (cond := pure true) (body := lkBody c dist) Inv Q (fun l1 _ => 64 - l1.bits.toNat)
    (by
      intro l1 h1 ⟨log1, I1, ist1, put1, left1, meas1, ext1, pull1⟩
      have hs1 : h1.istates i = some s := ist1.trans hs
      have get1 : Space.get h1 ref = some ca := (refOk.get_eq ist1 (I.static_eq I1)).trans get
      refine ⟨l1, h1, true, rfl, fun _ => ?_, fun x => (nomatch x)⟩
      have run := lkBody_run c dist l1 I1.cst hs1 tab hnb get1 root size
      have jlt := Nat.mod_lt l1.hold.toNat (Nat.two_pow_pos nb.toNat)
      have entry := entries _ jlt
      by_cases fit : (ca.getD (off + l1.hold.toNat % 2 ^ nb.toNat) default).bits.toUInt32 ≤ l1.bits
      · rw [if_pos fit] at run
        refine ⟨.ok true, _, h1, run, log1, I1.withHere _, ist1, fun _ => ⟨put1, left1, rfl, ?_, ext1, pull1⟩,
          fun e x => (nomatch x), meas1⟩
        have := UInt32.le_iff_toNat_le.mp fit
        simpa using this
      · rw [if_neg fit] at run
        have fit' : l1.bits.toNat < (ca.getD (off + l1.hold.toNat % 2 ^ nb.toNat) default).bits.toNat := by
          have := mt UInt32.le_iff_toNat_le.mpr fit
          simp only [UInt8.toNat_toUInt32] at this
          omega
        have I1' := I1.withHere (ca.getD (off + l1.hold.toNat % 2 ^ nb.toNat) default)
        obtain ⟨res2, l2, h2, log2, run2, I2, okc, errc, ist2, meas2⟩ :=
          PULLBYTE_p c pr I1' (by show l1.bits.toNat ≤ 31; omega)
        have meas2' : backMeasure pr h2 l2 log2 ≤ start := by
          have : backMeasure pr h1 { l1 with here := ca.getD (off + l1.hold.toNat % 2 ^ nb.toNat) default } log1 =
            backMeasure pr h1 l1 log1 := rfl
          omega
        cases res2 with
        | error e =>
          refine ⟨.error e, l2, h2, ?_, log2, I2, ist2.trans ist1, fun x => (nomatch x), errc, meas2'⟩
          rw [run, runX_bind, run2]
        | ok u =>
          cases u
          obtain ⟨bits2, put2, left2, hold2, -⟩ := okc rfl
          have hold2' : l2.hold.toNat % 2 ^ l1.bits.toNat = l1.hold.toNat := hold2
          have bits2' : l2.bits.toNat = l1.bits.toNat + 8 := bits2
          have hl1 : l1.hold.toNat < 2 ^ l1.bits.toNat := I1.bits.2
          have ext2 : Ext l l2 := by
            obtain ⟨e1, e2⟩ := ext1
            refine ⟨by omega, ?_⟩
            rw [← e2, ← hold2', Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 e1)]
          have pull2 : Pulled ca off nb.toNat l l2 :=
            Or.inr ⟨l1.bits.toNat, l1.hold.toNat, ext1.1, hl1, fit', bits2', hold2'⟩
          refine ⟨.ok false, l2, h2, ?_, ⟨log2, I2, ist2.trans ist1, put2.trans put1, left2.trans left1, meas2',
            ext2, pull2⟩, ?_⟩
          · rw [run, runX_bind, run2]; rfl
          · show 64 - l2.bits.toNat < 64 - l1.bits.toNat
            have := I1.bits.1
            omega)
    ⟨log, I, rfl, rfl, rfl, Nat.le_refl _, ⟨Nat.le_refl _, Nat.mod_eq_of_lt I.bits.2⟩, Or.inl ⟨rfl, rfl⟩⟩
    (by unfold fuel; omega)
  obtain ⟨res, l', h', run, log', I', ist, okc, errc, meas⟩ := loop
  exact ⟨res, l', h', log', run, I', ist, okc, errc, meas⟩

end Zlib.Infback.Safety
