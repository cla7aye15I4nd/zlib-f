import ZlibF.Proof.«infback.c.safety-copy»

/-!
# infback.c: `case LEN` without the fast path, on the loop invariant

The literal/length table and the distance table of the block are the state's own arrays or the
static fixed tables (`TablesOk`); `lenTab` and `distTab` give what `symLook_p` needs of either.
`distSym_p`: the distance symbol, its extra bits, then the match copy (`lenCopy_p`).
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
open Zlib.Inftrees.Spec.DecodeTableStability (StableQuery)
open Zlib.Inftrees.Proofs (PrefixQuery)
open Zlib.Inffast.Spec (TableSafe LenLeaf DistLeaf LenLink DistLink LenTableSafe DistTableSafe)
set_option autoImplicit false

/-- The literal/length table of a `LEN` state: what `symLook_p` needs. -/
theorem lenTab {h : Heap} {i : Nat} {s : InflateState} (hs : h.istates i = some s) (tabs : TablesOk i s)
    (globals : LibraryGlobals h) :
    ∃ ref off ca used lens, s.lencode = .ref ref off ∧ TabRef i ref ∧ Space.get h ref = some ca ∧
      LenTableSafe ca off s.lenbits.toNat ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca off s.lenbits.toNat used lens ∧
      StableQuery LENS ca off s.lenbits.toNat ∧ PrefixQuery LENS ca off s.lenbits.toNat := by
  rcases tabs.1 with ⟨ol, lc, safe, -, stable, pfx, used, lens, inv⟩ | ⟨lc, lb⟩
  · exact ⟨.istate_codes i, ol, s.codes, used, lens, lc, Or.inl rfl, CodeRef.get_istate_codes hs, safe, inv,
      stable, pfx⟩
  · have get : Space.get h CodeRef.st_lenfix = some Zlib.InffixedH.lenfix := by
      change some h.static.lenfix = some Zlib.InffixedH.lenfix
      rw [globals]
      rfl
    refine ⟨.st_lenfix, 0, Zlib.InffixedH.lenfix, 512, ZlibF.Spec.fixedLitLens, lc, Or.inr (Or.inl rfl),
      get, ?_, ?_, ?_, ?_⟩
    all_goals rw [lb]
    · exact Zlib.Inffast.Proofs.lenfix_tableSafe
    · exact Zlib.Inflate.Proofs.MeaningFixed.lenfix_inv
    · exact Zlib.Inflate.Proofs.MeaningFixed.lenfix_stable
    · exact Zlib.Inflate.Proofs.MeaningFixed.lenfix_prefix

/-- The distance table of a `LEN` state: what `symLook_p` needs. -/
theorem distTab {h : Heap} {i : Nat} {s : InflateState} (hs : h.istates i = some s) (tabs : TablesOk i s)
    (globals : LibraryGlobals h) :
    ∃ ref off ca used lens, s.distcode = .ref ref off ∧ TabRef i ref ∧ Space.get h ref = some ca ∧
      DistTableSafe ca off s.distbits.toNat ∧
      Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca off s.distbits.toNat used lens ∧
      StableQuery DISTS ca off s.distbits.toNat ∧ PrefixQuery DISTS ca off s.distbits.toNat := by
  rcases tabs.2 with ⟨od, dc, safe, stable, pfx, used, lens, inv⟩ | ⟨dc, db⟩
  · exact ⟨.istate_codes i, od, s.codes, used, lens, dc, Or.inl rfl, CodeRef.get_istate_codes hs, safe, inv,
      stable, pfx⟩
  · have get : Space.get h CodeRef.st_distfix = some Zlib.InffixedH.distfix := by
      change some h.static.distfix = some Zlib.InffixedH.distfix
      rw [globals]
      rfl
    refine ⟨.st_distfix, 0, Zlib.InffixedH.distfix, 32, ZlibF.Spec.fixedDistLens, dc,
      Or.inr (Or.inr rfl), get, ?_, ?_, ?_, ?_⟩
    all_goals rw [db]
    · exact Zlib.Inffast.Proofs.distfix_tableSafe
    · exact Zlib.Inflate.Proofs.MeaningFixed.distfix_inv
    · exact Zlib.Inflate.Proofs.MeaningFixed.distfix_stable
    · exact Zlib.Inflate.Proofs.MeaningFixed.distfix_prefix

theorem lit_dist_code : "invalid distance code" ∈ strTable := by decide +kernel
theorem lit_len_code : "invalid literal/length code" ∈ strTable := by decide +kernel

/-- `DROPBITS(k)` on the invariant: the registers `l1` with `k` bits fewer. -/
theorem drop_p {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) (k : UInt32) (hk : k.toNat ≤ l.bits.toNat)
    {l1 : IL} (hl1 : l1 = dropR l k) :
    (∀ hh, runX (DROPBITS k) l hh = .ok ((.ok (), l1), hh)) ∧ PInv c pr h0 h l1 log ∧
      l1.bits.toNat = l.bits.toNat - k.toNat ∧ baseM pr l1 log + 4 * k.toNat = baseM pr l log ∧
      l1.have_ = l.have_ := by
  have k64 : k.toNat < 64 := by have := I.bits.1; omega
  obtain ⟨B0, -, hbit⟩ := DROPBITS_inv (bitInv_of I) k hk k64
  have B1 : Zlib.Inflate.Proofs.BitInv h l1 (log.held.drop (log.held.length - l.have_.toNat)) := by
    rw [hl1]; exact B0
  have e1 : l1.bits.toNat = l.bits.toNat - k.toNat := by rw [hl1]; exact hbit
  refine ⟨fun hh => by rw [DROPBITS_run _ _ _ k64, hl1]; rfl, ?_, e1, ?_, by rw [hl1]; rfl⟩
  · exact I.regs (l' := l1) (by rw [hl1]; rfl) (by rw [hl1]; rfl) (by rw [hl1]; rfl) (by rw [hl1]; rfl)
      (by rw [e1]; have := I.bits.1; omega) B1.hold_lt
  · unfold baseM
    rw [e1, show l1.have_ = l.have_ by rw [hl1]; rfl]
    omega

set_option maxRecDepth 100000 in
/-- **The distance symbol on the invariant**: `DROPBITS(here.bits)`, an invalid code (`BAD`), or
the distance and its extra bits (at most 13), then the match copy. -/
theorem distSym_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) {s : InflateState} (hs : h.istates i = some s)
    (mode : s.mode = LEN) (len1 : 1 ≤ s.length.toNat) {d : Nat} (leaf : DistLeaf d l.here)
    (fit : l.here.bits.toNat ≤ l.bits.toNat) (short : l.bits.toNat - l.here.bits.toNat < 8) {B : Nat}
    (lt : baseM pr l log + 2 < B) :
    ∃ res l' h', runX (distSym c) l h = .ok ((res, l'), h') ∧ TRound c pr h0 B res l' h' := by
  obtain ⟨z, s0, valid, -, -⟩ := I.valid
  have e0 : s0 = s := Option.some.inj (valid.2.1.symm.trans hs)
  subst e0
  have wf := valid.2.2.2.2.2.1
  have hbN : l.here.bits.toUInt32.toNat = l.here.bits.toNat := UInt8.toNat_toUInt32 _
  obtain ⟨l1, hl1⟩ : ∃ l1 : IL, l1 = dropR l l.here.bits.toUInt32 := ⟨_, rfl⟩
  obtain ⟨hd1, I1, e1, m1, -⟩ := drop_p I l.here.bits.toUInt32 (by rw [hbN]; exact fit) hl1
  rw [hbN] at e1 m1
  have pre1 : runX (distSym c) l h = runX (do
      if (l.here.op &&& 64) != 0 then
        badMode c "invalid distance code"
        return
      wrS c.st fun s => { s with offset := l.here.val.toUInt32, extra := l.here.op.toUInt32 &&& 15 }
      let ex := l.here.op.toUInt32 &&& 15
      if ex != 0 then
        NEEDBITS c ex
        let b ← BITS ex
        wrS c.st fun s => { s with offset := s.offset + b }
        DROPBITS ex
      lenCopy c) l1 h := by
    unfold distSym
    simp only [runX_bind, runX_get, hd1]
  by_cases bad : ((l.here.op &&& 64) != 0) = true
  · obtain ⟨hb, runB, T⟩ := TRound.bad I1 "invalid distance code" lit_dist_code (B := B) (by omega)
    refine ⟨.ok (), l1, hb, ?_, T⟩
    rw [pre1]
    simp only [bad, ↓reduceIte, runX_bind, runX_lift_ok runB]
    rfl
  · have bad' : ((l.here.op &&& 64) != 0) = false := by simpa using bad
    have op64 : l.here.op &&& 64 = 0 := by simpa using bad
    have ex13 : (l.here.op &&& 15).toNat ≤ 13 := by
      rcases leaf.2 with ⟨-, e13, -⟩ | ⟨-, b64⟩
      · exact e13
      · exact absurd op64 b64
    have exN : (l.here.op.toUInt32 &&& 15).toNat = (l.here.op &&& 15).toNat := Zlib.Inffast.Proofs.mask15 _
    let S2 : InflateState := { s0 with offset := l.here.val.toUInt32, extra := l.here.op.toUInt32 &&& 15 }
    have hs2 : (setI h i S2).istates i = some S2 := by simp [setI]
    have wr2 : wrS c.st (fun s => { s with offset := l.here.val.toUInt32, extra := l.here.op.toUInt32 &&& 15 }) h =
        .ok ((), setI h i S2) := wrS_ok I.cst hs _
    have I2 := I1.setState hs S2 rfl rfl rfl (wf_with wf _ rfl rfl rfl) (I.mode s0 hs)
    have pre2 : runX (distSym c) l h = runX (do
        if (l.here.op.toUInt32 &&& 15) != 0 then
          NEEDBITS c (l.here.op.toUInt32 &&& 15)
          let b ← BITS (l.here.op.toUInt32 &&& 15)
          wrS c.st fun s => { s with offset := s.offset + b }
          DROPBITS (l.here.op.toUInt32 &&& 15)
        lenCopy c) l1 (setI h i S2) := by
      rw [pre1]
      simp only [bad', Bool.false_eq_true, ↓reduceIte, runX_bind, runX_lift_ok wr2]
    by_cases hex : ((l.here.op.toUInt32 &&& 15) != 0) = true
    · obtain ⟨res3, l3, h3, log3, run3, I3, ok3, err3, ist3, meas3⟩ :=
        NEEDBITS_p c pr (l.here.op.toUInt32 &&& 15) (by rw [exN]; omega) I2
      have hs3 : h3.istates i = some S2 := ist3.trans hs2
      cases res3 with
      | error e =>
        obtain ⟨rfl, ret⟩ := err3 e rfl
        refine ⟨.error Ex.leave, l3, h3, ?_, TRound.leave I3 B ret⟩
        rw [pre2]
        simp only [hex, ↓reduceIte, runX_bind, run3]
      | ok u =>
        cases u
        obtain ⟨k3, -, -, mx3⟩ := ok3 rfl
        have b3 := baseM_le meas3
        obtain ⟨bv, hbv⟩ : ∃ bv : UInt32, bv = bitsV l3 (l.here.op.toUInt32 &&& 15) := ⟨_, rfl⟩
        have rb : runX (BITS (l.here.op.toUInt32 &&& 15)) l3 h3 = .ok ((.ok bv, l3), h3) := by
          rw [BITS_run _ _ _ (by rw [exN]; omega), hbv]; rfl
        let S4 : InflateState := { S2 with offset := S2.offset + bv }
        have hs4 : (setI h3 i S4).istates i = some S4 := by simp [setI]
        have wr4 : wrS c.st (fun s => { s with offset := s.offset + bv }) h3 = .ok ((), setI h3 i S4) :=
          wrS_ok I3.cst hs3 _
        have I4 := I3.setState hs3 S4 rfl rfl rfl (wf_with wf _ rfl rfl rfl) (I.mode s0 hs)
        obtain ⟨l5, hl5⟩ : ∃ l5 : IL, l5 = dropR l3 (l.here.op.toUInt32 &&& 15) := ⟨_, rfl⟩
        obtain ⟨hd5, I5, e5, m5, -⟩ := drop_p I4 (l.here.op.toUInt32 &&& 15) k3 hl5
        have short5 : l5.bits.toNat < 8 := by
          rw [e5]
          have m : l3.bits.toNat ≤ max l1.bits.toNat ((l.here.op.toUInt32 &&& 15).toNat + 7) := mx3
          have : l3.bits.toNat ≤ (l.here.op.toUInt32 &&& 15).toNat + 7 :=
            Nat.le_trans m (Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩)
          omega
        obtain ⟨res6, l6, h6, run6, T6⟩ :=
          lenCopy_p c pr I5 hw hs4 mode len1 short5 (B := B) (by omega)
        refine ⟨res6, l6, h6, ?_, T6⟩
        rw [pre2]
        simp only [hex, ↓reduceIte, runX_bind, run3, rb, runX_lift_ok wr4, hd5]
        exact run6
    · have hex' : ((l.here.op.toUInt32 &&& 15) != 0) = false := by simpa using hex
      obtain ⟨res6, l6, h6, run6, T6⟩ :=
        lenCopy_p c pr I2 hw hs2 mode len1 (by omega) (B := B) (by omega)
      refine ⟨res6, l6, h6, ?_, T6⟩
      rw [pre2]
      simp only [hex', Bool.false_eq_true, ↓reduceIte, runX_bind, runX_pure]
      exact run6

/-- **The distance lookup and the rest of `case LEN` on the invariant.** -/
theorem lenDist_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) {s : InflateState} (hs : h.istates i = some s)
    (mode : s.mode = LEN) (tabs : TablesOk i s) (len1 : 1 ≤ s.length.toNat) (short : l.bits.toNat < 8)
    {B : Nat} (lt : baseM pr l log + 2 < B) :
    ∃ res l' h', runX (lenDist c) l h = .ok ((res, l'), h') ∧ TRound c pr h0 B res l' h' := by
  obtain ⟨z, s0, valid, -, -⟩ := I.valid
  have e0 : s0 = s := Option.some.inj (valid.2.1.symm.trans hs)
  subst e0
  have globals := valid.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨ref, off, ca, used, lens, dc, refOk, get, safe, inv, stable, pfx⟩ := distTab hs tabs globals
  rw [lenDist_eq]
  rcases symLook_p c pr true distIsLink (distSym c) I hs (type := DISTS) dc rfl refOk get safe
      (fun _ _ x => x.1) distIsLink_eq (fun e x => distLink_of_code e.op x)
      (fun e _ x => code_of_distLink e.op x) inv stable pfx short with
    ⟨l2, h2, log2, run2, I2, ret⟩ | ⟨l2, h2, log2, d, run2, I2, ist2, -, -, leaf, -, fit, short2, b2⟩
  · exact ⟨.error Ex.leave, l2, h2, run2, TRound.leave I2 B ret⟩
  · obtain ⟨res3, l3, h3, run3, T3⟩ :=
      distSym_p c pr I2 hw (ist2.trans hs) mode len1 leaf fit short2 (B := B) (by omega)
    exact ⟨res3, l3, h3, by rw [run2]; exact run3, T3⟩

theorem modeOk_ty (i : Nat) (s : InflateState) : ModeOk i { s with mode := TYPE } :=
  ⟨Or.inl rfl, fun e => absurd (e : TYPE = LEN) (by show TYPE ≠ LEN; decide)⟩

set_option maxRecDepth 100000 in
/-- **The literal/length symbol on the invariant**: a literal goes to the window through `ROOM()`
(the mode stays `LEN`); the end of the block gives `TYPE`; an invalid code `BAD`; a length takes
its extra bits (at most 5) and the distance follows. -/
theorem lenSym_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) {s : InflateState} (hs : h.istates i = some s)
    (mode : s.mode = LEN) (tabs : TablesOk i s) {d : Nat} (leaf : LenLeaf d l.here)
    (pos : 1 ≤ d + l.here.bits.toNat) (fit : l.here.bits.toNat ≤ l.bits.toNat)
    (short : l.bits.toNat - l.here.bits.toNat < 8) {B : Nat} (lt : baseM pr l log + 4 * d + 2 ≤ B) :
    ∃ res l' h', runX (lenSym c) l h = .ok ((res, l'), h') ∧ TRound c pr h0 B res l' h' := by
  obtain ⟨z, s0, valid, win, sz⟩ := I.valid
  have e0 : s0 = s := Option.some.inj (valid.2.1.symm.trans hs)
  subst e0
  have wf := valid.2.2.2.2.2.1
  have hbN : l.here.bits.toUInt32.toNat = l.here.bits.toNat := UInt8.toNat_toUInt32 _
  obtain ⟨l1, hl1⟩ : ∃ l1 : IL, l1 = dropR l l.here.bits.toUInt32 := ⟨_, rfl⟩
  obtain ⟨hd1, I1, e1, m1, -⟩ := drop_p I l.here.bits.toUInt32 (by rw [hbN]; exact fit) hl1
  rw [hbN] at e1 m1
  have lt1 : baseM pr l1 log + 2 < B := by omega
  let S2 : InflateState := { s0 with length := l.here.val.toUInt32 }
  have hs2 : (setI h i S2).istates i = some S2 := by simp [setI]
  have wr2 : wrS c.st (fun s => { s with length := l.here.val.toUInt32 }) h = .ok ((), setI h i S2) :=
    wrS_ok I.cst hs _
  have I2 := I1.setState hs S2 rfl rfl rfl (wf_with wf _ rfl rfl rfl) (I.mode s0 hs)
  have short1 : l1.bits.toNat < 8 := by omega
  by_cases lit : (l.here.op == 0) = true
  · -- a literal
    obtain ⟨res3, l3, h3, log3, run3, I3, ok3, err3, have3, next3, bits3, hold3, -, -, st3, meas3⟩ :=
      ROOM_p c pr I2
    have b3 := baseM_le meas3
    cases res3 with
    | error e =>
      obtain ⟨rfl, ret⟩ := err3 e rfl
      refine ⟨.error Ex.leave, l3, h3, ?_, TRound.leave I3 B ret⟩
      unfold lenSym
      simp only [runX_bind, runX_get, hd1, runX_lift_ok wr2, lit, ↓reduceIte, run3]
    | ok u =>
      cases u
      have left3 := ok3 rfl
      obtain ⟨wv, hs3⟩ := st3 S2 hs2
      obtain ⟨z3, S3', valid3, win3, sz3⟩ := I3.valid
      have eS : S3' = { S2 with whave := wv } := Option.some.inj (valid3.2.1.symm.trans hs3)
      subst eS
      have wr := valid3.2.2.2.2.2.2.2.2.2.2.1
      rw [win3, sz3, hw] at wr
      obtain ⟨a3, get3, ro3, room3⟩ : ∃ a, h3.bytes w = some a ∧ h3.ro w = false ∧ woff + n ≤ a.size := by
        rcases wr with ⟨null, -⟩ | ⟨ref, o, a0, ptr, g, ro, rm⟩
        · cases null
        · injection ptr with e1 e2; subst e1 e2; exact ⟨a0, g, ro, rm⟩
      obtain ⟨pput, lle⟩ := I3.put
      have hput : l3.put = .ref (.blk w) (woff + (n - l3.left.toNat)) := by rw [pput, hw]; rfl
      have lpos : 1 ≤ l3.left.toNat := Nat.pos_of_ne_zero (fun e => left3 (UInt32.toNat_inj.mp (by rw [e]; rfl)))
      let idx := woff + (n - l3.left.toNat)
      have ld3 : ldInflateState c.st h3 = .ok ({ S2 with whave := wv }, h3) := by
        rw [I3.cst]; exact ldInflateState_tab hs3
      have st : store8 l3.put S2.length.toUInt8 h3 = .ok ((), winHeap h3 w (a3.set! idx S2.length.toUInt8)) := by
        rw [hput]
        exact Ptr.store_ok (r := BRef.blk w) (show (Space.get h3 (BRef.blk w) : Option (Array UInt8)) = some a3 from get3)
          (show Space.ro h3 (BRef.blk w) = false from ro3) (by omega)
      have getW : (Space.get (winHeap h3 w (a3.set! idx S2.length.toUInt8)) (BRef.blk w) : Option (Array UInt8)) =
          some (a3.set! idx S2.length.toUInt8) := by simp [Space.get, winHeap]
      have add : OkOn (winHeap h3 w (a3.set! idx S2.length.toUInt8)) (Ptr.add l3.put 1) (Ptr.ref (BRef.blk w) (idx + 1)) := by
        rw [hput]; exact Ptr.add_nat_ok (n := 1) getW (by simp; omega)
      have I4 := I3.storeWindow hw get3 (by simp) (a' := a3.set! idx S2.length.toUInt8)
        (fun j out => Zlib.Inflate.Proofs.array_set!_getElem?_ne _ (by omega) _)
      have subL : (l3.left - 1).toNat = l3.left.toNat - 1 :=
        UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))
      have I5 := I4.produce (l' := { l3 with put := Ptr.ref (BRef.blk w) (idx + 1), left := l3.left - 1 }) 1
        (by show (l3.left - 1).toNat + 1 = _; omega) (by rw [hput]; rfl) rfl rfl rfl rfl
      have hs5 : (winHeap h3 w (a3.set! idx S2.length.toUInt8)).istates i = some { S2 with whave := wv } := hs3
      let S6 : InflateState := { S2 with whave := wv, mode := LEN }
      have I6 := I5.setState hs5 S6 rfl rfl rfl (wf_with wf _ rfl rfl rfl)
        ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), fun _ => tabs⟩
      refine ⟨.ok (), _, _, ?_, _, I6, Or.inl ⟨rfl, ?_⟩, fun _ => Short.of_bits (by
        show l3.bits.toNat < 8; rw [bits3]; exact short1)⟩
      · unfold lenSym
        simp only [runX_bind, runX_get, hd1, runX_lift_ok wr2, lit, ↓reduceIte, run3, runX_lift_ok ld3,
          runX_lift_ok st, runX_lift_ok add, runX_set,
          runX_lift_ok (setMode_ok I3.cst hs5 LEN), runX_pure]
        rfl
      · have r6 : modeRank S6.mode = 2 := by show modeRank LEN = 2; decide
        rw [backMeasure_of pr (s := S6) (by simp [setI]), r6]
        unfold baseM at b3 ⊢
        show 4 * (l3.bits.toNat + 8 * l3.have_.toNat + _) + 2 < B
        unfold baseM at lt1
        omega
  · have lit' : (l.here.op == 0) = false := by simpa using lit
    by_cases eob : ((l.here.op &&& 32) != 0) = true
    · -- the end of the block
      let S3 : InflateState := { S2 with mode := TYPE }
      have I3 := I2.setState hs2 S3 rfl rfl rfl (wf_with wf _ rfl rfl rfl) (modeOk_ty i S2)
      refine ⟨.ok (), l1, setI (setI h i S2) i S3, ?_, log, I3, Or.inl ⟨rfl, ?_⟩, fun _ => Short.of_bits short1⟩
      · unfold lenSym
        simp only [runX_bind, runX_get, hd1, runX_lift_ok wr2, lit', Bool.false_eq_true, ↓reduceIte, eob,
          runX_lift_ok (setMode_ok I.cst hs2 TYPE), runX_pure]
        rfl
      · have r3 : modeRank S3.mode = 1 := by show modeRank TYPE = 1; decide
        rw [backMeasure_of pr (s := S3) (by simp [setI]), r3]
        omega
    · have eob' : ((l.here.op &&& 32) != 0) = false := by simpa using eob
      by_cases bad : ((l.here.op &&& 64) != 0) = true
      · obtain ⟨hb, runB, T⟩ := TRound.bad I2 "invalid literal/length code" lit_len_code (B := B) (by omega)
        refine ⟨.ok (), l1, hb, ?_, T⟩
        unfold lenSym
        simp only [runX_bind, runX_get, hd1, runX_lift_ok wr2, lit', eob', bad, Bool.false_eq_true, ↓reduceIte,
          runX_lift_ok runB]
        rfl
      · have bad' : ((l.here.op &&& 64) != 0) = false := by simpa using bad
        have op0 : l.here.op ≠ 0 := by simpa using lit'
        have op64 : l.here.op &&& 64 = 0 := by simpa using bad
        obtain ⟨-, kinds⟩ := leaf
        have lenLeaf : l.here.op &&& 16 ≠ 0 ∧ (l.here.op &&& 15).toNat ≤ 5 ∧ 3 ≤ l.here.val.toNat ∧
            l.here.val.toNat + 2 ^ (l.here.op &&& 15).toNat ≤ 259 := by
          rcases kinds with z | ln | inv
          · exact absurd z op0
          · exact ln
          · exact absurd op64 inv.2
        obtain ⟨-, ex5, val3, valMax⟩ := lenLeaf
        have exN : (l.here.op.toUInt32 &&& 15).toNat = (l.here.op &&& 15).toNat := Zlib.Inffast.Proofs.mask15 _
        have val32 : l.here.val.toUInt32.toNat = l.here.val.toNat := UInt16.toNat_toUInt32 _
        let S3 : InflateState := { S2 with extra := l.here.op.toUInt32 &&& 15 }
        have hs3 : (setI (setI h i S2) i S3).istates i = some S3 := by simp [setI]
        have wr3 : wrS c.st (fun s => { s with extra := l.here.op.toUInt32 &&& 15 }) (setI h i S2) =
            .ok ((), setI (setI h i S2) i S3) := wrS_ok I.cst hs2 _
        have I3 := I2.setState hs2 S3 rfl rfl rfl (wf_with wf _ rfl rfl rfl) (I.mode s0 hs)
        by_cases hex : ((l.here.op.toUInt32 &&& 15) != 0) = true
        · obtain ⟨res4, l4, h4, log4, run4, I4, ok4, err4, ist4, meas4⟩ :=
            NEEDBITS_p c pr (l.here.op.toUInt32 &&& 15) (by rw [exN]; omega) I3
          have hs4 : h4.istates i = some S3 := ist4.trans hs3
          cases res4 with
          | error e =>
            obtain ⟨rfl, ret⟩ := err4 e rfl
            refine ⟨.error Ex.leave, l4, h4, ?_, TRound.leave I4 B ret⟩
            unfold lenSym
            simp only [runX_bind, runX_get, hd1, runX_lift_ok wr2, lit', eob', bad', Bool.false_eq_true,
              ↓reduceIte, runX_lift_ok wr3, hex, run4]
          | ok u =>
            cases u
            obtain ⟨k4, -, -, mx4⟩ := ok4 rfl
            have b4 := baseM_le meas4
            obtain ⟨bv, hbv⟩ : ∃ bv : UInt32, bv = bitsV l4 (l.here.op.toUInt32 &&& 15) := ⟨_, rfl⟩
            have bvlt : bv.toNat < 2 ^ (l.here.op &&& 15).toNat := by
              rw [hbv, ← exN]; exact bitsV_lt l4 (by rw [exN]; omega)
            have rb : runX (BITS (l.here.op.toUInt32 &&& 15)) l4 h4 = .ok ((.ok bv, l4), h4) := by
              rw [BITS_run _ _ _ (by rw [exN]; omega), hbv]; rfl
            let S5 : InflateState := { S3 with length := S3.length + bv }
            have hs5 : (setI h4 i S5).istates i = some S5 := by simp [setI]
            have wr5 : wrS c.st (fun s => { s with length := s.length + bv }) h4 = .ok ((), setI h4 i S5) :=
              wrS_ok I4.cst hs4 _
            have I5 := I4.setState hs4 S5 rfl rfl rfl (wf_with wf _ rfl rfl rfl) (I.mode s0 hs)
            obtain ⟨l6, hl6⟩ : ∃ l6 : IL, l6 = dropR l4 (l.here.op.toUInt32 &&& 15) := ⟨_, rfl⟩
            obtain ⟨hd6, I6, e6, m6, -⟩ := drop_p I5 (l.here.op.toUInt32 &&& 15) k4 hl6
            have short6 : l6.bits.toNat < 8 := by
              rw [e6]
              have m : l4.bits.toNat ≤ max l1.bits.toNat ((l.here.op.toUInt32 &&& 15).toNat + 7) := mx4
              have : l4.bits.toNat ≤ (l.here.op.toUInt32 &&& 15).toNat + 7 :=
                Nat.le_trans m (Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩)
              omega
            have len5 : 1 ≤ S5.length.toNat := by
              show 1 ≤ (l.here.val.toUInt32 + bv).toNat
              rw [UInt32.toNat_add, val32]
              have : 2 ^ (l.here.op &&& 15).toNat ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) ex5
              omega
            obtain ⟨res7, l7, h7, run7, T7⟩ :=
              lenDist_p c pr I6 hw hs5 mode tabs len5 short6 (B := B) (by omega)
            refine ⟨res7, l7, h7, ?_, T7⟩
            unfold lenSym
            simp only [runX_bind, runX_get, hd1, runX_lift_ok wr2, lit', eob', bad', Bool.false_eq_true,
              ↓reduceIte, runX_lift_ok wr3, hex, run4, rb, runX_lift_ok wr5, hd6]
            exact run7
        · have hex' : ((l.here.op.toUInt32 &&& 15) != 0) = false := by simpa using hex
          obtain ⟨res7, l7, h7, run7, T7⟩ :=
            lenDist_p c pr I3 hw hs3 mode tabs (by show 1 ≤ l.here.val.toUInt32.toNat; omega) short1
              (B := B) lt1
          refine ⟨res7, l7, h7, ?_, T7⟩
          unfold lenSym
          simp only [runX_bind, runX_get, hd1, runX_lift_ok wr2, lit', eob', bad', Bool.false_eq_true,
            ↓reduceIte, runX_lift_ok wr3, hex', runX_pure]
          exact run7

set_option maxRecDepth 100000 in
/-- **`case LEN` without the fast path, on the invariant**: one literal, the end of the block,
an invalid code, or a length/distance pair and its copy; or `Z_BUF_ERROR` from `in` or `out`.
The measure falls: the literal/length code reads at least one bit. Fewer than 8 bits stay held. -/
theorem LEN_slow_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {w woff : Nat} (hw : window = .ref (.blk w) woff) {s : InflateState} (hs : h.istates i = some s)
    (mode : s.mode = LEN) (short : l.bits.toNat < 8) (slow : (l.have_ >= 6 && l.left >= 258) = false) :
    ∃ res l' h', runX (back_LEN c) l h = .ok ((res, l'), h') ∧ Round c pr h0 h l log res l' h' := by
  obtain ⟨z, s0, valid, -, -⟩ := I.valid
  have e0 : s0 = s := Option.some.inj (valid.2.1.symm.trans hs)
  subst e0
  have globals := valid.2.2.2.2.2.2.2.2.2.2.2.2.2
  have tabs : TablesOk i s0 := (I.mode s0 hs).2 mode
  obtain ⟨ref, off, ca, used, lens, lc, refOk, get, safe, inv, stable, pfx⟩ := lenTab hs tabs globals
  have m0 : backMeasure pr h l log = baseM pr l log + 2 := by
    rw [backMeasure_of pr hs, mode]; rfl
  have pre : runX (back_LEN c) l h = runX (symLook c false lenIsLink (lenSym c)) l h := by
    rw [back_LEN_eq']
    simp only [runX_bind, runX_get, slow, Bool.false_eq_true, ↓reduceIte]
  rcases symLook_p c pr false lenIsLink (lenSym c) I hs (type := LENS) lc rfl refOk get safe
      (fun _ _ x => x.1) lenIsLink_eq (fun e x => lenLink_of_code e.op x)
      (fun e x y => code_of_lenLink e.op x.1 x.2.1 x.2.2 y) inv stable pfx short with
    ⟨l2, h2, log2, run2, I2, ret⟩ | ⟨l2, h2, log2, d, run2, I2, ist2, -, -, leaf, pos, fit, short2, b2⟩
  · refine ⟨.error Ex.leave, l2, h2, by rw [pre]; exact run2, TRound.leave I2 _ ret⟩
  · obtain ⟨res3, l3, h3, run3, T3⟩ :=
      lenSym_p c pr I2 hw (ist2.trans hs) mode tabs leaf pos fit short2
        (B := backMeasure pr h l log) (by rw [m0]; omega)
    exact ⟨res3, l3, h3, by rw [pre, run2]; exact run3, T3⟩

end Zlib.Infback.Safety
