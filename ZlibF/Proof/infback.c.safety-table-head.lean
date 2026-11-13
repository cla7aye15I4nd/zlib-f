import ZlibF.Proof.«infback.c.safety-lookup»
import ZlibF.Proof.«inflate.c.main.table2»
import ZlibF.Proof.«inflate.c.main.check0»

/-!
# infback.c: `case TABLE` on the loop invariant, the header

`back_TABLE` is split at its loops and table calls (`back_TABLE_eq`, by `rfl`). `TRound` is what a
piece of the round leaves when the round ends inside it, relative to the measure `B` at the start
of the round. `tabHead_p` is the header: `NEEDBITS(14)`, the three counts, and the check of the
counts; it ends with `BAD` or `Z_BUF_ERROR`, or reaches the code-length loops with the counts in
range.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
open Zlib.Inftrees (inflate_table)
set_option autoImplicit false

/-- The condition of the loop over the code-length code lengths read from the stream. -/
def tl1Cond (c : BCtx) : X Bool :=
  do let s ← ldInflateState c.st; return s.«have» < s.ncode

/-- One code-length code length read from the stream. -/
def tl1Body (c : BCtx) : X Unit := do
  NEEDBITS c 3
  let s ← ldInflateState c.st
  wrS c.st fun s => { s with «have» := s.«have» + 1 }
  let o ← orderAt s.«have»
  let b ← BITS 3
  Ptr.store (← (lensP c.st).add (o.toNat : Int)) b.toUInt16
  DROPBITS 3

/-- `case TABLE`: the code-length code lengths read from the stream. -/
def tabLoop1 (c : BCtx) : X Unit := xwhile (tl1Cond c) (tl1Body c)

/-- The condition of the loop over the code-length code lengths not sent. -/
def tl2Cond (c : BCtx) : X Bool :=
  do let s ← ldInflateState c.st; return s.«have» < 19

/-- One code-length code length not sent, set to 0. -/
def tl2Body (c : BCtx) : X Unit := do
  let s ← ldInflateState c.st
  wrS c.st fun s => { s with «have» := s.«have» + 1 }
  let o ← orderAt s.«have»
  Ptr.store (← (lensP c.st).add (o.toNat : Int)) (0 : UInt16)

/-- `case TABLE`: the code-length code lengths not sent, set to 0. -/
def tabLoop2 (c : BCtx) : X Unit := xwhile (tl2Cond c) (tl2Body c)

/-- `case TABLE`: the literal/length and distance code lengths, decoded with the code-length code. -/
def tabRead (c : BCtx) : X Unit :=
  xwhileBrk
    (do let s ← ldInflateState c.st; return s.«have» < s.nlen + s.ndist)
    (do
      lookup1 c false
      let here := (← get).here
      if here.val < 16 then
        DROPBITS here.bits.toUInt32
        let s ← ldInflateState c.st
        Ptr.store (← (lensP c.st).add (s.«have».toNat : Int)) here.val
        wrS c.st fun s => { s with «have» := s.«have» + 1 }
        return false
      else
        if here.val == 16 then
          NEEDBITS c (here.bits.toUInt32 + 2)
          DROPBITS here.bits.toUInt32
          let s ← ldInflateState c.st
          if s.«have» == 0 then
            badMode c "invalid bit length repeat"
            return true
          -- len = (unsigned)(state->lens[state->have - 1]); copy = 3 + BITS(2); DROPBITS(2);
          let v ← Ptr.index (lensP c.st) ((s.«have» - 1).toNat : Int)
          let b ← BITS 2
          modify fun l => { l with len := v.toUInt32, copy := 3 + b }
          DROPBITS 2
        else if here.val == 17 then
          NEEDBITS c (here.bits.toUInt32 + 3)
          DROPBITS here.bits.toUInt32
          let b ← BITS 3
          modify fun l => { l with len := 0, copy := 3 + b }
          DROPBITS 3
        else
          NEEDBITS c (here.bits.toUInt32 + 7)
          DROPBITS here.bits.toUInt32
          let b ← BITS 7
          modify fun l => { l with len := 0, copy := 11 + b }
          DROPBITS 7
        let s ← ldInflateState c.st
        if s.«have» + (← get).copy > s.nlen + s.ndist then
          badMode c "invalid bit length repeat"
          return true
        xwhile
          (do
            let l ← get
            set { l with copy := l.copy - 1 }
            return l.copy != 0)
          (do
            let s ← ldInflateState c.st
            Ptr.store (← (lensP c.st).add (s.«have».toNat : Int)) (← get).len.toUInt16
            wrS c.st fun s => { s with «have» := s.«have» + 1 })
        return false)

/-- `case TABLE` after the distance table call. -/
def tabLensTail2 (c : BCtx) (r : Int32) : X Unit := do
  if r != 0 then
    badMode c "invalid distances set"
    return
  -- state->mode = LEN; /* fallthrough */
  setMode c.st LEN
  back_LEN c

/-- `case TABLE` after the literal/length table call. -/
def tabLensTail1 (c : BCtx) (r : Int32) : X Unit := do
  if r != 0 then
    badMode c "invalid literal/lengths set"
    return
  wrS c.st fun s => { s with distcode := s.next, distbits := 6 }
  let s ← ldInflateState c.st
  let (r, nx, db) ← inflate_table DISTS (← (lensP c.st).add (s.nlen.toNat : Int)) s.ndist s.next s.distbits (workP c.st)
  wrS c.st fun s => { s with next := nx, distbits := db }
  modify fun l => { l with ret := r }
  tabLensTail2 c r

/-- `case TABLE`: the literal/length and distance tables, then `case LEN`. -/
def tabLens (c : BCtx) : X Unit := do
  wrS c.st fun s => { s with next := codesP c.st, lencode := codesP c.st, lenbits := 9 }
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table LENS (lensP c.st) s.nlen s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  tabLensTail1 c r

/-- `case TABLE` after the decoded code lengths: the mode check, the end-of-block check, the tables. -/
def tabC (c : BCtx) : X Unit := do
  if (← rdS c.st (·.mode)) == BAD then return
  if (← Ptr.index (lensP c.st) 256) == (0 : UInt16) then
    badMode c "invalid code -- missing end-of-block"
    return
  tabLens c

/-- `case TABLE` after the code-length table call. -/
def tabBTail (c : BCtx) (r : Int32) : X Unit := do
  if r != 0 then
    badMode c "invalid code lengths set"
    return
  wrS c.st fun s => { s with «have» := 0 }
  tabRead c
  tabC c

/-- `case TABLE` after the code-length code lengths: the code-length table, the decoded lengths. -/
def tabB (c : BCtx) : X Unit := do
  wrS c.st fun s => { s with next := codesP c.st, lencode := codesP c.st, lenbits := 7 }
  let s ← ldInflateState c.st
  let (r, nx, lb) ← inflate_table CODES (lensP c.st) 19 s.next s.lenbits (workP c.st)
  wrS c.st fun s => { s with next := nx, lenbits := lb }
  modify fun l => { l with ret := r }
  tabBTail c r

/-- `case TABLE` after the header. -/
def tabA (c : BCtx) : X Unit := do
  tabLoop1 c
  tabLoop2 c
  tabB c

theorem back_TABLE_eq (c : BCtx) : back_TABLE c = (do
  NEEDBITS c 14
  let b ← BITS 5
  wrS c.st fun s => { s with nlen := b + 257 }
  DROPBITS 5
  let b ← BITS 5
  wrS c.st fun s => { s with ndist := b + 1 }
  DROPBITS 5
  let b ← BITS 4
  wrS c.st fun s => { s with ncode := b + 4 }
  DROPBITS 4
  -- if (state->nlen > 286 || state->ndist > 30) { "too many length or distance symbols"; BAD; break; }
  let s ← ldInflateState c.st
  if s.nlen > 286 || s.ndist > 30 then
    badMode c "too many length or distance symbols"
    return
  -- state->have = 0; while (state->have < state->ncode) { NEEDBITS(3); lens[order[have++]] = BITS(3); DROPBITS(3); }
  wrS c.st fun s => { s with «have» := 0 }
  tabA c) := rfl

/-- The counts of `case TABLE` in range, the mode still `TABLE`. -/
structure TabSt (s : InflateState) : Prop where
  mode : s.mode = TABLE
  nlen : s.nlen.toNat ≤ 286
  ndist : s.ndist.toNat ≤ 30
  ncode : s.ncode.toNat ≤ 19

/-- What a piece of a round leaves when the round ends inside it: the invariant, and a measure
below `B` or the way out with one of the three results. -/
def TRound (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (h0 : Heap) (B : Nat) (res : Except Ex Unit) (l' : IL) (h' : Heap) : Prop :=
  ∃ log', PInv c pr h0 h' l' log' ∧
    ((res = .ok () ∧ backMeasure pr h' l' log' < B) ∨
     (res = .error Ex.leave ∧ (l'.ret = Z_STREAM_END ∨ l'.ret = Z_DATA_ERROR ∨ l'.ret = Z_BUF_ERROR)))

theorem TRound.leave {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    {pr : Proto c r i window n} {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    (B : Nat) (ret : l.ret = Z_BUF_ERROR) : TRound c pr h0 B (.error Ex.leave) l h :=
  ⟨log, I, Or.inr ⟨rfl, Or.inr (Or.inr ret)⟩⟩

/-- **`strm->msg = "..."; state->mode = BAD;` on the invariant.** The rank becomes 0. -/
theorem PInv.badRound {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    {pr : Proto c r i window n} {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    (msg : String) (hm : msg ∈ strTable) :
    ∃ h', badMode c msg h = .ok ((), h') ∧ PInv c pr h0 h' l log ∧ backMeasure pr h' l log = baseM pr l log ∧
      ∃ s', h'.istates i = some s' ∧ s'.mode = BAD := by
  obtain ⟨z, s, valid, -, -⟩ := I.valid
  have wf := valid.2.2.2.2.2.1
  obtain ⟨k, hbad⟩ := badMode_run c I.cstrm I.cst valid.1 valid.2.1 msg hm
  have IB := I.putMsg valid.1 (.ref (.str k) 0)
  have hsB : (r.put h { z with msg := .ref (.str k) 0 }).istates i = some s := by
    rw [ZStreamRef.put_istates]; exact valid.2.1
  have IC := IB.setState hsB { s with mode := BAD } rfl rfl rfl (wf_with wf _ rfl rfl rfl)
    (modeOk_of (Or.inr (Or.inr (Or.inr rfl))))
  refine ⟨_, hbad, IC, ?_, { s with mode := BAD }, by simp [setI], rfl⟩
  rw [backMeasure_of pr (s := { s with mode := BAD }) (by simp [setI]) l log]
  show baseM pr l log + modeRank BAD = _
  rw [modeRank_BAD]; rfl

theorem TRound.bad {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    {pr : Proto c r i window n} {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    (msg : String) (hm : msg ∈ strTable) {B : Nat} (lt : baseM pr l log < B) :
    ∃ h', badMode c msg h = .ok ((), h') ∧ TRound c pr h0 B (.ok ()) l h' := by
  obtain ⟨h', run, I', m, -⟩ := I.badRound msg hm
  exact ⟨h', run, log, I', Or.inl ⟨rfl, by rw [m]; exact lt⟩⟩

theorem PInv.withRegs {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    {pr : Proto c r i window n} {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) {l' : IL}
    (put : l'.put = l.put) (left : l'.left = l.left) (have_ : l'.have_ = l.have_) (next : l'.next = l.next)
    (bits : l'.bits = l.bits) (hold : l'.hold = l.hold) : PInv c pr h0 h l' log :=
  I.regs put left have_ next (by rw [bits]; exact I.bits.1) (by rw [hold, bits]; exact I.bits.2)

set_option maxRecDepth 100000 in
/-- **The header of `case TABLE` on the invariant.** `NEEDBITS(14)` and the three counts; too many
symbols give `BAD`; no input gives `Z_BUF_ERROR`; otherwise the code-length loops start with
`have = 0` and the counts in range. -/
theorem tabHead_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (mode : s.mode = TABLE) :
    (∃ res l' h', runX (back_TABLE c) l h = .ok ((res, l'), h') ∧ TRound c pr h0 (baseM pr l log + 2) res l' h') ∨
    (∃ l1 h1 log1 s1, runX (back_TABLE c) l h = runX (tabA c) l1 h1 ∧ PInv c pr h0 h1 l1 log1 ∧
      h1.istates i = some s1 ∧ TabSt s1 ∧ s1.«have» = 0 ∧ baseM pr l1 log1 ≤ baseM pr l log) := by
  obtain ⟨res0, l1, h1, log1, run1, I1, okc, errc, ist1, meas1⟩ := NEEDBITS_p c pr 14 (by decide) I
  have b1 := baseM_le meas1
  cases res0 with
  | error e =>
    obtain ⟨rfl, ret⟩ := errc e rfl
    left
    refine ⟨.error Ex.leave, l1, h1, ?_, TRound.leave I1 _ ret⟩
    rw [back_TABLE_eq]
    simp only [runX_bind, run1]
  | ok u =>
    cases u
    obtain ⟨b14, -, -, -⟩ := okc rfl
    have hs1 : h1.istates i = some s := ist1.trans hs
    obtain ⟨z1, s1, valid1, -, -⟩ := I1.valid
    have e1 : s1 = s := Option.some.inj (valid1.2.1.symm.trans hs1)
    subst e1
    have wf := valid1.2.2.2.2.2.1
    have h14 : (14 : UInt32).toNat = 14 := rfl
    rw [h14] at b14
    have hb39 := I1.bits.1
    have B0 := bitInv_of I1
    obtain ⟨v1, hv1⟩ : ∃ v : UInt32, v = l1.hold.toUInt32 &&& ((1 : UInt32) <<< 5 - 1) := ⟨_, rfl⟩
    obtain ⟨l2, hl2⟩ : ∃ l2 : IL, l2 = { l1 with hold := l1.hold >>> (5 : UInt32).toUInt64, bits := l1.bits - 5 } :=
      ⟨_, rfl⟩
    obtain ⟨v2, hv2⟩ : ∃ v : UInt32, v = l2.hold.toUInt32 &&& ((1 : UInt32) <<< 5 - 1) := ⟨_, rfl⟩
    obtain ⟨l3, hl3⟩ : ∃ l3 : IL, l3 = { l2 with hold := l2.hold >>> (5 : UInt32).toUInt64, bits := l2.bits - 5 } :=
      ⟨_, rfl⟩
    obtain ⟨v3, hv3⟩ : ∃ v : UInt32, v = l3.hold.toUInt32 &&& ((1 : UInt32) <<< 4 - 1) := ⟨_, rfl⟩
    obtain ⟨l4, hl4⟩ : ∃ l4 : IL, l4 = { l3 with hold := l3.hold >>> (4 : UInt32).toUInt64, bits := l3.bits - 4 } :=
      ⟨_, rfl⟩
    obtain ⟨B2, -, hbit2⟩ := DROPBITS_inv B0 5 (by rw [show (5 : UInt32).toNat = 5 from rfl]; omega) (by decide)
    rw [← hl2] at B2
    have e2 : l2.bits.toNat = l1.bits.toNat - 5 := by rw [hl2]; exact hbit2
    obtain ⟨B3, -, hbit3⟩ := DROPBITS_inv B2 5 (by rw [show (5 : UInt32).toNat = 5 from rfl]; omega) (by decide)
    rw [← hl3] at B3
    have e3 : l3.bits.toNat = l1.bits.toNat - 10 := by rw [hl3]; rw [hbit3, e2]; rfl
    obtain ⟨B4, -, hbit4⟩ := DROPBITS_inv B3 4 (by rw [show (4 : UInt32).toNat = 4 from rfl]; omega) (by decide)
    rw [← hl4] at B4
    have e4 : l4.bits.toNat = l1.bits.toNat - 14 := by rw [hl4]; rw [hbit4, e3]; rfl
    have hr1 : ∀ hh, runX (BITS 5) l1 hh = .ok ((.ok v1, l1), hh) := by
      intro hh; rw [BITS_run l1 hh 5 (by decide), hv1]
    have hd1 : ∀ hh, runX (DROPBITS 5) l1 hh = .ok ((.ok (), l2), hh) := by
      intro hh; rw [DROPBITS_run l1 hh 5 (by decide), hl2]
    have hr2 : ∀ hh, runX (BITS 5) l2 hh = .ok ((.ok v2, l2), hh) := by
      intro hh; rw [BITS_run l2 hh 5 (by decide), hv2]
    have hd2 : ∀ hh, runX (DROPBITS 5) l2 hh = .ok ((.ok (), l3), hh) := by
      intro hh; rw [DROPBITS_run l2 hh 5 (by decide), hl3]
    have hr3 : ∀ hh, runX (BITS 4) l3 hh = .ok ((.ok v3, l3), hh) := by
      intro hh; rw [BITS_run l3 hh 4 (by decide), hv3]
    have hd3 : ∀ hh, runX (DROPBITS 4) l3 hh = .ok ((.ok (), l4), hh) := by
      intro hh; rw [DROPBITS_run l3 hh 4 (by decide), hl4]
    have v3lt : v3.toNat < 16 := by
      rw [hv3, BITS_toNat l3 4 (by decide)]; exact Nat.mod_lt _ (by decide)
    obtain ⟨sA, hsA⟩ : ∃ x : InflateState, x = { s1 with nlen := v1 + 257 } := ⟨_, rfl⟩
    obtain ⟨sB, hsB⟩ : ∃ x : InflateState, x = { sA with ndist := v2 + 1 } := ⟨_, rfl⟩
    obtain ⟨sC, hsC⟩ : ∃ x : InflateState, x = { sB with ncode := v3 + 4 } := ⟨_, rfl⟩
    have hwA : wrS c.st (fun s => { s with nlen := v1 + 257 }) h1 = .ok ((), setI h1 i sA) := by
      rw [wrS_ok I1.cst hs1, hsA]
    have hwB : wrS c.st (fun s => { s with ndist := v2 + 1 }) (setI h1 i sA) = .ok ((), setI (setI h1 i sA) i sB) := by
      rw [wrS_ok I1.cst (show (setI h1 i sA).istates i = some sA by simp [setI]), hsB]
    have hwC : wrS c.st (fun s => { s with ncode := v3 + 4 }) (setI (setI h1 i sA) i sB) =
        .ok ((), setI (setI (setI h1 i sA) i sB) i sC) := by
      rw [wrS_ok I1.cst (show (setI (setI h1 i sA) i sB).istates i = some sB by simp [setI]), hsC]
    have hld : ldInflateState c.st (setI (setI (setI h1 i sA) i sB) i sC) =
        .ok (sC, setI (setI (setI h1 i sA) i sB) i sC) := by
      rw [I1.cst]; exact ldInflateState_tab (by simp [setI])
    have modeC : sC.mode = TABLE := by rw [hsC, hsB, hsA]; exact mode
    have IC : PInv c pr h0 (setI h1 i sC) l4 log1 :=
      (I1.setState hs1 sC (by rw [hsC, hsB, hsA]) (by rw [hsC, hsB, hsA]) (by rw [hsC, hsB, hsA])
        (wf_with wf _ (by rw [hsC, hsB, hsA]) (by rw [hsC, hsB, hsA]) (by rw [hsC, hsB, hsA]))
        (modeOk_of (Or.inr (Or.inl modeC)))).regs (l' := l4)
        (by rw [hl4, hl3, hl2]) (by rw [hl4, hl3, hl2]) (by rw [hl4, hl3, hl2]) (by rw [hl4, hl3, hl2])
        (by omega) B4.hold_lt
    have b4 : baseM pr l4 log1 ≤ baseM pr l log := by
      have have4 : l4.have_ = l1.have_ := by rw [hl4, hl3, hl2]
      unfold baseM at b1 ⊢
      rw [have4, e4]
      omega
    have pre : runX (back_TABLE c) l h = runX (do
        let s ← ldInflateState c.st
        if s.nlen > 286 || s.ndist > 30 then
          badMode c "too many length or distance symbols"
          return
        wrS c.st fun s => { s with «have» := 0 }
        tabA c) l4 (setI (setI (setI h1 i sA) i sB) i sC) := by
      rw [back_TABLE_eq]
      simp only [runX_bind, run1, hr1, runX_lift_ok hwA, hd1, hr2, runX_lift_ok hwB, hd2, hr3, runX_lift_ok hwC, hd3]
    have heap : setI (setI (setI h1 i sA) i sB) i sC = setI h1 i sC := by simp only [setI_setI]
    rw [heap] at pre hld
    have hsC' : (setI h1 i sC).istates i = some sC := by simp [setI]
    by_cases bad : (sC.nlen > 286 || sC.ndist > 30) = true
    · left
      obtain ⟨hb, runB, T⟩ := TRound.bad (B := baseM pr l log + 2) IC "too many length or distance symbols"
        lit_many_symbols (by omega)
      refine ⟨.ok (), l4, hb, ?_, T⟩
      rw [pre]
      simp only [runX_bind, runX_lift_ok hld, bad, ↓reduceIte, runX_lift_ok runB]
      rfl
    · right
      have bad' : (sC.nlen > 286 || sC.ndist > 30) = false := by simpa using bad
      have nl : ¬ sC.nlen > 286 := fun x => by simp [x] at bad
      have nd : ¬ sC.ndist > 30 := fun x => by simp [x] at bad
      have hwD : wrS c.st (fun s => { s with «have» := 0 }) (setI h1 i sC) =
          .ok ((), setI (setI h1 i sC) i { sC with «have» := 0 }) := wrS_ok I1.cst hsC' _
      have ID := IC.setState hsC' { sC with «have» := 0 } rfl rfl rfl (wf_with
        (by rw [hsC, hsB, hsA]; exact wf) _ rfl rfl rfl) (modeOk_of (Or.inr (Or.inl modeC)))
      refine ⟨l4, setI (setI h1 i sC) i { sC with «have» := 0 }, log1, { sC with «have» := 0 }, ?_, ID,
        by simp [setI], ⟨modeC, ?_, ?_, ?_⟩, rfl, b4⟩
      · rw [pre]
        simp only [runX_bind, runX_lift_ok hld, bad', Bool.false_eq_true, ↓reduceIte, runX_lift_ok hwD]
      · have := mt UInt32.lt_iff_toNat_lt.mpr nl
        show sC.nlen.toNat ≤ 286
        simp only [UInt32.toNat_ofNat] at this
        omega
      · have := mt UInt32.lt_iff_toNat_lt.mpr nd
        show sC.ndist.toNat ≤ 30
        simp only [UInt32.toNat_ofNat] at this
        omega
      · show (sC.ncode).toNat ≤ 19
        rw [hsC]
        show (v3 + 4).toNat ≤ 19
        rw [UInt32.toNat_add]
        simp only [show (4 : UInt32).toNat = 4 from rfl]
        omega

end Zlib.Infback.Safety
