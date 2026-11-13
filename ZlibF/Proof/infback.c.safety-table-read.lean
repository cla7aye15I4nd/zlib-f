import ZlibF.Proof.«infback.c.safety-table-codes»

/-!
# infback.c: `case TABLE` on the loop invariant, the decoded code lengths

The loop `while (state->have < state->nlen + state->ndist)` decodes the literal/length and
distance code lengths with the code-length table (`lookup1_p`): a length below 16 is stored at
`lens[have]`; 16, 17 and 18 repeat the previous length or 0 for `copy` entries after the check
`have + copy <= nlen + ndist`. Every store is inside `lens` (`nlen + ndist ≤ 316`), every stored
length is at most 15 (`RL`). The loop is measured by `nlen + ndist - have`; it leaves with `BAD`
(a bad repeat, which `tabC` sees), with `Z_BUF_ERROR`, or with `have = nlen + ndist`.
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
set_option autoImplicit false

/-- The condition of the decoding loop. -/
def trCond (c : BCtx) : X Bool := do
  let s ← ldInflateState c.st
  return s.«have» < s.nlen + s.ndist

/-- The condition of the repeat loop: `while (copy--)`. -/
def trCopyCond : X Bool := do
  let l ← get
  set { l with copy := l.copy - 1 }
  return l.copy != 0

/-- The body of the repeat loop: `state->lens[state->have++] = (unsigned short)len;`. -/
def trCopyBody (c : BCtx) : X Unit := do
  let s ← ldInflateState c.st
  Ptr.store (← (lensP c.st).add (s.«have».toNat : Int)) (← get).len.toUInt16
  wrS c.st fun s => { s with «have» := s.«have» + 1 }

/-- After a repeat code: the check and the repeat loop. -/
def trTail (c : BCtx) : X Bool := do
  let s ← ldInflateState c.st
  if s.«have» + (← get).copy > s.nlen + s.ndist then
    badMode c "invalid bit length repeat"
    return true
  xwhile trCopyCond (trCopyBody c)
  return false

/-- A repeat code (16, 17, 18). -/
def trRep (c : BCtx) (here : Code) : X Bool := do
  if here.val == 16 then
    NEEDBITS c (here.bits.toUInt32 + 2)
    DROPBITS here.bits.toUInt32
    let s ← ldInflateState c.st
    if s.«have» == 0 then
      badMode c "invalid bit length repeat"
      return true
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
  trTail c

/-- A length below 16. -/
def trLit (c : BCtx) (here : Code) : X Bool := do
  DROPBITS here.bits.toUInt32
  let s ← ldInflateState c.st
  Ptr.store (← (lensP c.st).add (s.«have».toNat : Int)) here.val
  wrS c.st fun s => { s with «have» := s.«have» + 1 }
  return false

/-- The body of the decoding loop after the lookup. -/
def trAfter (c : BCtx) : X Bool := do
  let here := (← get).here
  if here.val < 16 then trLit c here else trRep c here

theorem tabRead_eq (c : BCtx) :
    tabRead c = xwhileBrk (trCond c) (do Zlib.Infback.lookup1 c false; trAfter c) := rfl

/-- The decoded lengths so far are at most 15. -/
def RL (s : InflateState) : Prop := ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15

/-- The state of the decoding loop. -/
structure RdSt (i : Nat) (s : InflateState) : Prop where
  tab : TabSt s
  rd : RdTab i s
  le : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat
  rl : RL s

/-- The state after `state->lens[state->have++] = v`. -/
def rdSet (s : InflateState) (v : UInt16) : InflateState :=
  { s with lens := s.lens.set! s.«have».toNat v, «have» := s.«have» + 1 }

theorem rdSet_have {s : InflateState} (lt : s.«have».toNat < 320) (v : UInt16) :
    (rdSet s v).«have».toNat = s.«have».toNat + 1 := by
  show (s.«have» + 1).toNat = _
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_one]
  omega

theorem rdSet_st {i : Nat} {s : InflateState} (rd : RdSt i s) (lt : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (size : s.lens.size = 320) {v : UInt16} (hv : v.toNat ≤ 15) : RdSt i (rdSet s v) := by
  have l320 : s.«have».toNat < 320 := by have := rd.tab.nlen; have := rd.tab.ndist; omega
  refine ⟨⟨rd.tab.mode, rd.tab.nlen, rd.tab.ndist, rd.tab.ncode⟩, rd.rd, ?_, ?_⟩
  · rw [rdSet_have l320]; show s.«have».toNat + 1 ≤ s.nlen.toNat + s.ndist.toNat; omega
  · intro k hk
    rw [rdSet_have l320] at hk
    show ((s.lens.set! s.«have».toNat v).getD k 0).toNat ≤ 15
    rw [Zlib.Inftrees.Proofs.getD_set!]
    split
    · exact hv
    · next ne =>
      rcases Nat.lt_or_ge k s.«have».toNat with x | x
      · exact rd.rl k x
      · exfalso; apply ne; refine ⟨by omega, ?_⟩; rw [size]; exact l320

/-- `lens + have` and the store into it. -/
theorem lens_at {i : Nat} {h : Heap} {s : InflateState} (hs : h.istates i = some s) (lt : s.«have».toNat < 320)
    (size : s.lens.size = 320) (v : UInt16) :
    OkOn h (Ptr.add (Ptr.ref (WRef.istate_lens i) 0) (s.«have».toNat : Int))
      (Ptr.ref (WRef.istate_lens i) (0 + s.«have».toNat)) ∧
    Ptr.store (Ptr.ref (WRef.istate_lens i) (0 + s.«have».toNat)) v h =
      .ok ((), setI h i { s with lens := s.lens.set! s.«have».toNat v }) := by
  have getL := WRef.get_istate_lens hs
  refine ⟨Ptr.add_nat_ok getL (by omega), ?_⟩
  have st := Ptr.store_ok (off := 0 + s.«have».toNat) (v := v) getL rfl (by omega)
  rw [WRef.put_istate_lens hs] at st
  rw [st]
  simp only [Nat.zero_add]
  rfl

/-- `PInv` does not read `copy` or `len`. -/
theorem PInv.withCopy {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    {pr : Proto c r i window n} {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) (x y : UInt32) :
    PInv c pr h0 h { l with copy := x, len := y } log :=
  ⟨I.cstrm, I.cst, I.valid, I.winRoot, I.put, I.chunk, I.held, I.bits, I.proto, I.frame, I.live, I.mode⟩

theorem trCopyBody_run (c : BCtx) {i : Nat} (hc : c.st = some (.tab i)) {h : Heap} {s : InflateState}
    (hs : h.istates i = some s) (lt : s.«have».toNat < 320) (size : s.lens.size = 320) (l : IL) :
    runX (trCopyBody c) l h = .ok ((.ok (), l), setI h i (rdSet s l.len.toUInt16)) := by
  obtain ⟨add, st⟩ := lens_at hs lt size l.len.toUInt16
  have ld : ldInflateState (some (.tab i)) h = .ok (s, h) := ldInflateState_tab hs
  have hsL : (setI h i { s with lens := s.lens.set! s.«have».toNat l.len.toUInt16 }).istates i =
      some { s with lens := s.lens.set! s.«have».toNat l.len.toUInt16 } := by simp [setI]
  have wr := wrS_tab hsL (fun s => { s with «have» := s.«have» + 1 })
  unfold trCopyBody
  rw [hc]
  simp only [runX_bind, runX_lift_ok ld, lensP, runX_lift_ok add, runX_get, runX_lift_ok st, runX_lift_ok wr,
    setI_setI]
  rfl

/-- **The repeat loop on the invariant**: `copy` entries of `len` at `lens[have ..]`. -/
theorem trCopy_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (rd : RdSt i s)
    (fit : s.«have».toNat + l.copy.toNat ≤ s.nlen.toNat + s.ndist.toNat) (len15 : l.len.toNat ≤ 15) :
    ∃ x h', runX (xwhile trCopyCond (trCopyBody c)) l h = .ok ((.ok (), { l with copy := x }), h') ∧
      PInv c pr h0 h' l log ∧ ∃ s', h'.istates i = some s' ∧ RdSt i s' ∧
        s'.«have».toNat = s.«have».toNat + l.copy.toNat := by
  have v15 : l.len.toUInt16.toNat ≤ 15 := by rw [UInt32.toNat_toUInt16]; omega
  have key := xwhileBrk_wf (cond := trCopyCond) (body := (do trCopyBody c; pure false : X Bool))
    (fun l1 h1 => ∃ x s1, l1 = { l with copy := x } ∧ PInv c pr h0 h1 l log ∧ h1.istates i = some s1 ∧
      RdSt i s1 ∧ s1.nlen = s.nlen ∧ s1.ndist = s.ndist ∧ s1.«have».toNat + x.toNat = s.«have».toNat + l.copy.toNat)
    (fun res l1 h1 => res = .ok () ∧ (∃ x, l1 = { l with copy := x }) ∧ PInv c pr h0 h1 l log ∧
      ∃ s1, h1.istates i = some s1 ∧ RdSt i s1 ∧ s1.«have».toNat = s.«have».toNat + l.copy.toNat)
    (fun l1 _ => l1.copy.toNat)
    (fun l1 h1 hI => by
      obtain ⟨x, s1, rfl, I1, hs1, rd1, nl, nd, sum⟩ := hI
      have hcond : runX trCopyCond { l with copy := x } h1 =
          .ok ((.ok (x != 0), { l with copy := x - 1 }), h1) := by
        unfold trCopyCond; simp only [runX_bind, runX_get, runX_set]; rfl
      refine ⟨_, h1, _, hcond, fun hT => ?_, fun hF => ?_⟩
      · have ne : x ≠ 0 := by simpa using hT
        have pos : 0 < x.toNat := Nat.pos_of_ne_zero (fun e => ne (UInt32.toNat_inj.mp (by rw [e]; rfl)))
        obtain ⟨z1, s2, valid1, -, -⟩ := I1.valid
        have e2 : s2 = s1 := Option.some.inj (valid1.2.1.symm.trans hs1)
        subst e2
        have wf := valid1.2.2.2.2.2.1
        have lt : s2.«have».toNat < s2.nlen.toNat + s2.ndist.toNat := by rw [nl, nd]; omega
        have l320 : s2.«have».toNat < 320 := by have := rd1.tab.nlen; have := rd1.tab.ndist; omega
        have run := trCopyBody_run c I1.cst hs1 l320 wf.1 { l with copy := x - 1 }
        have IF := I1.setState hs1 (rdSet s2 l.len.toUInt16) rfl rfl rfl
          ⟨by simp [rdSet, wf.1], wf.2.1, wf.2.2⟩ (modeOk_of (Or.inr (Or.inl rd1.tab.mode)))
        have sub : (x - 1).toNat = x.toNat - 1 :=
          UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))
        refine ⟨.ok false, { l with copy := x - 1 }, setI h1 i (rdSet s2 l.len.toUInt16), by rw [runX_bind, run]; rfl,
          ⟨x - 1, rdSet s2 l.len.toUInt16, rfl, IF, by simp [setI], rdSet_st rd1 lt wf.1 v15, nl, nd, ?_⟩, ?_⟩
        · rw [rdSet_have l320, sub]; omega
        · show (x - 1).toNat < x.toNat; omega
      · have z : x = 0 := by simpa using hF
        have z' : x.toNat = 0 := by rw [z]; rfl
        exact ⟨rfl, ⟨_, rfl⟩, I1, s1, hs1, rd1, by omega⟩)
    (l := l) (h := h) ⟨l.copy, s, rfl, I, hs, rd, rfl, rfl, rfl⟩ (by have := UInt32.toNat_lt l.copy; unfold fuel; omega)
  obtain ⟨res, l', h', hr, rfl, ⟨x, rfl⟩, I', s', hs', rd', hv'⟩ := key
  exact ⟨x, h', by unfold xwhile; exact hr, I', s', hs', rd', hv'⟩

/-- **After a repeat code, on the invariant**: a repeat past `nlen + ndist` gives `BAD` (the loop
breaks); otherwise `copy ≥ 3` entries are stored. -/
theorem trTail_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (rd : RdSt i s) (len15 : l.len.toNat ≤ 15)
    (c3 : 3 ≤ l.copy.toNat) (c138 : l.copy.toNat ≤ 138) :
    ∃ res l' h', runX (trTail c) l h = .ok ((.ok res, l'), h') ∧ PInv c pr h0 h' l' log ∧
      l'.bits = l.bits ∧ l'.have_ = l.have_ ∧ ∃ s', h'.istates i = some s' ∧
        ((res = true ∧ s'.mode = BAD) ∨ (res = false ∧ RdSt i s' ∧ s.«have».toNat < s'.«have».toNat)) := by
  have ld : ldInflateState c.st h = .ok (s, h) := by rw [I.cst]; exact ldInflateState_tab hs
  have n1 := rd.tab.nlen
  have n2 := rd.tab.ndist
  have le := rd.le
  have sum : (s.«have» + l.copy).toNat = s.«have».toNat + l.copy.toNat := by
    rw [UInt32.toNat_add]; omega
  have nsum : (s.nlen + s.ndist).toNat = s.nlen.toNat + s.ndist.toNat := by
    rw [UInt32.toNat_add]; omega
  by_cases big : s.«have» + l.copy > s.nlen + s.ndist
  · obtain ⟨h', bad, I', -, s', hs', mode'⟩ := I.badRound "invalid bit length repeat" lit_bit_length_repeat
    refine ⟨true, l, h', ?_, I', rfl, rfl, s', hs', Or.inl ⟨rfl, mode'⟩⟩
    unfold trTail
    simp only [runX_bind, runX_lift_ok ld, runX_get, big, ↓reduceIte, runX_lift_ok bad]
    rfl
  · have fit : s.«have».toNat + l.copy.toNat ≤ s.nlen.toNat + s.ndist.toNat := by
      have hn : ¬ (s.nlen + s.ndist).toNat < (s.«have» + l.copy).toNat := fun x => big (UInt32.lt_iff_toNat_lt.mpr x)
      omega
    obtain ⟨x, h', run, I', s', hs', rd', hv'⟩ := trCopy_p c pr I hs rd fit len15
    refine ⟨false, { l with copy := x }, h', ?_, I'.withCopy x l.len, rfl, rfl, s', hs', Or.inr ⟨rfl, rd', by omega⟩⟩
    unfold trTail
    simp only [runX_bind, runX_lift_ok ld, runX_get, big, ↓reduceIte, run]
    rfl

/-- **A length below 16, on the invariant**: stored at `lens[have]`. -/
theorem trLit_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (rd : RdSt i s)
    (lt : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) {here : Code} (hv : here.val.toNat < 16)
    (hb : here.bits.toNat ≤ l.bits.toNat) :
    ∃ l' h', runX (trLit c here) l h = .ok ((.ok false, l'), h') ∧ PInv c pr h0 h' l' log ∧
      l'.have_ = l.have_ ∧ l'.bits.toNat ≤ l.bits.toNat ∧
      ∃ s', h'.istates i = some s' ∧ RdSt i s' ∧ s.«have».toNat < s'.«have».toNat := by
  obtain ⟨z, s0, valid, -, -⟩ := I.valid
  have e0 : s0 = s := Option.some.inj (valid.2.1.symm.trans hs)
  subst e0
  have wf := valid.2.2.2.2.2.1
  have l320 : s0.«have».toNat < 320 := by have := rd.tab.nlen; have := rd.tab.ndist; omega
  obtain ⟨add, st⟩ := lens_at hs l320 wf.1 here.val
  have ld : ldInflateState (some (.tab i)) h = .ok (s0, h) := ldInflateState_tab hs
  have hsL : (setI h i { s0 with lens := s0.lens.set! s0.«have».toNat here.val }).istates i =
      some { s0 with lens := s0.lens.set! s0.«have».toNat here.val } := by simp [setI]
  have wr := wrS_tab hsL (fun s => { s with «have» := s.«have» + 1 })
  have b8 : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; have := I.bits.1; omega
  have IF := I.setState hs (rdSet s0 here.val) rfl rfl rfl ⟨by simp [rdSet, wf.1], wf.2.1, wf.2.2⟩
    (modeOk_of (Or.inr (Or.inl rd.tab.mode)))
  obtain ⟨B2, -, hbit2⟩ := DROPBITS_inv (bitInv_of IF) here.bits.toUInt32 (by rw [UInt8.toNat_toUInt32]; exact hb) b8
  have IG := IF.regs (l' := { l with hold := l.hold >>> here.bits.toUInt32.toUInt64, bits := l.bits - here.bits.toUInt32 })
    rfl rfl rfl rfl (by show (l.bits - here.bits.toUInt32).toNat ≤ 39; rw [hbit2]; have := I.bits.1; omega) B2.hold_lt
  refine ⟨_, _, ?_, IG, rfl, by show (l.bits - here.bits.toUInt32).toNat ≤ _; rw [hbit2]; omega, rdSet s0 here.val,
    by simp [setI], rdSet_st rd lt wf.1 (by omega), by rw [rdSet_have l320]; omega⟩
  unfold trLit
  rw [I.cst]
  simp only [runX_bind, DROPBITS_run _ _ _ b8, runX_lift_ok ld, lensP, runX_lift_ok add, runX_lift_ok st,
    runX_lift_ok wr, setI_setI]
  rfl

/-- `DROPBITS(k)` on the registers. -/
def dropR (l : IL) (k : UInt32) : IL := { l with hold := l.hold >>> k.toUInt64, bits := l.bits - k }

/-- `BITS(k)`. -/
def bitsV (l : IL) (k : UInt32) : UInt32 := l.hold.toUInt32 &&& ((1 : UInt32) <<< k - 1)

theorem dropR_bits {l : IL} {k : UInt32} (hk : k.toNat ≤ l.bits.toNat) :
    (dropR l k).bits.toNat = l.bits.toNat - k.toNat :=
  UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hk)

theorem bitsV_lt (l : IL) {k : UInt32} (hk : k.toNat < 32) : (bitsV l k).toNat < 2 ^ k.toNat := by
  unfold bitsV
  rw [BITS_toNat l k hk]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The end of a repeat code: `BITS(m)`, the registers `len` and `copy`, `DROPBITS(m)`, then
`trTail`. The bits for it are held. -/
theorem repEnd_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (rd : RdSt i s) (m base len : UInt32)
    (hm : m.toNat ≤ l.bits.toNat) (m7 : m.toNat ≤ 7) (len15 : len.toNat ≤ 15) (lo : 3 ≤ base.toNat)
    (hi : base.toNat + 2 ^ m.toNat ≤ 139) :
    ∃ res l' h', runX (trTail c) (dropR { l with len := len, copy := base + bitsV l m } m) h =
        .ok ((.ok res, l'), h') ∧ PInv c pr h0 h' l' log ∧ baseM pr l' log ≤ baseM pr l log ∧
      ∃ s', h'.istates i = some s' ∧
        ((res = true ∧ s'.mode = BAD) ∨ (res = false ∧ RdSt i s' ∧ s.«have».toNat < s'.«have».toNat)) := by
  have B0 := bitInv_of I
  have B : BitInv h { l with len := len, copy := base + bitsV l m } (log.held.drop (log.held.length - l.have_.toNat)) :=
    ⟨B0.have_eq, B0.next, B0.hold_lt⟩
  obtain ⟨B5, -, -⟩ := DROPBITS_inv B m hm (by omega)
  have b5 : (dropR { l with len := len, copy := base + bitsV l m } m).bits.toNat = l.bits.toNat - m.toNat :=
    dropR_bits (l := { l with len := len, copy := base + bitsV l m }) hm
  have I5 := (I.withCopy (base + bitsV l m) len).regs (l' := dropR { l with len := len, copy := base + bitsV l m } m)
    rfl rfl rfl rfl (by rw [b5]; have := I.bits.1; omega) B5.hold_lt
  have bv := bitsV_lt l (k := m) (by omega)
  have cp : (base + bitsV l m).toNat = base.toNat + (bitsV l m).toNat := by
    rw [UInt32.toNat_add]; omega
  obtain ⟨res, l6, h6, run6, I6, bits6, have6, s', hs', out⟩ :=
    trTail_p c pr I5 hs rd len15 (by show 3 ≤ (base + bitsV l m).toNat; omega)
      (by show (base + bitsV l m).toNat ≤ 138; omega)
  refine ⟨res, l6, h6, run6, I6, ?_, s', hs', out⟩
  unfold baseM
  rw [bits6, have6, b5]
  show 4 * (l.bits.toNat - m.toNat + 8 * l.have_.toNat + _) ≤ _
  omega

set_option maxRecDepth 100000 in
/-- **A repeat code, on the invariant.** -/
theorem trRep_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (rd : RdSt i s) {here : Code}
    (hb : here.bits.toNat ≤ l.bits.toNat) (h7 : here.bits.toNat ≤ 7) :
    ∃ res l' h' log', runX (trRep c here) l h = .ok ((res, l'), h') ∧ PInv c pr h0 h' l' log' ∧
      (∀ b, res = .ok b → baseM pr l' log' ≤ baseM pr l log ∧ ∃ s', h'.istates i = some s' ∧
          ((b = true ∧ s'.mode = BAD) ∨ (b = false ∧ RdSt i s' ∧ s.«have».toNat < s'.«have».toNat))) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) := by
  have hb8 : here.bits.toUInt32.toNat = here.bits.toNat := UInt8.toNat_toUInt32 _
  have b64 : here.bits.toUInt32.toNat < 64 := by omega
  have need : ∀ m : UInt32, m.toNat ≤ 7 → ∃ res2 l2 h2 log2,
      runX (NEEDBITS c (here.bits.toUInt32 + m)) l h = .ok ((res2, l2), h2) ∧ PInv c pr h0 h2 l2 log2 ∧
      h2.istates i = some s ∧ baseM pr l2 log2 ≤ baseM pr l log ∧
      (res2 = .ok () → here.bits.toNat + m.toNat ≤ l2.bits.toNat) ∧
      (∀ e, res2 = .error e → e = Ex.leave ∧ l2.ret = Z_BUF_ERROR) := by
    intro m m7
    have k : (here.bits.toUInt32 + m).toNat = here.bits.toNat + m.toNat := by rw [UInt32.toNat_add, hb8]; omega
    obtain ⟨res2, l2, h2, log2, run2, I2, okc, errc, ist2, meas2⟩ :=
      NEEDBITS_p c pr (here.bits.toUInt32 + m) (by rw [k]; omega) I
    exact ⟨res2, l2, h2, log2, run2, I2, ist2.trans hs, baseM_le meas2, fun e => by rw [← k]; exact (okc e).1, errc⟩
  -- after `NEEDBITS` and `DROPBITS(here.bits)`
  have drop : ∀ {h2 : Heap} {l2 : IL} {log2 : BackLog}, PInv c pr h0 h2 l2 log2 → here.bits.toNat ≤ l2.bits.toNat →
      PInv c pr h0 h2 (dropR l2 here.bits.toUInt32) log2 ∧
      (dropR l2 here.bits.toUInt32).bits.toNat = l2.bits.toNat - here.bits.toNat ∧
      baseM pr (dropR l2 here.bits.toUInt32) log2 ≤ baseM pr l2 log2 := by
    intro h2 l2 log2 I2 hb2
    obtain ⟨B3, -, -⟩ := DROPBITS_inv (bitInv_of I2) here.bits.toUInt32 (by omega) b64
    have e3 : (dropR l2 here.bits.toUInt32).bits.toNat = l2.bits.toNat - here.bits.toNat := by
      rw [dropR_bits (by omega), hb8]
    refine ⟨I2.regs rfl rfl rfl rfl (by rw [e3]; have := I2.bits.1; omega) B3.hold_lt, e3, ?_⟩
    unfold baseM
    rw [e3]
    show 4 * (l2.bits.toNat - here.bits.toNat + 8 * l2.have_.toNat + _) ≤ _
    omega
  have done : ∀ {res : Bool} {l6 h6 : Heap → Prop}, True := fun {_ _ _} => trivial
  clear done
  by_cases v16 : (here.val == 16) = true
  · obtain ⟨res2, l2, h2, log2, run2, I2, hs2, b2, okc, errc⟩ := need 2 (by decide)
    cases res2 with
    | error e =>
      obtain ⟨rfl, ret⟩ := errc e rfl
      refine ⟨.error Ex.leave, l2, h2, log2, ?_, I2, fun b x => (nomatch x), fun e x => ?_⟩
      · unfold trRep
        simp only [v16, ↓reduceIte, runX_bind, run2]
      · injection x with x; subst x; exact ⟨rfl, ret⟩
    | ok u =>
      cases u
      have k2 : here.bits.toNat + 2 ≤ l2.bits.toNat := okc rfl
      obtain ⟨I3, e3, b3⟩ := drop I2 (by omega)
      have ld : ldInflateState (some (.tab i)) h2 = .ok (s, h2) := ldInflateState_tab hs2
      by_cases z : (s.«have» == 0) = true
      · obtain ⟨h', bad, I', m, s', hs', mode'⟩ := I3.badRound "invalid bit length repeat" lit_bit_length_repeat
        refine ⟨.ok true, dropR l2 here.bits.toUInt32, h', log2, ?_, I',
          fun b x => ⟨by omega, s', hs', Or.inl ⟨by injection x with x; exact x.symm, mode'⟩⟩, fun e x => (nomatch x)⟩
        unfold trRep
        simp only [v16, ↓reduceIte, runX_bind, run2, DROPBITS_run _ _ _ b64, I2.cst, runX_lift_ok ld, z,
          runX_lift_ok bad]
        rfl
      · have z' : s.«have» ≠ 0 := by simpa using z
        have hpos : 0 < s.«have».toNat := Nat.pos_of_ne_zero (fun e => z' (UInt32.toNat_inj.mp (by rw [e]; rfl)))
        obtain ⟨z1, s1, valid1, -, -⟩ := I2.valid
        have e1 : s1 = s := Option.some.inj (valid1.2.1.symm.trans hs2)
        subst e1
        have wf := valid1.2.2.2.2.2.1
        have sub : (s1.«have» - 1).toNat = s1.«have».toNat - 1 :=
          UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (by simp; omega))
        have l320 : s1.«have».toNat ≤ 316 := by have := rd.le; have := rd.tab.nlen; have := rd.tab.ndist; omega
        have inside : 0 + (s1.«have» - 1).toNat < s1.lens.size := by rw [wf.1, sub]; omega
        have read0 := Ptr.index_ok (off := 0) (i := (s1.«have» - 1).toNat) (WRef.get_istate_lens hs2) inside
        have val : s1.lens[0 + (s1.«have» - 1).toNat] = s1.lens.getD (s1.«have» - 1).toNat 0 := by
          simp only [Nat.zero_add, Array.getD_eq_getD_getElem?]
          rw [Array.getElem?_eq_getElem (by rw [wf.1, sub]; omega)]
          rfl
        rw [val] at read0
        have len15 : (s1.lens.getD (s1.«have» - 1).toNat 0).toUInt32.toNat ≤ 15 := by
          rw [UInt16.toNat_toUInt32]; exact rd.rl _ (by rw [sub]; omega)
        obtain ⟨res, l6, h6, run6, I6, b6, s', hs', out⟩ :=
          repEnd_p c pr I3 hs2 rd 2 3 (s1.lens.getD (s1.«have» - 1).toNat 0).toUInt32
            (by rw [e3]; show 2 ≤ _; omega) (by decide) len15 (by decide) (by decide)
        refine ⟨.ok res, l6, h6, log2, ?_, I6, fun b x => ?_, fun e x => (nomatch x)⟩
        · unfold trRep
          simp only [v16, ↓reduceIte, runX_bind, run2, DROPBITS_run _ _ _ b64, I2.cst, runX_lift_ok ld, z,
            Bool.false_eq_true, lensP, runX_lift_ok read0, BITS_run _ _ 2 (by decide), runX_modify,
            DROPBITS_run _ _ 2 (by decide)]
          exact run6
        · injection x with x
          subst x
          exact ⟨by omega, s', hs', out⟩
  · have v16' : (here.val == 16) = false := by simpa using v16
    by_cases v17 : (here.val == 17) = true
    · obtain ⟨res2, l2, h2, log2, run2, I2, hs2, b2, okc, errc⟩ := need 3 (by decide)
      cases res2 with
      | error e =>
        obtain ⟨rfl, ret⟩ := errc e rfl
        refine ⟨.error Ex.leave, l2, h2, log2, ?_, I2, fun b x => (nomatch x), fun e x => ?_⟩
        · unfold trRep
          simp only [v16', v17, Bool.false_eq_true, ↓reduceIte, runX_bind, run2]
        · injection x with x; subst x; exact ⟨rfl, ret⟩
      | ok u =>
        cases u
        have k2 : here.bits.toNat + 3 ≤ l2.bits.toNat := okc rfl
        obtain ⟨I3, e3, b3⟩ := drop I2 (by omega)
        obtain ⟨res, l6, h6, run6, I6, b6, s', hs', out⟩ :=
          repEnd_p c pr I3 hs2 rd 3 3 0 (by rw [e3]; show 3 ≤ _; omega) (by decide) (by decide) (by decide)
            (by decide)
        refine ⟨.ok res, l6, h6, log2, ?_, I6, fun b x => ?_, fun e x => (nomatch x)⟩
        · unfold trRep
          simp only [v16', v17, Bool.false_eq_true, ↓reduceIte, runX_bind, run2, DROPBITS_run _ _ _ b64,
            BITS_run _ _ 3 (by decide), runX_modify, DROPBITS_run _ _ 3 (by decide)]
          exact run6
        · injection x with x
          subst x
          exact ⟨by omega, s', hs', out⟩
    · have v17' : (here.val == 17) = false := by simpa using v17
      obtain ⟨res2, l2, h2, log2, run2, I2, hs2, b2, okc, errc⟩ := need 7 (by decide)
      cases res2 with
      | error e =>
        obtain ⟨rfl, ret⟩ := errc e rfl
        refine ⟨.error Ex.leave, l2, h2, log2, ?_, I2, fun b x => (nomatch x), fun e x => ?_⟩
        · unfold trRep
          simp only [v16', v17', Bool.false_eq_true, ↓reduceIte, runX_bind, run2]
        · injection x with x; subst x; exact ⟨rfl, ret⟩
      | ok u =>
        cases u
        have k2 : here.bits.toNat + 7 ≤ l2.bits.toNat := okc rfl
        obtain ⟨I3, e3, b3⟩ := drop I2 (by omega)
        obtain ⟨res, l6, h6, run6, I6, b6, s', hs', out⟩ :=
          repEnd_p c pr I3 hs2 rd 7 11 0 (by rw [e3]; show 7 ≤ _; omega) (by decide) (by decide) (by decide)
            (by decide)
        refine ⟨.ok res, l6, h6, log2, ?_, I6, fun b x => ?_, fun e x => (nomatch x)⟩
        · unfold trRep
          simp only [v16', v17', Bool.false_eq_true, ↓reduceIte, runX_bind, run2, DROPBITS_run _ _ _ b64,
            BITS_run _ _ 7 (by decide), runX_modify, DROPBITS_run _ _ 7 (by decide)]
          exact run6
        · injection x with x
          subst x
          exact ⟨by omega, s', hs', out⟩

/-- **The decoding loop of `case TABLE` on the invariant**, measured by `316 - have`. -/
theorem tabRead_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (rd : RdSt i s) :
    ∃ res l' h' log', runX (tabRead c) l h = .ok ((res, l'), h') ∧ PInv c pr h0 h' l' log' ∧
      (res = .ok () → baseM pr l' log' ≤ baseM pr l log ∧ ∃ s', h'.istates i = some s' ∧
        (s'.mode = BAD ∨ (RdSt i s' ∧ s'.«have».toNat = s'.nlen.toNat + s'.ndist.toNat))) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) := by
  have key := xwhileBrk_wf (cond := trCond c) (body := (do Zlib.Infback.lookup1 c false; trAfter c : X Bool))
    (fun l1 h1 => ∃ log1 s1, PInv c pr h0 h1 l1 log1 ∧ h1.istates i = some s1 ∧ RdSt i s1 ∧
      baseM pr l1 log1 ≤ baseM pr l log)
    (fun res l1 h1 => ∃ log1, PInv c pr h0 h1 l1 log1 ∧
      (res = .ok () → baseM pr l1 log1 ≤ baseM pr l log ∧ ∃ s1, h1.istates i = some s1 ∧
        (s1.mode = BAD ∨ (RdSt i s1 ∧ s1.«have».toNat = s1.nlen.toNat + s1.ndist.toNat))) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l1.ret = Z_BUF_ERROR))
    (fun _ h1 => tabGap i (fun _ => 316) h1)
    (fun l1 h1 hI => by
      obtain ⟨log1, s1, I1, hs1, rd1, b1⟩ := hI
      have ld1 : ldInflateState c.st h1 = .ok (s1, h1) := by rw [I1.cst]; exact ldInflateState_tab hs1
      have hcond : runX (trCond c) l1 h1 = .ok ((.ok (decide (s1.«have» < s1.nlen + s1.ndist)), l1), h1) := by
        unfold trCond; rw [runX_bind, runX_lift_ok ld1]; rfl
      have n1 := rd1.tab.nlen
      have n2 := rd1.tab.ndist
      have nsum : (s1.nlen + s1.ndist).toNat = s1.nlen.toNat + s1.ndist.toNat := by
        rw [UInt32.toNat_add]; omega
      refine ⟨l1, h1, _, hcond, fun hT => ?_, fun hF => ?_⟩
      · have lt : s1.«have».toNat < s1.nlen.toNat + s1.ndist.toNat := by
          have := UInt32.lt_iff_toNat_lt.mp (of_decide_eq_true hT); omega
        obtain ⟨tab, safe⟩ := rd1.rd
        have root7 := safe.2.1
        obtain ⟨res2, l2, h2, log2, run2, I2, ist2, okc, errc, meas2⟩ :=
          lookup1_p c pr false I1 hs1 (ref := .istate_codes i) (off := 0) (ca := s1.codes) (nb := s1.lenbits)
            tab rfl (Or.inl rfl) (CodeRef.get_istate_codes hs1) (by omega) safe.2.2.1
            (fun j hj => by have := (safe.2.2.2 j hj).2.1; omega)
        have b2 := baseM_le meas2
        have hs2 : h2.istates i = some s1 := ist2.trans hs1
        cases res2 with
        | error e =>
          obtain ⟨rfl, ret⟩ := errc e rfl
          exact ⟨.error Ex.leave, l2, h2, by rw [runX_bind, run2], log2, I2, fun x => (nomatch x),
            fun e x => by injection x with x; subst x; exact ⟨rfl, ret⟩⟩
        | ok u =>
          cases u
          obtain ⟨-, -, ⟨j, hj, hhere⟩, hbits⟩ := okc rfl
          have h7 : l2.here.bits.toNat ≤ 7 := by rw [hhere]; have := (safe.2.2.2 j hj).2.1; omega
          have pre : runX (do Zlib.Infback.lookup1 c false; trAfter c : X Bool) l1 h1 = runX (trAfter c) l2 h2 := by
            rw [runX_bind, run2]
          by_cases v : l2.here.val < 16
          · have pre2 : runX (trAfter c) l2 h2 = runX (trLit c l2.here) l2 h2 := by
              unfold trAfter; simp only [runX_bind, runX_get, v, ↓reduceIte]
            obtain ⟨l3, h3, run3, I3, have3, bits3, s', hs', rd', up⟩ :=
              trLit_p c pr I2 hs2 rd1 lt (UInt16.lt_iff_toNat_lt.mp v) hbits
            refine ⟨.ok false, l3, h3, by rw [pre, pre2, run3], ⟨log2, s', I3, hs', rd', ?_⟩, ?_⟩
            · unfold baseM at b1 b2 ⊢; rw [have3]; omega
            · show tabGap i (fun _ => 316) h3 < tabGap i (fun _ => 316) h1
              rw [tabGap_of hs', tabGap_of hs1]
              have := rd'.le; have := rd'.tab.nlen; have := rd'.tab.ndist
              omega
          · have pre2 : runX (trAfter c) l2 h2 = runX (trRep c l2.here) l2 h2 := by
              unfold trAfter; simp only [runX_bind, runX_get, v, ↓reduceIte]
            obtain ⟨res3, l3, h3, log3, run3, I3, okc3, errc3⟩ := trRep_p c pr I2 hs2 rd1 hbits h7
            cases res3 with
            | error e =>
              obtain ⟨rfl, ret⟩ := errc3 e rfl
              exact ⟨.error Ex.leave, l3, h3, by rw [pre, pre2, run3], log3, I3, fun x => (nomatch x),
                fun e x => by injection x with x; subst x; exact ⟨rfl, ret⟩⟩
            | ok b =>
              obtain ⟨b3, s', hs', out⟩ := okc3 b rfl
              rcases out with ⟨rfl, bad⟩ | ⟨rfl, rd', up⟩
              · exact ⟨.ok true, l3, h3, by rw [pre, pre2, run3], log3, I3,
                  fun _ => ⟨by omega, s', hs', Or.inl bad⟩, fun e x => (nomatch x)⟩
              · refine ⟨.ok false, l3, h3, by rw [pre, pre2, run3], ⟨log3, s', I3, hs', rd', by omega⟩, ?_⟩
                show tabGap i (fun _ => 316) h3 < tabGap i (fun _ => 316) h1
                rw [tabGap_of hs', tabGap_of hs1]
                have := rd'.le; have := rd'.tab.nlen; have := rd'.tab.ndist
                omega
      · have ge : ¬ s1.«have» < s1.nlen + s1.ndist := fun x => by simp [x] at hF
        have ge' : s1.nlen.toNat + s1.ndist.toNat ≤ s1.«have».toNat := by
          have hn : ¬ s1.«have».toNat < (s1.nlen + s1.ndist).toNat := fun x => ge (UInt32.lt_iff_toNat_lt.mpr x)
          omega
        exact ⟨log1, I1, fun _ => ⟨b1, s1, hs1, Or.inr ⟨rd1, by have := rd1.le; omega⟩⟩, fun e x => (nomatch x)⟩)
    (l := l) (h := h) ⟨log, s, I, hs, rd, Nat.le_refl _⟩
    (by rw [tabGap_of hs]; unfold fuel; omega)
  obtain ⟨res, l', h', hr, log', I', okc, errc⟩ := key
  exact ⟨res, l', h', log', by rw [tabRead_eq]; exact hr, I', okc, errc⟩

end Zlib.Infback.Safety
