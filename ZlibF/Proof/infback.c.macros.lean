import ZlibF.Proof.«infback.c.back»
import ZlibF.Proof.«inflate.c.main.macros»

/-!
# infback.c: the input macros with the call-back `in`

`PULL`, `PULLBYTE` and `NEEDBITS` of `inflateBack()`. The bit algebra (`BitInv`, `PULLBYTE_succ`, `BITS_run`, `DROPBITS_run`,
`BYTEBITS_run`) is the one of `inflate()` (module `inflate.c.main.macros`): `PULLBYTE` of `infback.c` differs only in that
`PULL` may call `in` when no input is left.

The registers describe the rest `bs` of the chunk that `in` returned last (`BIn`); the chunk is in a block of `in` (`ownI`),
so `out`, the writes into the window and the record tables cannot change it.
-/

namespace Zlib.Infback.Spec
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs

/-- The registers describe the bytes `bs` left of the current chunk (`BitInv`), and a non-empty chunk is in an `ownI` block. -/
structure BIn (ownI : Nat → Prop) (h : Heap) (l : IL) (bs : List UInt8) : Prop where
  bit : BitInv h l bs
  own : bs = [] ∨ ∃ b off, l.next = .ref (.blk b) off ∧ ownI b

/-- The input is finite: a measure `μ` of what `in` can still deliver (it depends only on the blocks of `in`), and a call that
returns `n` bytes lowers it by at least `n`. Without it `inflateBack` may run for ever: zlib.h does not promise that `in`
eventually reports the end of input, and the model then runs out of fuel. -/
structure InFinite (c : BCtx) (ownI : Nat → Prop) (R : Heap → Prop) (μ : Heap → Nat) : Prop where
  step : ∀ h nx n nx' h', R h → c.inCb c.inDesc nx h = .ok ((n, nx'), h') → μ h' + n.toNat ≤ μ h
  local_ : ∀ h h', (∀ b, ownI b → h'.bytes b = h.bytes b) → μ h' = μ h

/-- The input still to be read: the bits held, the bytes of the chunk, and what `in` can still deliver (in bits). -/
def phi (μ : Heap → Nat) (h : Heap) (l : IL) : Nat := l.bits.toNat + 8 * l.have_.toNat + 8 * μ h

end Zlib.Infback.Spec

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

theorem BIn.congr {ownI : Nat → Prop} {h h' : Heap} {l : IL} {bs : List UInt8}
    (hS : ∀ b, ownI b → h'.bytes b = h.bytes b) (B : BIn ownI h l bs) : BIn ownI h' l bs := by
  obtain ⟨⟨he, hn, hl⟩, ho⟩ := B
  refine ⟨⟨he, ?_, hl⟩, ho⟩
  rcases hn with e | ⟨r, a, off, hnx, hg, hsz, hbs⟩
  · exact Or.inl e
  · rcases ho with e | ⟨b, off', hb, hown⟩
    · exact Or.inl e
    · rw [hb] at hnx
      obtain ⟨h1, h2⟩ := Ptr.ref.inj hnx
      subst h1
      have hg' : h.bytes b = some a := hg
      refine Or.inr ⟨_, a, off, by rw [hb, h2], ?_, hsz, hbs⟩
      show h'.bytes b = some a
      rw [hS b hown, hg']

theorem CbFrame.trans {o : Nat → Prop} {h1 h2 h3 : Heap} (a : CbFrame o h1 h2) (b : CbFrame o h2 h3) : CbFrame o h1 h3 :=
  ⟨fun x hx => (b.bytes x hx).trans (a.bytes x hx), fun x => (b.live x).trans (a.live x),
   fun x => (b.words x).trans (a.words x), fun x => (b.ro x).trans (a.ro x), fun x => (b.streams x).trans (a.streams x),
   fun x => (b.gzheaders x).trans (a.gzheaders x), fun x => (b.dstates x).trans (a.dstates x),
   fun x => (b.istates x).trans (a.istates x), fun x => (b.gzstates x).trans (a.gzstates x),
   b.static.trans a.static, b.nextBlk.trans a.nextBlk, b.nalloc.trans a.nalloc, b.allocOk.trans a.allocOk,
   b.garbage.trans a.garbage⟩

/-- `PULL()` when input is left: nothing happens. -/
theorem PULL_have {c : BCtx} {l : IL} {h : Heap} (hne : l.have_ ≠ 0) :
    runX (PULL c) l h = .ok ((.ok (), l), h) := by
  have hb : (l.have_ == 0) = false := by simpa using hne
  unfold PULL
  simp [runX_bind, runX_get, hb, hne, runX_pure]

/-- `PULL()` with no input left and `in` returning a chunk of `n ≠ 0` bytes at `nx`. -/
theorem PULL_chunk {c : BCtx} {l : IL} {h h' : Heap} {n : UInt32} {nx : BPtr} (h0 : l.have_ = 0) (hn : n ≠ 0)
    (hin : c.inCb c.inDesc l.next h = .ok ((n, nx), h')) :
    runX (PULL c) l h = .ok ((.ok (), { l with have_ := n, next := nx }), h') := by
  have hb : (n == 0) = false := by simpa using hn
  unfold PULL
  simp [runX_bind, runX_get, h0, hin, runX_lift_ok, hb, hn, runX_set, runX_pure, runX_lift]

theorem PULL_noinput {c : BCtx} {l : IL} {h h' : Heap} {nx : BPtr} (h0 : l.have_ = 0)
    (hin : c.inCb c.inDesc l.next h = .ok ((0, nx), h')) :
    runX (PULL c) l h = .ok ((.error Ex.leave, { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }), h') :=
  PULL_eof h0 hin

theorem PULLBYTE_c_eq (c : BCtx) {l : IL} {h : Heap} (hne : l.have_ ≠ 0) :
    runX (Zlib.Infback.PULLBYTE c) l h = runX Zlib.Inflate.PULLBYTE l h := by
  have hb : (l.have_ == 0) = false := by simpa using hne
  unfold Zlib.Infback.PULLBYTE Zlib.Inflate.PULLBYTE
  simp only [runX_bind, PULL_have hne, runX_get, hb, Bool.false_eq_true, ↓reduceIte, runX_pure, runX_set, runX_lift]
  generalize load8 l.next h = r1
  rcases r1 with e | ⟨a1, h1⟩
  · rfl
  simp only []
  generalize Ptr.add l.next 1 h1 = r2
  rcases r2 with e | ⟨a2, h2⟩
  · rfl
  simp only []
  generalize shl64 a1.toUInt64 l.bits h2 = r3
  rcases r3 with e | ⟨a3, h3⟩ <;> rfl

/-- `PULLBYTE` of `inflate()` with its pointer made explicit. -/
theorem PULLBYTE_nx {h : Heap} {l : IL} {b : UInt8} {r : BRef} {off : Nat} {a : Array UInt8} (hne : l.have_ ≠ 0)
    (hnext : l.next = .ref r off) (hg : (Space.get h r : Option (Array UInt8)) = some a) (hlt : off < a.size)
    (hb : a[off] = b) (hbits : l.bits.toNat < 64) :
    runX Zlib.Inflate.PULLBYTE l h = .ok ((.ok (), pulled l b (.ref r (off + 1))), h) := by
  have hne' : (l.have_ == 0) = false := by simpa using hne
  have hadd : OkOn h (l.next.add 1) (.ref r (off + 1)) := by
    rw [hnext]; exact Ptr.add_nat_ok (n := 1) hg (by omega)
  have hld : OkOn h (load8 l.next) b := by
    rw [hnext]
    have := Ptr.load_ok (h := h) (r := r) (off := off) hg hlt
    rw [hb] at this; exact this
  have hshl : shl64 b.toUInt64 l.bits h = .ok (b.toUInt64 <<< l.bits.toUInt64, h) := by
    rw [shl64_run _ _ hbits]; rfl
  unfold Zlib.Inflate.PULLBYTE
  rw [runX_bind, runX_get]
  simp only [hne', Bool.false_eq_true, ↓reduceIte]
  simp only [runX_bind, runX_set, runX_lift_ok hld, runX_lift_ok hadd, runX_lift_ok hshl]
  rfl

/-- `PULLBYTE` with input left in an `in` chunk: one byte moves into the bit buffer; the chunk stays in its block. -/
theorem PULLBYTE_have (c : BCtx) {ownI : Nat → Prop} {h : Heap} {l : IL} {b : UInt8} {rest : List UInt8}
    (B : BIn ownI h l (b :: rest)) (hb : l.bits.toNat ≤ 56) :
    ∃ nx, runX (Zlib.Infback.PULLBYTE c) l h = .ok ((.ok (), pulled l b nx), h) ∧ BIn ownI h (pulled l b nx) rest ∧
      (pulled l b nx).bits.toNat = l.bits.toNat + 8 := by
  have hne0 : l.have_ ≠ 0 := fun e => by have := B.bit.have_eq; rw [e] at this; simp at this
  obtain ⟨nx, hrun, hB2, -, hbits⟩ := PULLBYTE_succ B.bit hb
  refine ⟨nx, by rw [PULLBYTE_c_eq c hne0]; exact hrun, ?_, hbits⟩
  refine ⟨hB2, ?_⟩
  obtain ⟨bb, off0, hnx0, hown⟩ := B.own.resolve_left (by simp)
  obtain ⟨r, a, off, hnext, hg, hsz, hbs⟩ := B.bit.next.resolve_left (by simp)
  rw [hnx0] at hnext
  obtain ⟨h1, h2⟩ := Ptr.ref.inj hnext
  subst h1; subst h2
  have hsz' : off0 + rest.length + 1 ≤ a.size := by simp at hsz; omega
  have hbs' : b :: rest = a[off0] :: (a.toList.drop (off0 + 1)).take rest.length := by
    have := take_succ_drop a off0 rest.length hsz'
    simp only [List.length_cons] at hbs
    rw [← this]; exact hbs
  have hbb : a[off0] = b := by injection hbs' with h1; exact h1.symm
  have hrun2 := PULLBYTE_nx (b := b) hne0 hnx0 hg (by omega) hbb (by omega)
  rw [hrun] at hrun2
  have hnx : pulled l b nx = pulled l b (.ref (.blk bb) (off0 + 1)) := by
    simpa using hrun2
  right
  refine ⟨bb, off0 + 1, ?_, hown⟩
  rw [hnx]; rfl

/-- The registers after a successful `PULLBYTE`/`NEEDBITS`: only `next`, `have`, `hold`, `bits` differ. -/
def InShape (l l' : IL) : Prop := l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits }

/-- The registers after the end of input: `next = NULL`, `have = 0`, `ret = Z_BUF_ERROR`. -/
def EofRegs (l : IL) : IL := { l with have_ := 0, next := .null, ret := Z_BUF_ERROR }

/-- **`PULLBYTE` with the call-back.** Under `CbContract`, with at most 56 bits held: no fault, and either one byte is pulled
(`ok`: `bits` grows by 8, only the input registers change, `in` was called only if the chunk was used up) or `goto inf_leave`
with `Z_BUF_ERROR` (`in` returned 0: `next = NULL`, `have = 0`). The call-back changed only its own blocks; `R` holds
again; the registers describe the new chunk. -/
theorem PULLBYTE_run (c : BCtx) {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {μ : Heap → Nat} (hF : InFinite c ownI R μ)
    {h : Heap} {l : IL} {bs : List UInt8}
    (B : BIn ownI h l bs) (hR : R h) (hb : l.bits.toNat ≤ 56) :
    ∃ r l' h' bs', runX (Zlib.Infback.PULLBYTE c) l h = .ok ((r, l'), h') ∧ CbFrame ownI h h' ∧ R h' ∧
      BIn ownI h' l' bs' ∧
      (r = .ok () → l'.bits.toNat = l.bits.toNat + 8 ∧ InShape l l') ∧
      (r = .error Ex.leave → l' = EofRegs l) ∧ (∀ e, r = .error e → e = Ex.leave) ∧
      phi μ h' l' ≤ phi μ h l := by
  by_cases hz : l.have_ = 0
  · have hbs : bs = [] := by
      have := B.bit.have_eq; rw [hz] at this
      exact List.eq_nil_of_length_eq_zero (by simpa using this.symm)
    obtain ⟨n, nx, h', he, fr, hR', hbuf⟩ := hK.inOk h l.next hR
    by_cases hn : n = 0
    · subst hn
      refine ⟨.error Ex.leave, EofRegs l, h', [], ?_, fr, hR', ⟨⟨by simp [EofRegs], Or.inl rfl, B.bit.hold_lt⟩, Or.inl rfl⟩,
        (fun e => by cases e), fun _ => rfl, (fun e he => by cases he; rfl), ?_⟩
      · unfold Zlib.Infback.PULLBYTE
        rw [runX_bind, PULL_noinput hz he]
        rfl
      · have hs := hF.step h l.next 0 nx h' hR he
        have hz0 : l.have_.toNat = 0 := by rw [hz]; rfl
        simp only [phi, EofRegs]
        simp only [UInt32.toNat_zero] at hs ⊢
        omega
    · obtain ⟨bb, off, a, hnx, hown, ha, hle⟩ := hbuf hn
      have hn1 : ({ l with have_ := n, next := nx } : IL).have_ ≠ 0 := hn
      let bsc := (a.toList.drop off).take n.toNat
      have hlen : bsc.length = n.toNat := by simp [bsc]; omega
      have hB1 : BIn ownI h' { l with have_ := n, next := nx } bsc :=
        ⟨⟨hlen.symm, Or.inr ⟨.blk bb, a, off, by simp [hnx], ha, by omega, by rw [hlen]⟩, B.bit.hold_lt⟩,
          Or.inr ⟨bb, off, by simp [hnx], hown⟩⟩
      have e1 : runX (Zlib.Infback.PULLBYTE c) l h = runX (Zlib.Infback.PULLBYTE c) { l with have_ := n, next := nx } h' := by
        unfold Zlib.Infback.PULLBYTE
        simp only [runX_bind, PULL_chunk hz hn he, PULL_have hn1]
      have hne : bsc ≠ [] := fun e => hn (by
        have : n.toNat = 0 := by rw [← hlen, e]; rfl
        exact UInt32.toNat_inj.mp (by simpa using this))
      obtain ⟨b0, rest, hbc⟩ : ∃ b0 rest, bsc = b0 :: rest := by
        cases hh : bsc with
        | nil => exact absurd hh hne
        | cons x y => exact ⟨x, y, rfl⟩
      rw [hbc] at hB1
      obtain ⟨nx', hrun, hB2, hbits⟩ := PULLBYTE_have c hB1 (by simpa using hb)
      refine ⟨.ok (), _, h', rest, by rw [e1]; exact hrun, fr, hR', hB2, fun _ => ⟨by simpa using hbits, rfl⟩,
        (fun e => by cases e), (fun e he => by cases he), ?_⟩
      have hs := hF.step h l.next n nx h' hR he
      have h1 := hB2.bit.have_eq
      have hz0 : l.have_.toNat = 0 := by rw [hz]; rfl
      rw [hbc] at hlen
      simp only [phi]
      simp only [pulled, List.length_cons] at hlen h1 hbits ⊢
      omega
  · have hbs : ∃ b rest, bs = b :: rest := by
      cases hh : bs with
      | nil => exact absurd (by have := B.bit.have_eq; rw [hh] at this; exact UInt32.toNat_inj.mp (by simpa using this)) hz
      | cons x y => exact ⟨x, y, rfl⟩
    obtain ⟨b0, rest, rfl⟩ := hbs
    obtain ⟨nx, hrun, hB2, hbits⟩ := PULLBYTE_have c B hb
    refine ⟨.ok (), _, h, rest, hrun, CbFrame.refl _ _, hR, hB2, fun _ => ⟨hbits, rfl⟩, (fun e => by cases e),
      (fun e he => by cases he), ?_⟩
    have h1 := hB2.bit.have_eq
    have h0 := B.bit.have_eq
    simp only [phi]
    simp only [pulled, List.length_cons] at h0 h1 hbits ⊢
    omega

theorem InShape.refl (l : IL) : InShape l l := by cases l; rfl

theorem InShape.trans {l l1 l2 : IL} (a : InShape l l1) (b : InShape l1 l2) : InShape l l2 := by
  cases l; cases l1; cases l2; simp_all [InShape]

/-- The registers after the end of input in the middle of `NEEDBITS`: the input registers and `ret` differ. -/
def EofShape (l l' : IL) : Prop :=
  l' = { l with next := .null, have_ := 0, hold := l'.hold, bits := l'.bits, ret := Z_BUF_ERROR }

theorem EofShape.of_eof {l l1 : IL} (a : InShape l l1) : EofShape l (EofRegs l1) := by
  cases l; cases l1; simp_all [InShape, EofShape, EofRegs]

/-- **`NEEDBITS(n)` with the call-back**, `n ≤ 49`. No fault. Either at least `n` bits are held afterwards (`ok`; only the
input registers changed; nothing happens when `n` bits are already held), or `in` returned 0 and the call ends with
`goto inf_leave`, `Z_BUF_ERROR`, `next = NULL`, `have = 0`. At most `max bits (n+7)` bits are held. The call-back changed only
its own blocks, `R` holds again, and the registers describe the chunk in use. -/
theorem NEEDBITS_run (c : BCtx) {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {μ : Heap → Nat} (hF : InFinite c ownI R μ)
    {h : Heap} {l : IL} {bs : List UInt8}
    (B : BIn ownI h l bs) (hR : R h) (n : UInt32) (hn : n.toNat ≤ 49) :
    ∃ r l' h' bs', runX (NEEDBITS c n) l h = .ok ((r, l'), h') ∧ CbFrame ownI h h' ∧ R h' ∧ BIn ownI h' l' bs' ∧
      l'.bits.toNat ≤ max l.bits.toNat (n.toNat + 7) ∧ (n.toNat ≤ l.bits.toNat → l' = l) ∧
      (r = .ok () → n.toNat ≤ l'.bits.toNat ∧ InShape l l') ∧
      (r = .error Ex.leave → EofShape l l') ∧ (∀ e, r = .error e → e = Ex.leave) ∧ phi μ h' l' ≤ phi μ h l := by
  let Kf : IL → Nat := fun l1 => if l1.bits.toNat < n.toNat then (n.toNat - l1.bits.toNat + 7) / 8 else 0
  have key := xwhileBrk_run (cond := (do return (← get).bits < n : X Bool))
    (body := (do Zlib.Infback.PULLBYTE c; pure false : X Bool))
    (fun k l1 h1 => ∃ bs1, BIn ownI h1 l1 bs1 ∧ R h1 ∧ CbFrame ownI h h1 ∧ InShape l l1 ∧
      l1.bits.toNat ≤ max l.bits.toNat (n.toNat + 7) ∧ l.bits.toNat ≤ l1.bits.toNat ∧
      (n.toNat ≤ l.bits.toNat → l1 = l) ∧ phi μ h1 l1 ≤ phi μ h l ∧ k = Kf l1)
    (fun r l1 h1 => ∃ bs1, BIn ownI h1 l1 bs1 ∧ R h1 ∧ CbFrame ownI h h1 ∧
      l1.bits.toNat ≤ max l.bits.toNat (n.toNat + 7) ∧ (n.toNat ≤ l.bits.toNat → l1 = l) ∧
      (r = .ok () → n.toNat ≤ l1.bits.toNat ∧ InShape l l1) ∧ (r = .error Ex.leave → EofShape l l1) ∧
      (∀ e, r = .error e → e = Ex.leave) ∧ phi μ h1 l1 ≤ phi μ h l)
    (fun k l1 h1 hP => by
      obtain ⟨bs1, B1, R1, F1, S1, M1, Lb, Z1, Ph1, hk⟩ := hP
      have hnl : l1.bits.toNat < n.toNat := by
        by_cases hc : l1.bits.toNat < n.toNat
        · exact hc
        · simp only [Kf, ite_eq_right hc] at hk; omega
      have hnl' : l1.bits < n := UInt32.lt_iff_toNat_lt.mpr hnl
      have hcond : runX (do return (← get).bits < n : X Bool) l1 h1 = .ok ((.ok true, l1), h1) := by
        rw [runX_cond_lt]; simp [hnl']
      refine ⟨l1, h1, hcond, ?_⟩
      obtain ⟨r, l2, h2, bs2, hrun, F2, R2, B2, Hok, Hleave, Herr, Ph2⟩ := PULLBYTE_run c hK hF B1 R1 (by omega)
      have hFt := CbFrame.trans F1 F2
      cases r with
      | error e =>
        have he := Herr e rfl
        subst he
        refine ⟨.error Ex.leave, l2, h2, ?_, ?_⟩
        · rw [runX_bind, hrun]
        · have hl2 := Hleave rfl
          have hsh := EofShape.of_eof S1
          refine ⟨bs2, B2, R2, hFt, ?_, (fun h0 => by omega), (fun e => by cases e), (fun _ => by rw [hl2]; exact hsh), (fun e he => ?_), (by omega)⟩
          · rw [hl2]; simp [EofRegs]; omega
          · cases he; rfl
      | ok u =>
        cases u
        obtain ⟨hb8, hS2⟩ := Hok rfl
        refine ⟨.ok false, l2, h2, ?_, ?_⟩
        · rw [runX_bind, hrun]; rfl
        · refine ⟨bs2, B2, R2, hFt, S1.trans hS2, (by omega), (by omega), (fun h0 => by omega), (by omega), ?_⟩
          simp only [Kf] at hk ⊢
          rw [ite_eq_left hnl] at hk
          split <;> omega)
    (fun l1 h1 hP => by
      obtain ⟨bs1, B1, R1, F1, S1, M1, Lb, Z1, Ph1, hk⟩ := hP
      have hnl : ¬ l1.bits.toNat < n.toNat := by
        intro hl; simp only [Kf, ite_eq_left hl] at hk; omega
      refine ⟨l1, h1, (by rw [runX_cond_lt]; simp [UInt32.lt_iff_toNat_lt, hnl]), bs1, B1, R1, F1, M1, Z1,
        (fun _ => ⟨by omega, S1⟩), (fun e => by cases e), (fun e he => by cases he), Ph1⟩)
    (k := Kf l) (l := l) (h := h)
    ⟨bs, B, hR, CbFrame.refl _ _, InShape.refl l, (by omega), Nat.le_refl _, (fun _ => rfl), Nat.le_refl _, rfl⟩
    (by unfold fuel Kf; split <;> omega)
  obtain ⟨r, l', h', hr, bs', B', R', F', M', Z', Q1, Q2, Q3, Q4⟩ := key
  exact ⟨r, l', h', bs', by unfold NEEDBITS xwhile; exact hr, F', R', B', M', Z', Q1, Q2, Q3, Q4⟩

/-- **Witness for `InFinite`.** The call-back `eofIn` (no input) has the measure 0. Together with `cbContract_eof` this shows the
hypotheses of the macro theorems are met by a concrete call-back on the heap of the real initialisation. -/
theorem inFinite_eof (c : BCtx) (hc : c.inCb = eofIn) (ownI : Nat → Prop) (R : Heap → Prop) :
    InFinite c ownI R (fun _ => 0) := by
  refine ⟨fun h nx n nx' h' _ e => ?_, fun _ _ _ => rfl⟩
  have e' : (Except.ok ((0, nx), h) : Except Fault ((UInt32 × BPtr) × Heap)) = .ok ((n, nx'), h') := by
    rw [← e, hc]; rfl
  have h1 := (Prod.mk.inj (Except.ok.inj e')).1
  have h2 := (Prod.mk.inj h1).1
  subst h2
  simp

end Zlib.Infback.Proofs
