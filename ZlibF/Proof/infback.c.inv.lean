import ZlibF.Proof.«infback.c.room»
import ZlibF.Proof.«inftrees.c.fixed»

/-!
# infback.c: the invariant at the top of the loop, and `case TYPE`

`LInv` is what holds whenever `for (;;) switch (state->mode)` is about to read the mode: the stream and the state record
exist, the window is the caller's writable block, `put`/`left` describe the unwritten tail of the window, the registers
describe the current input chunk (`BIn`), the call-backs' invariant holds, and at most 39 bits are held.
-/

namespace Zlib.Infback.Spec
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs

/-- The invariant of the dispatch loop. `c.strm = r`, `c.st = zs`; `z`, `s` are the stream and state records; `bs` the rest of
the current input chunk. -/
structure LInv (c : BCtx) (win : Nat) (ownI : Nat → Prop) (R : Heap → Prop) (r : ZStreamRef) (zs : Nat) (h : Heap)
    (l : IL) (z : ZStream) (s : InflateState) (bs : List UInt8) : Prop where
  cstrm : c.strm = some r
  cst : c.st = some (.tab zs)
  hz : r.get h = some z
  hs : h.istates zs = some s
  wf : s.WellFormed
  wnd : ∃ off a, s.window = .ref (.blk win) off ∧ h.bytes win = some a ∧ h.ro win = false ∧ off + s.wsize.toNat ≤ a.size
  put : ∃ off, s.window = .ref (.blk win) off ∧ l.put = .ref (.blk win) (off + (s.wsize.toNat - l.left.toNat)) ∧
    l.left.toNat ≤ s.wsize.toNat
  bin : BIn ownI h l bs
  hR : R h
  bits : l.bits.toNat ≤ 39

end Zlib.Infback.Spec

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

theorem rdS_ok {c : BCtx} {zs : Nat} {h : Heap} {s : InflateState} (hc : c.st = some (.tab zs))
    (hs : h.istates zs = some s) {α : Type} (f : InflateState → α) : rdS c.st f h = .ok (f s, h) := by
  rw [hc, rdI_eq]; simp [hs]

theorem setMode_ok {c : BCtx} {zs : Nat} {h : Heap} {s : InflateState} (hc : c.st = some (.tab zs))
    (hs : h.istates zs = some s) (m : UInt32) : setMode c.st m h = .ok ((), setI h zs { s with mode := m }) := by
  rw [hc]; exact setMode_tab hs m

theorem wrS_ok {c : BCtx} {zs : Nat} {h : Heap} {s : InflateState} (hc : c.st = some (.tab zs))
    (hs : h.istates zs = some s) (f : InflateState → InflateState) : wrS c.st f h = .ok ((), setI h zs (f s)) := by
  rw [hc]; exact wrS_tab hs f

theorem wf_with {s : InflateState} (hw : s.WellFormed) (s' : InflateState) (e1 : s'.lens = s.lens) (e2 : s'.work = s.work)
    (e3 : s'.codes = s.codes) : s'.WellFormed := by
  unfold InflateState.WellFormed at *; rw [e1, e2, e3]; exact hw

/-- A write to the state record that keeps the window and the array sizes keeps the invariant. -/
theorem LInv.setS {c : BCtx} {win : Nat} {ownI : Nat → Prop} {R : Heap → Prop} {r : ZStreamRef} {zs : Nat} {h : Heap}
    {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8} (I : LInv c win ownI R r zs h l z s bs)
    (s' : InflateState) (hw : s'.window = s.window) (hsz : s'.wsize = s.wsize) (e1 : s'.lens = s.lens)
    (e2 : s'.work = s.work) (e3 : s'.codes = s.codes) (hR' : R (setI h zs s')) :
    LInv c win ownI R r zs (setI h zs s') l z s' bs := by
  obtain ⟨hcs, hct, hz, hs, wf, ⟨o1, a, w1, ba, ro, le⟩, ⟨o2, w2, pp, pl⟩, B, hR, hb⟩ := I
  refine ⟨hcs, hct, by simpa using hz, by simp, wf_with wf s' e1 e2 e3, ⟨o1, a, by rw [hw]; exact w1, by simpa using ba,
    by simpa using ro, by rw [hsz]; exact le⟩, ⟨o2, by rw [hw]; exact w2, by rw [hsz]; exact pp, by rw [hsz]; exact pl⟩,
    @BIn.congr ownI h (setI h zs s') l bs (fun _ _ => rfl) B, hR', hb⟩

/-- New registers (same `put` and `left`, a valid chunk, at most 39 bits) keep the invariant. -/
theorem LInv.regs {c : BCtx} {win : Nat} {ownI : Nat → Prop} {R : Heap → Prop} {r : ZStreamRef} {zs : Nat} {h : Heap}
    {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8} (I : LInv c win ownI R r zs h l z s bs) {l' : IL}
    {bs' : List UInt8} (hp : l'.put = l.put) (hl : l'.left = l.left) (B' : BIn ownI h l' bs')
    (hb : l'.bits.toNat ≤ 39) : LInv c win ownI R r zs h l' z s bs' := by
  obtain ⟨hcs, hct, hz, hs, wf, wnd, ⟨o2, w2, pp, pl⟩, B, hR, hb0⟩ := I
  exact ⟨hcs, hct, hz, hs, wf, wnd, ⟨o2, w2, by rw [hp, hl]; exact pp, by rw [hl]; exact pl⟩, B', hR, hb⟩

/-- After a call of `in` or `out` (a `CbFrame` for the blocks `own`, the window being none of them). -/
theorem LInv.cb {c : BCtx} {win : Nat} {ownI own : Nat → Prop} {R : Heap → Prop} {r : ZStreamRef} {zs : Nat} {h h' : Heap}
    {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8} (I : LInv c win ownI R r zs h l z s bs)
    (F : CbFrame own h h') (hw : ¬ own win) (hR' : R h') {l' : IL} {bs' : List UInt8}
    (hp : l'.put = l.put) (hl : l'.left = l.left) (B' : BIn ownI h' l' bs') (hb : l'.bits.toNat ≤ 39) :
    LInv c win ownI R r zs h' l' z s bs' := by
  obtain ⟨hcs, hct, hz, hs, wf, ⟨o1, a, w1, ba, ro, le⟩, ⟨o2, w2, pp, pl⟩, B, hR, hb0⟩ := I
  refine ⟨hcs, hct, by rw [CbFrame.zget F]; exact hz, by rw [F.istates]; exact hs, wf,
    ⟨o1, a, w1, by rw [F.bytes win hw]; exact ba, by rw [F.ro]; exact ro, le⟩,
    ⟨o2, w2, by rw [hp, hl]; exact pp, by rw [hl]; exact pl⟩, B', hR', hb⟩

theorem LInv.R_setI {c : BCtx} {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {h : Heap} (hR : R h) (zs : Nat)
    (s : InflateState) : R (setI h zs s) := (hK.local_ h (setI h zs s) (fun _ _ => rfl)).1 hR

/-- `case TYPE` after the last block: `BYTEBITS(); state->mode = DONE`. -/
theorem TYPE_last {c : BCtx} {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {μ : Heap → Nat} (hF : InFinite c ownI R μ) {r : ZStreamRef} {zs : Nat}
    {h : Heap} {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (I : LInv c win ownI R r zs h l z s bs) (hl : s.last ≠ 0) :
    ∃ bs', runX (back_TYPE c) l h = .ok ((.ok (), bytebits l), setI h zs { s with mode := DONE }) ∧
      LInv c win ownI R r zs (setI h zs { s with mode := DONE }) (bytebits l) z { s with mode := DONE } bs' ∧
      phi μ (setI h zs { s with mode := DONE }) (bytebits l) ≤ phi μ h l := by
  have hne : (s.last != 0) = true := by simpa using hl
  have hrd : liftM (rdS c.st (·.last)) = (liftM (rdS c.st (·.last)) : X Int32) := rfl
  obtain ⟨B1, hs1, hb1⟩ := BYTEBITS_inv I.bin.bit
  have I1 := Zlib.Infback.Proofs.LInv.setS I { s with mode := DONE } rfl rfl rfl rfl rfl (LInv.R_setI hK I.hR zs _)
  have hbl : (bytebits l).bits.toNat ≤ l.bits.toNat := by
    show (l.bits - (l.bits &&& 7)).toNat ≤ _
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (and7_le l))]; omega
  refine ⟨bs, ?_, ?_, ?_⟩
  · unfold back_TYPE
    simp [runX_bind, runX_lift_ok (rdS_ok I.cst I.hs _), hne, hl, BYTEBITS_run, runX_lift_ok (setMode_ok I.cst I.hs DONE), runX_pure]
  · have := I.bits
    exact Zlib.Infback.Proofs.LInv.regs I1 rfl rfl
      (@BIn.congr ownI h (setI h zs { s with mode := DONE }) (bytebits l) bs (fun _ _ => rfl) ⟨B1, I.bin.own⟩) (by omega)
  · simp only [phi]
    have := I.bin.bit.have_eq
    have h2 : (bytebits l).have_ = l.have_ := rfl
    rw [h2]
    have hm : μ (setI h zs { s with mode := DONE }) = μ h := hF.local_ _ _ (fun _ _ => rfl)
    omega

set_option maxRecDepth 100000 in
theorem msg_block_type : "invalid block type" ∈ strTable := by
  rw [Array.mem_def]; decide +kernel

theorem LInv.putMsg {c : BCtx} {win : Nat} {ownI : Nat → Prop} {R : Heap → Prop} {r : ZStreamRef} {zs : Nat} {h : Heap}
    {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8} (I : LInv c win ownI R r zs h l z s bs) (m : BPtr)
    (hR' : R (r.put h { z with msg := m })) :
    LInv c win ownI R r zs (r.put h { z with msg := m }) l { z with msg := m } s bs := by
  obtain ⟨hcs, hct, hz, hs, wf, ⟨o1, a, w1, ba, ro, le⟩, pt, B, hR, hb⟩ := I
  refine ⟨hcs, hct, by simp [hz], by simpa using hs, wf, ⟨o1, a, w1, by simpa using ba, by simpa using ro, le⟩, pt,
    @BIn.congr ownI h (r.put h { z with msg := m }) l bs (fun _ _ => by simp) B, hR', hb⟩

/-- `strm->msg = "..."; state->mode = BAD;` for a message that is a string literal. -/
theorem badMode_run (c : BCtx) {r : ZStreamRef} {zs : Nat} {h : Heap} {z : ZStream} {s : InflateState}
    (hcs : c.strm = some r) (hct : c.st = some (.tab zs)) (hz : r.get h = some z) (hs : h.istates zs = some s)
    (msg : String) (hm : msg ∈ strTable) :
    ∃ i, badMode c msg h = .ok ((), setI (r.put h { z with msg := .ref (.str i) 0 }) zs { s with mode := BAD }) := by
  obtain ⟨i, hi, -⟩ := strLitRef_of_mem (h := h) hm
  refine ⟨i, ?_⟩
  have hs' : (r.put h { z with msg := .ref (.str i) 0 }).istates zs = some s := by simpa using hs
  have hz' : r.get (r.put h { z with msg := .ref (.str i) 0 }) = some { z with msg := .ref (.str i) 0 } := by simp [hz]
  unfold badMode setMsg Zlib.Zutil.strLit
  simp [bind_app, hi, hcs, ldZ_eq, hz, stZ_eq, setMode_ok hct hs']

theorem phi_congr {c : BCtx} {ownI : Nat → Prop} {R : Heap → Prop} {μ : Heap → Nat} (hF : InFinite c ownI R μ)
    {h h' : Heap} (e : ∀ b, h'.bytes b = h.bytes b) (l : IL) : phi μ h' l = phi μ h l := by
  simp only [phi]; rw [hF.local_ h h' (fun b _ => e b)]

/-- `case TYPE` for a block that is not the last: `NEEDBITS(3)`, the last-block flag, the block type, `DROPBITS`. Either the
input ended (`Z_BUF_ERROR`), or three bits are consumed and the mode is `STORED`, `LEN` (fixed tables), `TABLE`, or `BAD`
("invalid block type"). -/
theorem TYPE_more {c : BCtx} {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {μ : Heap → Nat} (hF : InFinite c ownI R μ)
    {r : ZStreamRef} {zs : Nat} {h : Heap} {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (I : LInv c win ownI R r zs h l z s bs) (hl : s.last = 0) :
    ∃ res l' h' z' s' bs', runX (back_TYPE c) l h = .ok ((res, l'), h') ∧ LInv c win ownI R r zs h' l' z' s' bs' ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR ∧ phi μ h' l' ≤ phi μ h l) ∧
      (res = .ok () → phi μ h' l' + 3 ≤ phi μ h l ∧
        (s'.mode = STORED ∨ s'.mode = LEN ∨ s'.mode = TABLE ∨ s'.mode = BAD)) := by
  obtain ⟨res0, l1, h1, bs1, hrun1, F1, R1, B1, M1, Z1, Hok, Hleave, Herr, Ph1⟩ :=
    NEEDBITS_run c hK hF I.bin I.hR 3 (by decide)
  have hL1 : ∀ {l1 : IL}, InShape l l1 → l1.put = l.put ∧ l1.left = l.left := by
    intro l1 hs; exact ⟨by simpa using congrArg IL.put hs, by simpa using congrArg IL.left hs⟩
  have h3n : (3 : UInt32).toNat = 3 := rfl
  have hb39 : l1.bits.toNat ≤ 39 := by have := I.bits; rw [h3n] at M1; omega
  cases res0 with
  | error e =>
    have he := Herr e rfl
    subst he
    have hE := Hleave rfl
    have hp : l1.put = l.put := by rw [hE]
    have hlf : l1.left = l.left := by rw [hE]
    have I1 := Zlib.Infback.Proofs.LInv.cb I F1 hK.disj.1 R1 hp hlf B1 hb39
    refine ⟨.error Ex.leave, l1, h1, z, s, bs1, ?_, I1, ?_, fun he => by cases he⟩
    · unfold back_TYPE
      simp [runX_bind, runX_lift_ok (rdS_ok I.cst I.hs _), hl, hrun1]
    · intro e he
      cases he
      exact ⟨rfl, by rw [hE], Ph1⟩
  | ok u =>
    cases u
    obtain ⟨h3, hS⟩ := Hok rfl
    obtain ⟨hp, hlf⟩ := hL1 hS
    have I1 := Zlib.Infback.Proofs.LInv.cb I F1 hK.disj.1 R1 hp hlf B1 hb39
    have h3n' : 3 ≤ l1.bits.toNat := by rw [h3n] at h3; exact h3
    have hb1 : 1 ≤ l1.bits.toNat := by omega
    -- the registers after `DROPBITS(1)` and `DROPBITS(2)`
    obtain ⟨B2, -, hbit2⟩ := DROPBITS_inv I1.bin.bit 1 (by simpa using hb1) (by decide)
    obtain ⟨B3, -, hbit3⟩ := DROPBITS_inv B2 2 (by simp at hbit2 ⊢; omega) (by decide)
    simp only [UInt32.toNat_one, show (2 : UInt32).toNat = 2 from rfl] at hbit2 hbit3
    obtain ⟨v1, hv1⟩ : ∃ v1 : UInt32, v1 = l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1) := ⟨_, rfl⟩
    obtain ⟨l2, hl2⟩ : ∃ l2 : IL, l2 = { l1 with hold := l1.hold >>> (1 : UInt32).toUInt64, bits := l1.bits - 1 } := ⟨_, rfl⟩
    obtain ⟨v2, hv2⟩ : ∃ v2 : UInt32, v2 = l2.hold.toUInt32 &&& ((1 : UInt32) <<< 2 - 1) := ⟨_, rfl⟩
    obtain ⟨l3, hl3⟩ : ∃ l3 : IL, l3 = { l2 with hold := l2.hold >>> (2 : UInt32).toUInt64, bits := l2.bits - 2 } := ⟨_, rfl⟩
    obtain ⟨s1, hs1d⟩ : ∃ s1 : InflateState, s1 = { s with last := u2i v1 } := ⟨_, rfl⟩
    have hr1 : runX (BITS 1) l1 h1 = .ok ((.ok v1, l1), h1) := by rw [BITS_run l1 h1 1 (by decide), hv1]
    have hd1 : ∀ h, runX (DROPBITS 1) l1 h = .ok ((.ok (), l2), h) := by
      intro h; rw [DROPBITS_run l1 h 1 (by decide), hl2]
    have hb2 : ∀ h, runX (BITS 2) l2 h = .ok ((.ok v2, l2), h) := by intro h; rw [BITS_run l2 h 2 (by decide), hv2]
    have hd2 : ∀ h, runX (DROPBITS 2) l2 h = .ok ((.ok (), l3), h) := by
      intro h; rw [DROPBITS_run l2 h 2 (by decide), hl3]
    have hw1 : wrS c.st (fun s => { s with last := u2i v1 }) h1 = .ok ((), setI h1 zs s1) := by
      rw [wrS_ok I1.cst I1.hs, hs1d]
    have bits2 : l2.bits.toNat = l1.bits.toNat - 1 := by rw [hl2]; simpa using hbit2
    have bits3 : l3.bits.toNat = l2.bits.toNat - 2 := by
      rw [hl3, hl2]; simpa using hbit3
    have B3' : BIn ownI h1 l3 bs1 := by
      refine ⟨?_, ?_⟩
      · rw [hl3, hl2]; exact B3
      · rw [hl3, hl2]; exact I1.bin.own
    have B3c : ∀ s' : InflateState, BIn ownI (setI h1 zs s') l3 bs1 := fun s' =>
      @BIn.congr ownI h1 (setI h1 zs s') l3 bs1 (fun _ _ => rfl) B3'
    have hv2lt : v2.toNat < 4 := by
      rw [hv2, BITS_toNat l2 2 (by decide)]
      exact Nat.mod_lt _ (by decide)
    have hs2 : (setI h1 zs s1).istates zs = some s1 := by simp
    have hR2 : R (setI h1 zs s1) := LInv.R_setI hK I1.hR zs s1
    have hzs2 : r.get (setI h1 zs s1) = some z := by simpa using I1.hz
    have hcases : v2 = 0 ∨ v2 = 1 ∨ v2 = 2 ∨ v2 = 3 := by
      have : v2.toNat = 0 ∨ v2.toNat = 1 ∨ v2.toNat = 2 ∨ v2.toNat = 3 := by omega
      rcases this with e | e | e | e
      · exact Or.inl (UInt32.toNat_inj.mp (by simpa using e))
      · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by simpa using e)))
      · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by simpa using e))))
      · exact Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp (by simpa using e))))
    have hphi : ∀ hf : Heap, (∀ b, hf.bytes b = h1.bytes b) → phi μ hf l3 + 3 ≤ phi μ h l := by
      intro hf hb
      rw [phi_congr hF hb]
      simp only [phi] at Ph1 ⊢
      have : l3.have_ = l1.have_ := by rw [hl3, hl2]
      rw [this]; omega
    rcases hcases with rfl | rfl | rfl | rfl
    · refine ⟨.ok (), l3, setI h1 zs { s1 with mode := STORED }, z, { s1 with mode := STORED }, bs1, ?_, ?_,
        (fun e he => by cases he), fun _ => ⟨hphi _ (fun _ => rfl), Or.inl rfl⟩⟩
      · unfold back_TYPE
        simp only [runX_bind, runX_lift_ok (rdS_ok I.cst I.hs _), hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrun1,
          hr1, runX_lift_ok hw1, hd1, hb2, runX_lift_ok (setMode_ok I1.cst hs2 STORED), hd2]
        simp only [setI_setI]
      · exact Zlib.Infback.Proofs.LInv.regs
          (Zlib.Infback.Proofs.LInv.setS I1 { s1 with mode := STORED } (by rw [hs1d]) (by rw [hs1d]) (by rw [hs1d])
            (by rw [hs1d]) (by rw [hs1d]) (LInv.R_setI hK I1.hR zs _)) (by rw [hl3, hl2]) (by rw [hl3, hl2]) (B3c _)
          (by have := I1.bits; omega)
    · have hfx : Zlib.Inftrees.inflate_fixed c.st (setI h1 zs s1) =
          .ok ((), setI (setI h1 zs s1) zs (Zlib.Inftrees.Proofs.fixedState s1)) := by
        rw [I1.cst]; have := Zlib.Inftrees.Proofs.inflate_fixed_ok hs2; rwa [C.run] at this
      have hs3 : (setI (setI h1 zs s1) zs (Zlib.Inftrees.Proofs.fixedState s1)).istates zs =
          some (Zlib.Inftrees.Proofs.fixedState s1) := by simp
      refine ⟨.ok (), l3, setI h1 zs { Zlib.Inftrees.Proofs.fixedState s1 with mode := LEN }, z,
        { Zlib.Inftrees.Proofs.fixedState s1 with mode := LEN }, bs1, ?_, ?_,
        (fun e he => by cases he), fun _ => ⟨hphi _ (fun _ => rfl), Or.inr (Or.inl rfl)⟩⟩
      · unfold back_TYPE
        simp only [runX_bind, runX_lift_ok (rdS_ok I.cst I.hs _), hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrun1,
          hr1, runX_lift_ok hw1, hd1, hb2, runX_lift_ok hfx, runX_lift_ok (setMode_ok I1.cst hs3 LEN), hd2]
        simp only [setI_setI]
      · exact Zlib.Infback.Proofs.LInv.regs
          (Zlib.Infback.Proofs.LInv.setS I1 { Zlib.Inftrees.Proofs.fixedState s1 with mode := LEN } (by rw [hs1d]; rfl)
            (by rw [hs1d]; rfl) (by rw [hs1d]; rfl) (by rw [hs1d]; rfl) (by rw [hs1d]; rfl) (LInv.R_setI hK I1.hR zs _))
          (by rw [hl3, hl2]) (by rw [hl3, hl2]) (B3c _) (by have := I1.bits; omega)
    · refine ⟨.ok (), l3, setI h1 zs { s1 with mode := TABLE }, z, { s1 with mode := TABLE }, bs1, ?_, ?_,
        (fun e he => by cases he), fun _ => ⟨hphi _ (fun _ => rfl), Or.inr (Or.inr (Or.inl rfl))⟩⟩
      · unfold back_TYPE
        simp only [runX_bind, runX_lift_ok (rdS_ok I.cst I.hs _), hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrun1,
          hr1, runX_lift_ok hw1, hd1, hb2, runX_lift_ok (setMode_ok I1.cst hs2 TABLE), hd2]
        simp only [setI_setI]
      · exact Zlib.Infback.Proofs.LInv.regs
          (Zlib.Infback.Proofs.LInv.setS I1 { s1 with mode := TABLE } (by rw [hs1d]) (by rw [hs1d]) (by rw [hs1d])
            (by rw [hs1d]) (by rw [hs1d]) (LInv.R_setI hK I1.hR zs _)) (by rw [hl3, hl2]) (by rw [hl3, hl2]) (B3c _)
          (by have := I1.bits; omega)
    · obtain ⟨i, hbad⟩ := badMode_run c I1.cstrm I1.cst hzs2 hs2 "invalid block type" msg_block_type
      have I2 := Zlib.Infback.Proofs.LInv.setS I1 s1 (by rw [hs1d]) (by rw [hs1d]) (by rw [hs1d]) (by rw [hs1d])
        (by rw [hs1d]) hR2
      have hRm : R (r.put (setI h1 zs s1) { z with msg := .ref (.str i) 0 }) :=
        (hK.local_ (setI h1 zs s1) _ (fun b _ => by simp)).1 hR2
      have I3 := Zlib.Infback.Proofs.LInv.putMsg I2 (.ref (.str i) 0) hRm
      refine ⟨.ok (), l3, setI (r.put (setI h1 zs s1) { z with msg := .ref (.str i) 0 }) zs { s1 with mode := BAD },
        { z with msg := .ref (.str i) 0 }, { s1 with mode := BAD }, bs1, ?_, ?_,
        (fun e he => by cases he), fun _ => ⟨hphi _ (fun b => by simp), Or.inr (Or.inr (Or.inr rfl))⟩⟩
      · unfold back_TYPE
        simp only [runX_bind, runX_lift_ok (rdS_ok I.cst I.hs _), hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrun1,
          hr1, runX_lift_ok hw1, hd1, hb2]
        show runX (liftM (badMode c "invalid block type") >>= fun _ => DROPBITS 2) l2 (setI h1 zs s1) = _
        simp only [runX_bind, runX_lift_ok hbad, hd2]
      · exact Zlib.Infback.Proofs.LInv.regs
          (Zlib.Infback.Proofs.LInv.setS I3 { s1 with mode := BAD } rfl rfl rfl rfl rfl
            (LInv.R_setI hK I3.hR zs _)) (by rw [hl3, hl2]) (by rw [hl3, hl2]) (@BIn.congr ownI h1 _ l3 bs1 (fun _ _ => by simp) B3') (by have := I1.bits; omega)

end Zlib.Infback.Proofs
