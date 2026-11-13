import ZlibF.Proof.«infback.c.safety-library»
import ZlibF.Proof.«infback.c.inv»

/-!
# infback.c: the modes of the dispatch loop on the invariant

`Round` is what one round of `for (;;) switch (state->mode)` leaves: the invariant with a smaller
measure, or the way out with one of the three results. `PInv.regs` and `PInv.putMsg` move the
invariant over a change of the bit registers and over a store of `strm->msg`. `TYPE_p` is
`case TYPE` (ported from `TYPE_last`, `TYPE_more` of `infback.c.inv`).
-/

namespace Zlib.Infback.Safety
open C ZlibF.Spec ZlibF.Spec.Public Zlib.Inflate Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Proofs
open Zlib.Inflate.Spec (setI)
set_option autoImplicit false

/-- Fewer than 8 bits are held when the next round is in `TYPE`, `TABLE` or `LEN`: the entry
assumption of `inflate_fast`, which `case LEN` calls without checking it. -/
def Short (i : Nat) (l : IL) (h : Heap) : Prop :=
  ∀ s, h.istates i = some s → (s.mode = TYPE ∨ s.mode = TABLE ∨ s.mode = LEN) → l.bits.toNat < 8

theorem Short.of_bits {i : Nat} {l : IL} {h : Heap} (b : l.bits.toNat < 8) : Short i l h := fun _ _ _ => b

theorem Short.of_mode {i : Nat} {l : IL} {h : Heap} {sF : InflateState} (hs : h.istates i = some sF)
    (m : sF.mode = BAD ∨ sF.mode = DONE ∨ sF.mode = STORED) : Short i l h := by
  intro s g mm
  rw [hs] at g
  cases g
  exfalso
  rcases m with m | m | m <;> rcases mm with x | x | x <;> rw [m] at x <;> exact absurd x (by decide)

/-- What one round of the dispatch loop leaves. -/
def Round (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) (h0 h : Heap) (l : IL) (log : BackLog)
    (res : Except Ex Unit) (l' : IL) (h' : Heap) : Prop :=
  ∃ log', PInv c pr h0 h' l' log' ∧
    ((res = .ok () ∧ backMeasure pr h' l' log' < backMeasure pr h l log) ∨
     (res = .error Ex.leave ∧ (l'.ret = Z_STREAM_END ∨ l'.ret = Z_DATA_ERROR ∨ l'.ret = Z_BUF_ERROR))) ∧
    (res = .ok () → Short i l' h')

/-- **A change of the bit registers alone keeps `PInv`.** -/
theorem PInv.regs {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) {l' : IL}
    (put : l'.put = l.put) (left : l'.left = l.left) (have_ : l'.have_ = l.have_) (next : l'.next = l.next)
    (bits : l'.bits.toNat ≤ 39) (hold : l'.hold.toNat < 2 ^ l'.bits.toNat) : PInv c pr h0 h l' log :=
  { I with
    put := by rw [put, left]; exact I.put
    chunk := by rw [have_, next]; exact I.chunk
    bits := ⟨bits, hold⟩ }

/-- A store into the stream record leaves every byte view. -/
theorem get_put (h : Heap) (r : ZStreamRef) (z : ZStream) (ref : BRef) :
    (Space.get (r.put h z) ref : Option (Array UInt8)) = Space.get h ref := by
  cases r <;> cases ref <;> simp only [ZStreamRef.put] <;> split <;> rfl

theorem ro_put (h : Heap) (r : ZStreamRef) (z : ZStream) (ref : BRef) :
    Space.ro (r.put h z) ref = Space.ro h ref := by
  cases r <;> cases ref <;> simp only [ZStreamRef.put] <;> split <;> rfl

/-- A store into the stream record is a frame of the call. -/
theorem callbackFrame_put {own : Nat → Prop} {h : Heap} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (z : ZStream) : CallbackFrame own h (r.put h z) r i window n := by
  classical
  have frame : Frame h (r.put h z) (fun b => StreamRoot r b ∨ b = i ∨ own b) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun b _ outside => ?_⟩
    all_goals cases r
    all_goals simp only [ZStreamRef.put]
    all_goals try (split <;> rfl)
    all_goals try (split <;> exact Nat.le_refl _)
    · have ne : b ≠ _ := fun e => outside (Or.inl e)
      split <;> simp [upd_ne _ _ _ _ ne]
    · have ne : b ≠ _ := fun e => outside (Or.inl e)
      split <;> simp [upd_ne _ _ _ _ ne]
  refine ⟨Frame.mono frame (fun b x => by rcases x with x | x | x <;> simp [x]), fun _ => ?_⟩
  have restore : restoreRegions h (r.put h z) [⟨window, n⟩] = r.put h z := by
    simp only [restoreRegions, List.foldl]
    cases window with
    | null => rfl
    | ref ref off =>
      simp only []
      cases get : Space.get h ref with
      | none => rfl
      | some a => exact put_self (by rw [get_put]; exact get)
  refine ⟨by rw [restore]; exact frame, ?_⟩
  intro region _ ref off a _ get
  exact ⟨a, by rw [get_put]; exact get, rfl, fun _ _ _ => rfl⟩

/-- **A store of `strm->msg` keeps `PInv`.** -/
theorem PInv.putMsg {c : BCtx} {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat} {pr : Proto c r i window n}
    {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log) {z : ZStream} (hz : r.get h = some z)
    (m : BPtr) : PInv c pr h0 (r.put h { z with msg := m }) l log := by
  obtain ⟨z1, s, valid, win, sz⟩ := I.valid
  have e : z1 = z := Option.some.inj (valid.1.symm.trans hz)
  subst e
  have shape := Zlib.Inflate.Proofs.shape_put hz { z1 with msg := m }
  have ist : (r.put h { z1 with msg := m }).istates = h.istates := Zlib.Inflate.Proofs.ZStreamRef.put_istates h r _
  obtain ⟨-, hs, zst, za, zf, wf, lo, hi, ws, nn, wr, fresh, uniq, globals⟩ := valid
  have valid' : BackValid (r.put h { z1 with msg := m }) r i { z1 with msg := m } s := by
    refine ⟨Zlib.Inflate.Proofs.ZStreamRef.get_put_same hz _, by rw [ist]; exact hs, zst, za, zf, wf, lo, hi, ws, nn,
      ?_, ?_, Zlib.Inflate.Proofs.Shape.uniq shape uniq, ?_⟩
    · rcases wr with x | ⟨ref, off, a, ptr, get, ro, room⟩
      · exact Or.inl x
      · exact Or.inr ⟨ref, off, a, ptr, by rw [get_put]; exact get, by rw [ro_put]; exact ro, room⟩
    · exact Zlib.Inflate.Proofs.Shape.fresh shape (by cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl) fresh
    · unfold LibraryGlobals at globals ⊢
      rw [← globals]; cases r <;> simp only [ZStreamRef.put] <;> split <;> rfl
  have writable : Writable h window n := by rw [win, sz] at wr; exact wr
  have proto' : pr.invariant (r.put h { z1 with msg := m }) log := by
    refine (pr.local_ h _ log ?_).1 I.proto
    rw [restoreWindow_of_same (fun ref _ _ => get_put h r _ ref)]
    refine ⟨?_, ?_, ?_, ?_, ?_, fun b own => ?_⟩
    all_goals cases r
    all_goals simp only [ZStreamRef.put]
    all_goals try (split <;> rfl)
    · have ne : b ≠ _ := fun e => pr.disjoint.2 b e own
      split <;> simp [upd_ne _ _ _ _ ne]
    · have ne : b ≠ _ := fun e => pr.disjoint.2 b e own
      split <;> simp [upd_ne _ _ _ _ ne]
  exact
    { cstrm := I.cstrm, cst := I.cst, valid := ⟨{ z1 with msg := m }, s, valid', win, sz⟩, winRoot := I.winRoot,
      put := I.put, chunk := I.chunk,
      held := by
        intro ne
        obtain ⟨bytes, sep, roots⟩ := I.held ne
        refine ⟨?_, sep, roots⟩
        rcases bytes with x | ⟨ref, off, a, ptr, g, room, xs⟩
        · exact Or.inl x
        · exact Or.inr ⟨ref, off, a, ptr, by rw [get_put]; exact g, room, xs⟩,
      bits := I.bits, proto := proto',
      frame := CallbackFrame.trans I.frame (callbackFrame_put _) (fun d => window_views writable I.winRoot d),
      live := fun b o => (Zlib.Inflate.Proofs.Shape.live shape b).trans (I.live b o),
      mode := fun s1 g => I.mode s1 (by rw [ist] at g; exact g),
      platform := I.platform, fit := fun ref a g => I.fit ref a (by rw [get_put] at g; exact g),
      chunkBlk := I.chunkBlk }

theorem modeRank_le (m : UInt32) : modeRank m ≤ 2 := by
  unfold modeRank; split <;> (try split) <;> omega

/-- The modes `inflateBack()` sets. -/
theorem modeOk_of {i : Nat} {s : InflateState} (m : s.mode = STORED ∨ s.mode = TABLE ∨ s.mode = DONE ∨ s.mode = BAD) :
    ModeOk i s := by
  refine ⟨by rcases m with m | m | m | m <;> simp [m], fun e => ?_⟩
  exfalso
  rcases m with m | m | m | m <;> rw [m] at e <;> exact absurd e (by decide)

theorem modeOk_fixed (i : Nat) (s : InflateState) :
    ModeOk i { Zlib.Inftrees.Proofs.fixedState s with mode := LEN } :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), fun _ => ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩⟩

set_option maxRecDepth 100000 in
/-- **`case TYPE` on the invariant**: after the last block `DONE`; otherwise three bits read, and
`STORED`, `LEN` with the fixed tables, `TABLE` or `BAD`; or the input ends (`Z_BUF_ERROR`). -/
theorem TYPE_p (c : BCtx) {r : ZStreamRef} {i : Nat} {window : BPtr} {n : Nat}
    (pr : Proto c r i window n) {h0 h : Heap} {l : IL} {log : BackLog} (I : PInv c pr h0 h l log)
    {s : InflateState} (hs : h.istates i = some s) (mode : s.mode = TYPE) (short : l.bits.toNat < 8) :
    ∃ res l' h', runX (back_TYPE c) l h = .ok ((res, l'), h') ∧ Round c pr h0 h l log res l' h' := by
  have rank0 : backMeasure pr h l log = 4 * (l.bits.toNat + 8 * l.have_.toNat + 8 * (pr.inputBound - log.supplied.length)) + 1 := by
    unfold backMeasure; rw [hs]; simp [modeRank, mode]; decide
  obtain ⟨z0, s0, valid0, -, -⟩ := I.valid
  have e0 : s0 = s := Option.some.inj (valid0.2.1.symm.trans hs)
  subst e0
  have wf0 := valid0.2.2.2.2.2.1
  by_cases hl : s0.last ≠ 0
  · have hne : (s0.last != 0) = true := by simpa using hl
    let sD : InflateState := { s0 with mode := DONE }
    have I1 := I.setState hs sD rfl rfl rfl (wf_with wf0 sD rfl rfl rfl) (modeOk_of (Or.inr (Or.inr (Or.inl rfl))))
    obtain ⟨B1, -, -⟩ := BYTEBITS_inv (bitInv_of I1)
    have hbl : (bytebits l).bits.toNat ≤ l.bits.toNat := by
      show (l.bits - (l.bits &&& 7)).toNat ≤ _
      rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (and7_le l))]; omega
    have I2 := I1.regs (l' := bytebits l) rfl rfl rfl rfl (by have := I.bits.1; omega) B1.hold_lt
    refine ⟨.ok (), bytebits l, setI h i sD, ?_, log, I2, Or.inl ⟨rfl, ?_⟩,
      fun _ => Short.of_mode (sF := sD) (by simp [setI]) (Or.inr (Or.inl rfl))⟩
    · unfold back_TYPE
      simp [runX_bind, runX_lift_ok (rdS_ok I.cst hs _), hl, BYTEBITS_run, runX_lift_ok (setMode_ok I.cst hs DONE),
        runX_pure, sD]
    · rw [rank0]
      unfold backMeasure
      simp [setI, sD, modeRank]
      show 4 * ((bytebits l).bits.toNat + 8 * l.have_.toNat + 8 * (pr.inputBound - log.supplied.length)) + 0 < _
      omega
  · have hl0 : s0.last = 0 := Classical.byContradiction hl
    obtain ⟨res0, l1, h1, log1, run1, I1, okc, errc, -, meas1⟩ := NEEDBITS_p c pr 3 (by decide) I
    cases res0 with
    | error e =>
      obtain ⟨rfl, ret⟩ := errc e rfl
      refine ⟨.error Ex.leave, l1, h1, ?_, log1, I1, Or.inr ⟨rfl, Or.inr (Or.inr ret)⟩, fun x => (nomatch x)⟩
      unfold back_TYPE
      simp [runX_bind, runX_lift_ok (rdS_ok I.cst hs _), hl0, run1]
    | ok u =>
      cases u
      obtain ⟨b3, put1, left1, mx⟩ := okc rfl
      obtain ⟨z1, s1, valid1, -, -⟩ := I1.valid
      have hs1 := valid1.2.1
      have wf1 := valid1.2.2.2.2.2.1
      have hzs1 := valid1.1
      have h3n : (3 : UInt32).toNat = 3 := rfl
      rw [h3n] at b3
      have hb39 := I1.bits.1
      have B0 := bitInv_of I1
      obtain ⟨B2, -, hbit2⟩ := DROPBITS_inv B0 1 (by simp; omega) (by decide)
      obtain ⟨B3, -, hbit3⟩ := DROPBITS_inv B2 2 (by simp at hbit2 ⊢; omega) (by decide)
      simp only [UInt32.toNat_one, show (2 : UInt32).toNat = 2 from rfl] at hbit2 hbit3
      obtain ⟨v1, hv1⟩ : ∃ v1 : UInt32, v1 = l1.hold.toUInt32 &&& ((1 : UInt32) <<< 1 - 1) := ⟨_, rfl⟩
      obtain ⟨l2, hl2⟩ : ∃ l2 : IL, l2 = { l1 with hold := l1.hold >>> (1 : UInt32).toUInt64, bits := l1.bits - 1 } :=
        ⟨_, rfl⟩
      obtain ⟨v2, hv2⟩ : ∃ v2 : UInt32, v2 = l2.hold.toUInt32 &&& ((1 : UInt32) <<< 2 - 1) := ⟨_, rfl⟩
      obtain ⟨l3, hl3⟩ : ∃ l3 : IL, l3 = { l2 with hold := l2.hold >>> (2 : UInt32).toUInt64, bits := l2.bits - 2 } :=
        ⟨_, rfl⟩
      obtain ⟨sL, hsL⟩ : ∃ sL : InflateState, sL = { s1 with last := u2i v1 } := ⟨_, rfl⟩
      have hr1 : runX (BITS 1) l1 h1 = .ok ((.ok v1, l1), h1) := by rw [BITS_run l1 h1 1 (by decide), hv1]
      have hd1 : ∀ h, runX (DROPBITS 1) l1 h = .ok ((.ok (), l2), h) := by
        intro h; rw [DROPBITS_run l1 h 1 (by decide), hl2]
      have hb2 : ∀ h, runX (BITS 2) l2 h = .ok ((.ok v2, l2), h) := by
        intro h; rw [BITS_run l2 h 2 (by decide), hv2]
      have hd2 : ∀ h, runX (DROPBITS 2) l2 h = .ok ((.ok (), l3), h) := by
        intro h; rw [DROPBITS_run l2 h 2 (by decide), hl3]
      have hw1 : wrS c.st (fun s => { s with last := u2i v1 }) h1 = .ok ((), setI h1 i sL) := by
        rw [wrS_ok I1.cst hs1, hsL]
      have bits3 : l3.bits.toNat = l1.bits.toNat - 3 := by
        have e2 : l2.bits.toNat = l1.bits.toNat - 1 := by rw [hl2]; simpa using hbit2
        rw [hl3]; simp only []
        have : (l2.bits - 2).toNat = l2.bits.toNat - 2 := by rw [hl2]; simpa using hbit3
        rw [this, e2]; omega
      have B3' : BitInv h1 l3 (log1.held.drop (log1.held.length - l1.have_.toNat)) := by rw [hl3, hl2]; exact B3
      have have3 : l3.have_ = l1.have_ := by rw [hl3, hl2]
      have next3 : l3.next = l1.next := by rw [hl3, hl2]
      have put3 : l3.put = l1.put := by rw [hl3, hl2]
      have left3 : l3.left = l1.left := by rw [hl3, hl2]
      have hs2 : (setI h1 i sL).istates i = some sL := by simp [setI]
      have hv2lt : v2.toNat < 4 := by
        rw [hv2, BITS_toNat l2 2 (by decide)]
        exact Nat.mod_lt _ (by decide)
      have hcases : v2 = 0 ∨ v2 = 1 ∨ v2 = 2 ∨ v2 = 3 := by
        have : v2.toNat = 0 ∨ v2.toNat = 1 ∨ v2.toNat = 2 ∨ v2.toNat = 3 := by omega
        rcases this with e | e | e | e
        · exact Or.inl (UInt32.toNat_inj.mp (by simpa using e))
        · exact Or.inr (Or.inl (UInt32.toNat_inj.mp (by simpa using e)))
        · exact Or.inr (Or.inr (Or.inl (UInt32.toNat_inj.mp (by simpa using e))))
        · exact Or.inr (Or.inr (Or.inr (UInt32.toNat_inj.mp (by simpa using e))))
      have rank1 : 4 * (l1.bits.toNat + 8 * l1.have_.toNat + 8 * (pr.inputBound - log1.supplied.length)) ≤
          backMeasure pr h1 l1 log1 := by unfold backMeasure; omega
      have measure : ∀ (hf : Heap) (sf : InflateState), hf.istates i = some sf →
          backMeasure pr hf l3 log1 < backMeasure pr h l log := by
        intro hf sf g
        have rk := modeRank_le sf.mode
        unfold backMeasure
        rw [g, have3]
        simp only [Option.map_some, Option.getD_some]
        omega
      have regs : ∀ (hf : Heap) (I' : PInv c pr h0 hf l1 log1), PInv c pr h0 hf l3 log1 := fun hf I' =>
        I'.regs put3 left3 have3 next3 (by omega) B3'.hold_lt
      have wfL : sL.WellFormed := by rw [hsL]; exact wf_with wf1 _ rfl rfl rfl
      have short3 : l3.bits.toNat < 8 := by
        have m3 : l1.bits.toNat ≤ max l.bits.toNat ((3 : UInt32).toNat + 7) := mx
        simp only [show (3 : UInt32).toNat = 3 from rfl] at m3
        have m4 : l1.bits.toNat ≤ 10 := Nat.le_trans m3 (Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩)
        omega
      rcases hcases with rfl | rfl | rfl | rfl
      · refine ⟨.ok (), l3, setI h1 i { sL with mode := STORED }, ?_, log1,
          regs _ (I1.setState hs1 { sL with mode := STORED } (by rw [hsL]) (by rw [hsL]) (by rw [hsL])
            (wf_with wfL _ rfl rfl rfl) (modeOk_of (Or.inl rfl))),
          Or.inl ⟨rfl, measure _ { sL with mode := STORED } (by simp [setI])⟩,
          fun _ => Short.of_mode (sF := { sL with mode := STORED }) (by simp [setI]) (Or.inr (Or.inr rfl))⟩
        unfold back_TYPE
        simp only [runX_bind, runX_lift_ok (rdS_ok I.cst hs _), hl0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          run1, hr1, runX_lift_ok hw1, hd1, hb2, runX_lift_ok (setMode_ok I1.cst hs2 STORED), hd2]
        simp only [setI_setI]
      · have hfx : Zlib.Inftrees.inflate_fixed c.st (setI h1 i sL) =
            .ok ((), setI (setI h1 i sL) i (Zlib.Inftrees.Proofs.fixedState sL)) := by
          rw [I1.cst]; have := Zlib.Inftrees.Proofs.inflate_fixed_ok hs2; rwa [C.run] at this
        have hs3 : (setI (setI h1 i sL) i (Zlib.Inftrees.Proofs.fixedState sL)).istates i =
            some (Zlib.Inftrees.Proofs.fixedState sL) := by simp [setI]
        refine ⟨.ok (), l3, setI h1 i { Zlib.Inftrees.Proofs.fixedState sL with mode := LEN }, ?_, log1,
          regs _ (I1.setState hs1 { Zlib.Inftrees.Proofs.fixedState sL with mode := LEN } (by rw [hsL]; rfl)
            (by rw [hsL]; rfl) (by rw [hsL]; rfl) (wf_with wfL _ rfl rfl rfl) (modeOk_fixed i sL)),
          Or.inl ⟨rfl, measure _ { Zlib.Inftrees.Proofs.fixedState sL with mode := LEN } (by simp [setI])⟩,
          fun _ => Short.of_bits short3⟩
        unfold back_TYPE
        simp only [runX_bind, runX_lift_ok (rdS_ok I.cst hs _), hl0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          run1, hr1, runX_lift_ok hw1, hd1, hb2, runX_lift_ok hfx, runX_lift_ok (setMode_ok I1.cst hs3 LEN), hd2]
        simp only [setI_setI]
      · refine ⟨.ok (), l3, setI h1 i { sL with mode := TABLE }, ?_, log1,
          regs _ (I1.setState hs1 { sL with mode := TABLE } (by rw [hsL]) (by rw [hsL]) (by rw [hsL])
            (wf_with wfL _ rfl rfl rfl) (modeOk_of (Or.inr (Or.inl rfl)))),
          Or.inl ⟨rfl, measure _ { sL with mode := TABLE } (by simp [setI])⟩, fun _ => Short.of_bits short3⟩
        unfold back_TYPE
        simp only [runX_bind, runX_lift_ok (rdS_ok I.cst hs _), hl0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          run1, hr1, runX_lift_ok hw1, hd1, hb2, runX_lift_ok (setMode_ok I1.cst hs2 TABLE), hd2]
        simp only [setI_setI]
      · have hzA : r.get (setI h1 i sL) = some z1 := by simpa using hzs1
        obtain ⟨k, hbad⟩ := badMode_run c I1.cstrm I1.cst hzA hs2 "invalid block type" msg_block_type
        have IA := I1.setState hs1 sL (by rw [hsL]) (by rw [hsL]) (by rw [hsL]) wfL (by rw [hsL]; exact I1.mode s1 hs1)
        have IB := IA.putMsg hzA (.ref (.str k) 0)
        have hsB : (r.put (setI h1 i sL) { z1 with msg := .ref (.str k) 0 }).istates i = some sL := by simp [setI]
        have IC := IB.setState hsB { sL with mode := BAD } rfl rfl rfl (wf_with wfL _ rfl rfl rfl)
          (modeOk_of (Or.inr (Or.inr (Or.inr rfl))))
        refine ⟨.ok (), l3, setI (r.put (setI h1 i sL) { z1 with msg := .ref (.str k) 0 }) i { sL with mode := BAD }, ?_,
          log1, regs _ IC, Or.inl ⟨rfl, measure _ { sL with mode := BAD } (by simp [setI])⟩,
          fun _ => Short.of_mode (sF := { sL with mode := BAD }) (by simp [setI]) (Or.inl rfl)⟩
        unfold back_TYPE
        simp only [runX_bind, runX_lift_ok (rdS_ok I.cst hs _), hl0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          run1, hr1, runX_lift_ok hw1, hd1, hb2]
        show runX (liftM (badMode c "invalid block type") >>= fun _ => DROPBITS 2) l2 (setI h1 i sL) = _
        simp only [runX_bind, runX_lift_ok hbad, hd2]

end Zlib.Infback.Safety
