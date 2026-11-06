import ZlibF.Proof.«infback.c.pull»
import ZlibF.Proof.«infback.c.pure»
import ZlibF.Proof.«infback.c.wf»
import ZlibF.Proof.«inflate.c.main.stored»
import ZlibF.Proof.«inflate.c.main.stored2»

/-!
# infback.c: `ROOM()` on the loop invariant, and `case STORED`
-/

namespace Zlib.Infback.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Infback Zlib.Infback.Spec

/-- Registers with the same input fields describe the same chunk. -/
theorem BIn.regs_eq {ownI : Nat → Prop} {h : Heap} {l l' : IL} {bs : List UInt8} (B : BIn ownI h l bs)
    (hn : l'.next = l.next) (hh : l'.have_ = l.have_) (hho : l'.hold = l.hold) (hb : l'.bits = l.bits) :
    BIn ownI h l' bs := by
  obtain ⟨⟨he, hn', hl⟩, ho⟩ := B
  refine ⟨⟨by rw [hh]; exact he, by rw [hn]; exact hn', by rw [hho, hb]; exact hl⟩, by rw [hn]; exact ho⟩

/-- Like `LInv.cb`, but the window position may move (`ROOM()` restarts at the window). -/
theorem LInv.cb' {c : BCtx} {win : Nat} {ownI own : Nat → Prop} {R : Heap → Prop} {r : ZStreamRef} {zs : Nat}
    {h h' : Heap} {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8} (I : LInv c win ownI R r zs h l z s bs)
    (F : CbFrame own h h') (hw : ¬ own win) (hR' : R h') {l' : IL} {bs' : List UInt8}
    (hp : ∃ off, s.window = .ref (.blk win) off ∧ l'.put = .ref (.blk win) (off + (s.wsize.toNat - l'.left.toNat)) ∧
      l'.left.toNat ≤ s.wsize.toNat) (B' : BIn ownI h' l' bs') (hb : l'.bits.toNat ≤ 39) :
    LInv c win ownI R r zs h' l' z s bs' := by
  obtain ⟨hcs, hct, hz, hs, wf, ⟨o1, a, w1, ba, ro, le⟩, pt, B, hR, hb0⟩ := I
  exact ⟨hcs, hct, by rw [CbFrame.zget F]; exact hz, by rw [F.istates]; exact hs, wf,
    ⟨o1, a, w1, by rw [F.bytes win hw]; exact ba, by rw [F.ro]; exact ro, le⟩, hp, B', hR', hb⟩

/-- **`ROOM()` on the invariant.** The window is the caller's, so `out` is called on `wsize` readable bytes. Afterwards the
invariant holds with the state `{ s with whave := w }` (only `whave` changes); on `ok` there is room (`left /= 0`, using
`wsize /= 0`) and the input registers are as before; on a leave the result is `Z_BUF_ERROR`. -/
theorem ROOM_inv (c : BCtx) {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {μ : Heap → Nat} (hF : InFinite c ownI R μ)
    {r : ZStreamRef} {zs : Nat} {h : Heap} {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (I : LInv c win ownI R r zs h l z s bs) (hw0 : 0 < s.wsize.toNat) :
    ∃ res l' h' w, runX (ROOM c) l h = .ok ((res, l'), h') ∧
      LInv c win ownI R r zs h' l' z { s with whave := w } bs ∧ phi μ h' l' = phi μ h l ∧
      l'.next = l.next ∧ l'.have_ = l.have_ ∧ l'.hold = l.hold ∧ l'.bits = l.bits ∧ l'.copy = l.copy ∧
      (res = .ok () → l'.left ≠ 0) ∧ (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) := by
  by_cases hl : l.left = 0
  · obtain ⟨o1, a, w1, ba, ro, le⟩ := I.wnd
    have hRd : ReadableAt h s.window s.wsize.toNat := ⟨win, o1, a, w1, ba, le⟩
    obtain ⟨res, l', h', hrun, F, hR', hres⟩ := ROOM_run c hK I.cst I.hs hl I.hR hRd
    have I1 := Zlib.Infback.Proofs.LInv.setS I { s with whave := s.wsize } rfl rfl rfl rfl rfl (LInv.R_setI hK I.hR zs _)
    have hsame : ∀ b, ownI b → h'.bytes b = (roomHeap h zs s).bytes b := fun b hb => F.bytes b (hK.disj.2.2 b hb)
    have Bh : BIn ownI h' l bs := @BIn.congr ownI h h' l bs (fun b hb => hsame b hb) I.bin
    have Bn : BIn ownI h' l' bs := by
      rcases hres with ⟨-, e⟩ | ⟨-, e⟩ <;> exact BIn.regs_eq Bh (by rw [e]) (by rw [e]) (by rw [e]) (by rw [e])
    have hp : ∃ off, ({ s with whave := s.wsize } : InflateState).window = .ref (.blk win) off ∧
        l'.put = .ref (.blk win) (off + (({ s with whave := s.wsize } : InflateState).wsize.toNat - l'.left.toNat)) ∧
        l'.left.toNat ≤ ({ s with whave := s.wsize } : InflateState).wsize.toNat := by
      obtain ⟨off, hw, -, -⟩ := I.put
      rcases hres with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> refine ⟨off, hw, ?_, by simp⟩ <;> simp [hw]
    have hb39 : l'.bits.toNat ≤ 39 := by
      have := I.bits; rcases hres with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> simpa using this
    refine ⟨res, l', h', s.wsize, hrun, Zlib.Infback.Proofs.LInv.cb' I1 F hK.disj.2.1 hR' hp Bn hb39, ?_, ?_⟩
    · simp only [phi]
      rw [hF.local_ h h' (fun b hb => (hsame b hb))]
      rcases hres with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> rfl
    · rcases hres with ⟨h1, e⟩ | ⟨h1, e⟩ <;> rw [e]
      · refine ⟨rfl, rfl, rfl, rfl, rfl, fun _ => ?_, fun e he => ?_⟩
        · intro hh
          have hz : s.wsize.toNat = 0 := by rw [show s.wsize = 0 from hh]; rfl
          omega
        · rw [h1] at he; cases he
      · refine ⟨rfl, rfl, rfl, rfl, rfl, fun hh => ?_, fun e he => ?_⟩
        · rw [h1] at hh; cases hh
        · rw [h1] at he; cases he; exact ⟨rfl, rfl⟩
  · refine ⟨.ok (), l, h, s.whave, ROOM_have c hl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => hl, fun e he => by cases he⟩
    · have : ({ s with whave := s.whave } : InflateState) = s := rfl
      rw [this]; exact I

/-! ## `case STORED` -/

/-- The copy count of `case STORED`: `min(length, have, left)`, written with the two `if`s of the C. -/
def clampCopy (len hv lf : UInt32) : UInt32 :=
  let c1 := if len > hv then hv else len
  if c1 > lf then lf else c1

theorem clampCopy_le (len hv lf : UInt32) : (clampCopy len hv lf).toNat ≤ len.toNat ∧
    (clampCopy len hv lf).toNat ≤ hv.toNat ∧ (clampCopy len hv lf).toNat ≤ lf.toNat := by
  unfold clampCopy
  simp only [GT.gt, UInt32.lt_iff_toNat_lt]
  split <;> split <;> omega

theorem clampCopy_pos (len hv lf : UInt32) (h1 : len ≠ 0) (h2 : hv ≠ 0) (h3 : lf ≠ 0) : clampCopy len hv lf ≠ 0 := by
  have e1 : 0 < len.toNat := by
    apply Nat.pos_of_ne_zero; intro e; exact h1 (UInt32.toNat_inj.mp (by simpa using e))
  have e2 : 0 < hv.toNat := by
    apply Nat.pos_of_ne_zero; intro e; exact h2 (UInt32.toNat_inj.mp (by simpa using e))
  have e3 : 0 < lf.toNat := by
    apply Nat.pos_of_ne_zero; intro e; exact h3 (UInt32.toNat_inj.mp (by simpa using e))
  intro e
  have := congrArg UInt32.toNat e
  unfold clampCopy at this
  simp only [GT.gt, UInt32.lt_iff_toNat_lt] at this
  split at this <;> split at this <;> simp at this <;> omega

/-- The part of the copy loop after `ROOM()`. -/
def storedTail (c : BCtx) : X Unit := do
  let l ← get
  let mut copy := l.copy
  if copy > l.have_ then copy := l.have_
  if copy > l.left then copy := l.left
  memcpyB l.put l.next copy.toNat
  let nx ← l.next.add (copy.toNat : Int)
  let pt ← l.put.add (copy.toNat : Int)
  set { l with copy := copy, have_ := l.have_ - copy, next := nx, left := l.left - copy, put := pt }
  wrS c.st fun s => { s with length := s.length - copy }

/-- The heap after the copy: `n` bytes written into the window block, and `state->length` set to `L`. -/
def copiedHeap (h : Heap) (zs win : Nat) (s : InflateState) (da sa : Array UInt8) (od off2 n : Nat) (L : UInt32) : Heap :=
  setI { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n)) } zs { s with length := L }

/-- The registers after the copy of `n` bytes. -/
def storedRegs (l : IL) (n : UInt32) (bb off2 win od : Nat) : IL :=
  { l with copy := n, have_ := l.have_ - n, next := .ref (.blk bb) (off2 + n.toNat), left := l.left - n, put := .ref (.blk win) (od + n.toNat) }

/-- **The copy of one piece.** `n = min(length, have, left)` bytes move from the input chunk (block `bb`) to the window (block
`win`); the two blocks differ, both ranges are inside their blocks. The heap changes in the window block and in
`state->length`. -/
theorem storedTail_run (c : BCtx) {h : Heap} {l : IL} {zs : Nat} {s : InflateState} {bb off2 win od : Nat}
    {da sa : Array UInt8} (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (hput : l.put = .ref (.blk win) od) (hnext : l.next = .ref (.blk bb) off2)
    (hd : h.bytes win = some da) (hsa : h.bytes bb = some sa) (hro : h.ro win = false) (hne : win ≠ bb)
    (hhave : l.have_ ≠ 0) (hleft : l.left ≠ 0) (hcopy : l.copy ≠ 0)
    (h1 : od + l.left.toNat ≤ da.size) (h2 : off2 + l.have_.toNat ≤ sa.size) :
    runX (storedTail c) l h = .ok ((.ok (), storedRegs l (clampCopy l.copy l.have_ l.left) bb off2 win od),
      copiedHeap h zs win s da sa od off2 (clampCopy l.copy l.have_ l.left).toNat (s.length - clampCopy l.copy l.have_ l.left)) := by
  obtain ⟨hn1, hn2, hn3⟩ := clampCopy_le l.copy l.have_ l.left
  obtain ⟨n, hn⟩ : ∃ n, n = clampCopy l.copy l.have_ l.left := ⟨_, rfl⟩
  rw [← hn] at hn1 hn2 hn3 ⊢
  have hmc : memcpyB l.put l.next n.toNat h = .ok ((), { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) }) := by
    rw [hput, hnext]; exact memcpyB_blk_ok hd hsa hro hne (by omega) (by omega)
  have hsz : (copyRange da sa od off2 n.toNat).size = da.size := size_copyRange _ _ _ _ _
  have hdg : (Space.get h (BRef.blk win) : Option (Array UInt8)) = some da := hd
  have hsg : (Space.get h (BRef.blk bb) : Option (Array UInt8)) = some sa := hsa
  obtain ⟨a2, ha2, hs2⟩ := get_after_put hd hsz hsg
  obtain ⟨a3, ha3, hs3⟩ := get_after_put hd hsz hdg
  have hadd1 : OkOn { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) } (l.next.add (n.toNat : Int))
      (.ref (.blk bb) (off2 + n.toNat)) := by
    rw [hnext]; exact Ptr.add_nat_ok ha2 (by omega)
  have hadd2 : OkOn { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) } (l.put.add (n.toNat : Int))
      (.ref (.blk win) (od + n.toNat)) := by
    rw [hput]; exact Ptr.add_nat_ok ha3 (by omega)
  have hs' : ({ h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) } : Heap).istates zs = some s := hs
  have hw : wrS c.st (fun s => { s with length := s.length - n })
      { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) } =
      .ok ((), setI { h with bytes := upd h.bytes win (some (copyRange da sa od off2 n.toNat)) } zs
        { s with length := s.length - n }) := wrS_ok hc hs' _
  unfold storedTail storedRegs copiedHeap
  rw [runX_bind, runX_get]
  by_cases e1 : l.copy > l.have_
  · by_cases e2 : l.have_ > l.left
    · have hv : n = l.left := by rw [hn]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok hmc, runX_lift_ok hadd1, runX_lift_ok hadd2, runX_set,
        runX_lift_ok hw]
    · have hv : n = l.have_ := by rw [hn]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok hmc, runX_lift_ok hadd1, runX_lift_ok hadd2, runX_set,
        runX_lift_ok hw]
  · by_cases e2 : l.copy > l.left
    · have hv : n = l.left := by rw [hn]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok hmc, runX_lift_ok hadd1, runX_lift_ok hadd2, runX_set,
        runX_lift_ok hw]
    · have hv : n = l.copy := by rw [hn]; simp only [clampCopy, e1, e2, ↓reduceIte]
      subst hv
      simp only [e1, e2, ↓reduceIte, runX_bind, runX_lift_ok hmc, runX_lift_ok hadd1, runX_lift_ok hadd2, runX_set,
        runX_lift_ok hw]

/-- The loop body of `case STORED`. -/
def storedBody (c : BCtx) : X Unit := do
  let s ← ldInflateState c.st
  modify fun l => { l with copy := s.length }
  PULL c
  ROOM c
  storedTail c

/-- The condition of the copy loop. -/
def storedCond (c : BCtx) : X Bool := do return (← rdS c.st (·.length)) != 0

/-- `case STORED` as the function `back_STORED`, with the loop split into `storedCond` and `storedBody`. -/
theorem back_STORED_eq (c : BCtx) : back_STORED c = (do
    BYTEBITS
    NEEDBITS c 32
    let l ← get
    if (l.hold &&& (0xffff : UInt64)) != ((l.hold >>> 16) ^^^ (0xffff : UInt64)) then
      badMode c "invalid stored block lengths"
      return
    wrS c.st fun s => { s with length := l.hold.toUInt32 &&& 0xffff }
    INITBITS
    xwhile (storedCond c) (storedBody c)
    setMode c.st TYPE) := rfl

theorem drop_take_drop (a : List UInt8) (o k n : Nat) :
    ((a.drop o).take k).drop n = (a.drop (o + n)).take (k - n) := by
  rw [List.drop_take, List.drop_drop]
  all_goals (try (congr 2; omega))

/-- The invariant after `storedTail`: `n` bytes of the chunk were copied into the window. -/
theorem LInv.copied {c : BCtx} {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {r : ZStreamRef} {zs : Nat} {h : Heap} {l : IL}
    {z : ZStream} {s : InflateState} {bs : List UInt8} (I : LInv c win ownI R r zs h l z s bs) {bb off2 od : Nat}
    {da sa : Array UInt8} (hnext : l.next = .ref (.blk bb) off2) (hown : ownI bb) (hsa : h.bytes bb = some sa)
    (hd : h.bytes win = some da) (hne : win ≠ bb)
    (hput : l.put = .ref (.blk win) od) (hodl : ∃ off, s.window = .ref (.blk win) off ∧
      od = off + (s.wsize.toNat - l.left.toNat))
    (n : UInt32) (hn1 : n.toNat ≤ l.have_.toNat) (hn2 : n.toNat ≤ l.left.toNat) (L : UInt32) :
    LInv c win ownI R r zs (copiedHeap h zs win s da sa od off2 n.toNat L)
      (storedRegs l n bb off2 win od) z { s with length := L } (bs.drop n.toNat) := by
  unfold storedRegs copiedHeap
  obtain ⟨hcs, hct, hz, hs, wf, ⟨o1, a, w1, ba, ro, le⟩, ⟨o2, w2, pp, pl⟩, B, hR, hb⟩ := I
  obtain ⟨o3, w3, hod⟩ := hodl
  have ho12 : o3 = o1 := (Ptr.ref.inj (w3.symm.trans w1)).2
  have hda : a = da := by rw [hd] at ba; exact (Option.some.inj ba).symm
  subst hda
  have hsz : (copyRange a sa od off2 n.toNat).size = a.size := size_copyRange _ _ _ _ _
  have hbn : h.bytes bb = some sa := hsa
  have hL : (l.left - n).toNat = l.left.toNat - n.toNat := UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hn2)
  have hH : (l.have_ - n).toNat = l.have_.toNat - n.toNat := UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hn1)
  have hbb : ∀ b, b ≠ win → (upd h.bytes win (some (copyRange a sa od off2 n.toNat))) b = h.bytes b :=
    fun b hb => upd_ne _ _ _ _ hb
  refine ⟨hcs, hct, by cases r <;> simpa [ZStreamRef.get] using hz, by simp, wf_with wf _ rfl rfl rfl, ⟨o1, copyRange a sa od off2 n.toNat, w1, ?_, ?_, ?_⟩,
    ⟨o2, w2, ?_, ?_⟩, ?_, ?_, hb⟩
  · show (upd h.bytes win (some (copyRange a sa od off2 n.toNat))) win = _
    simp
  · simpa using ro
  · rw [hsz]; exact le
  · rw [hL, hod, ho12]; simp only []
    have := pl
    have e : o1 + (s.wsize.toNat - l.left.toNat) + n.toNat = o2 + (s.wsize.toNat - (l.left.toNat - n.toNat)) := by
      have : o2 = o1 := (Ptr.ref.inj (w2.symm.trans w1)).2
      omega
    rw [e]
  · simp only []; omega
  · -- the chunk
    refine ⟨?_, ?_⟩
    · rcases B.bit.next with e0 | ⟨r', a', off', hn', hg', hsz', hbs'⟩
      · have e1 : bs = [] := e0
        subst e1
        refine ⟨by simp only [List.drop_nil, List.length_nil, hH]; have := B.bit.have_eq; simp at this; omega, Or.inl (by simp), B.bit.hold_lt⟩
      · rw [hnext] at hn'
        obtain ⟨h1, h2⟩ := Ptr.ref.inj hn'
        subst h1; subst h2
        have hsa' : a' = sa := by have : h.bytes bb = some a' := hg'; rw [hsa] at this; exact (Option.some.inj this).symm
        rw [hsa'] at hsz' hbs'
        refine ⟨?_, ?_, B.bit.hold_lt⟩
        · simp only [List.length_drop, hH]; have := B.bit.have_eq; omega
        · by_cases hz0 : (bs.drop n.toNat) = []
          · exact Or.inl hz0
          · right
            refine ⟨.blk bb, sa, off2 + n.toNat, rfl, ?_, ?_, ?_⟩
            · show (upd h.bytes win (some (copyRange a sa od off2 n.toNat))) bb = _
              rw [hbb bb (fun e => hne e.symm)]; exact hsa
            · simp only [List.length_drop]; have := B.bit.have_eq; omega
            · have e2 : bs.drop n.toNat = (sa.toList.drop (off2 + n.toNat)).take (bs.length - n.toNat) := by
                have := drop_take_drop sa.toList off2 bs.length n.toNat
                rw [← hbs'] at this; exact this
              simp only [List.length_drop]
              exact e2
    · rcases B.own with e0 | ⟨b', o', hb', hob'⟩
      · left; subst e0; simp
      · right
        rw [hnext] at hb'
        obtain ⟨h1, h2⟩ := Ptr.ref.inj hb'
        exact ⟨bb, off2 + n.toNat, rfl, hown⟩
  · apply (hK.local_ h _ _).1 hR
    intro b hb'
    have hbw : b ≠ win := by
      rcases hb' with hb' | hb'
      · intro e; subst e; exact hK.disj.1 hb'
      · intro e; subst e; exact hK.disj.2.1 hb'
    show (upd h.bytes win (some (copyRange a sa od off2 n.toNat))) b = h.bytes b
    exact hbb b hbw

/-- **One trip of the copy loop of `case STORED`.** A stored block with `length /= 0` bytes left: `PULL()`, `ROOM()`, then
`min(length, have, left) >= 1` bytes move from the chunk to the window. Either the call ends at `PULL`/`ROOM` with `Z_BUF_ERROR`
(`in` ended, or `out` failed), or the invariant holds again with a smaller `length` and less input to read. Only `whave` and
`length` of the state change; the bit buffer is untouched. -/
theorem stored_body_run (c : BCtx) {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {μ : Heap → Nat} (hF : InFinite c ownI R μ)
    {r : ZStreamRef} {zs : Nat} {h : Heap} {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (I : LInv c win ownI R r zs h l z s bs) (hw0 : 0 < s.wsize.toNat) (hlen : s.length ≠ 0) :
    ∃ res l' h' s' bs', runX (storedBody c) l h = .ok ((res, l'), h') ∧ LInv c win ownI R r zs h' l' z s' bs' ∧
      (∃ w n, s' = { s with whave := w, length := n }) ∧ l'.bits = l.bits ∧ l'.hold = l.hold ∧
      (res = .ok () → s'.length.toNat < s.length.toNat ∧ phi μ h' l' < phi μ h l) ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR ∧ phi μ h' l' ≤ phi μ h l) := by
  have hld : ldInflateState c.st h = .ok (s, h) := by rw [I.cst]; exact ldInflateState_tab I.hs
  have I0 : LInv c win ownI R r zs h { l with copy := s.length } z s bs :=
    Zlib.Infback.Proofs.LInv.regs I rfl rfl (BIn.regs_eq I.bin rfl rfl rfl rfl) I.bits
  obtain ⟨r1, l1, h1, bs1, hp, F1, R1, B1, Hok1, Hl1, He1, Hbh1, Ph1⟩ := PULL_run c hK hF I0.bin I.hR
  have hphi0 : phi μ h { l with copy := s.length } = phi μ h l := rfl
  cases r1 with
  | error e =>
    have he := He1 e rfl
    subst he
    have hE := Hl1 rfl
    have I1 := Zlib.Infback.Proofs.LInv.cb I0 F1 hK.disj.1 R1 (l' := l1) (by rw [hE]; rfl) (by rw [hE]; rfl) B1
      (by rw [hE]; exact I.bits)
    refine ⟨.error Ex.leave, l1, h1, s, bs1, ?_, I1, ⟨s.whave, s.length, rfl⟩, by rw [hE]; rfl, by rw [hE]; rfl,
      (fun h0 => by cases h0), fun e he => ?_⟩
    · unfold storedBody
      rw [runX_bind, runX_lift_ok hld]; simp only []
      rw [runX_bind, runX_modify]; simp only []
      rw [runX_bind, hp]
    · cases he
      exact ⟨rfl, by rw [hE]; rfl, by rw [hphi0] at Ph1; exact Ph1⟩
  | ok u =>
    cases u
    obtain ⟨hh1, hS1⟩ := Hok1 rfl
    have hp1 : l1.put = l.put := by rw [hS1]
    have hl1 : l1.left = l.left := by rw [hS1]
    have hc1 : l1.copy = s.length := by rw [hS1]
    have hbits1 : l1.bits = l.bits := Hbh1.1
    have hhold1 : l1.hold = l.hold := Hbh1.2
    have I1 := Zlib.Infback.Proofs.LInv.cb I0 F1 hK.disj.1 R1 (l' := l1) hp1 hl1 B1 (by rw [hbits1]; exact I.bits)
    obtain ⟨res2, l2, h2, w, hr2, I2, Phi2, hn2, hh2, hho2, hbi2, hco2, hlf2, he2⟩ := ROOM_inv c hK hF I1 hw0
    have hrun_pre : runX (storedBody c) l h = runX (ROOM c >>= fun _ => storedTail c) l1 h1 := by
      unfold storedBody
      rw [runX_bind, runX_lift_ok hld]; simp only []
      rw [runX_bind, runX_modify]; simp only []
      rw [runX_bind, hp]
    have hphi01 : phi μ h1 l1 ≤ phi μ h l := Ph1
    cases res2 with
    | error e =>
      have he := (he2 e rfl).1
      subst he
      refine ⟨.error Ex.leave, l2, h2, { s with whave := w }, bs1, ?_, I2, ⟨w, s.length, rfl⟩, by rw [hbi2, hbits1],
        by rw [hho2, hhold1], (fun h0 => by cases h0), fun e he => ?_⟩
      · rw [hrun_pre, runX_bind, hr2]
      · cases he
        exact ⟨rfl, (he2 _ rfl).2, by omega⟩
    | ok u2 =>
      cases u2
      have hleft2 := hlf2 rfl
      obtain ⟨hcs2, hct2, hz2, hs2, wf2, ⟨o1, da, w1, ba, ro, le⟩, ⟨o2, w2, pp, pl⟩, B2, hR2, hb2⟩ := I2
      have hhave2 : l2.have_ ≠ 0 := by rw [hh2]; exact hh1
      have hbs1 : bs1 ≠ [] := by
        intro e
        have := B2.bit.have_eq
        rw [e] at this
        exact hhave2 (UInt32.toNat_inj.mp (by simpa using this))
      obtain ⟨bb, off2, hnx2, hown⟩ := B2.own.resolve_left hbs1
      obtain ⟨r', sa, off', hn', hg', hsz', hbs'⟩ := B2.bit.next.resolve_left hbs1
      rw [hnx2] at hn'
      obtain ⟨h1', h2'⟩ := Ptr.ref.inj hn'
      subst h1'; subst h2'
      have hsa : h2.bytes bb = some sa := hg'
      have hne : win ≠ bb := fun e => hK.disj.1 (e ▸ hown)
      have hcopy2 : l2.copy ≠ 0 := by rw [hco2, hc1]; exact hlen
      have ho21 : o2 = o1 := (Ptr.ref.inj (w2.symm.trans w1)).2
      have hhv : l2.have_.toNat = bs1.length := B2.bit.have_eq
      have Ihold : LInv c win ownI R r zs h2 l2 z { s with whave := w } bs1 :=
        ⟨hcs2, hct2, hz2, hs2, wf2, ⟨o1, da, w1, ba, ro, le⟩, ⟨o2, w2, pp, pl⟩, B2, hR2, hb2⟩
      have hle' : o1 + s.wsize.toNat ≤ da.size := le
      have hpl' : l2.left.toNat ≤ s.wsize.toNat := pl
      have hodsz : o2 + (s.wsize.toNat - l2.left.toNat) + l2.left.toNat ≤ da.size := by omega
      have hrt := storedTail_run c (h := h2) (l := l2) (zs := zs) (s := { s with whave := w }) (bb := bb) (off2 := off2)
        (win := win) (od := o2 + (s.wsize.toNat - l2.left.toNat)) (da := da) (sa := sa) hct2 hs2 pp hnx2 ba hsa ro hne
        hhave2 hleft2 hcopy2 hodsz (by omega)
      obtain ⟨n1, n2, n3⟩ := clampCopy_le l2.copy l2.have_ l2.left
      have hnpos : clampCopy l2.copy l2.have_ l2.left ≠ 0 := clampCopy_pos _ _ _ hcopy2 hhave2 hleft2
      have hnpos' : 0 < (clampCopy l2.copy l2.have_ l2.left).toNat := by
        apply Nat.pos_of_ne_zero; intro e; exact hnpos (UInt32.toNat_inj.mp (by simpa using e))
      have Ifin := LInv.copied hK Ihold hnx2 hown hsa ba hne pp ⟨o2, w2, rfl⟩ (clampCopy l2.copy l2.have_ l2.left) (by omega)
        (by omega) ({ s with whave := w }.length - clampCopy l2.copy l2.have_ l2.left)
      refine ⟨.ok (), _, _, { s with whave := w, length := s.length - clampCopy l2.copy l2.have_ l2.left },
        _, ?_, Ifin, ⟨w, _, rfl⟩, (by show l2.bits = l.bits; rw [hbi2, hbits1]), (by show l2.hold = l.hold; rw [hho2, hhold1]),
        fun _ => ⟨?_, ?_⟩, fun e he => by cases he⟩
      · rw [hrun_pre, runX_bind, hr2]; exact hrt
      · have : (s.length - clampCopy l2.copy l2.have_ l2.left).toNat = s.length.toNat - (clampCopy l2.copy l2.have_ l2.left).toNat :=
          UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (Nat.le_trans n1 (Nat.le_of_eq (by rw [hco2, hc1]))))
        have hsl : 0 < s.length.toNat := by
          apply Nat.pos_of_ne_zero; intro e; exact hlen (UInt32.toNat_inj.mp (by simpa using e))
        simp only [this]; omega
      · have hmu : μ (copiedHeap h2 zs win { s with whave := w } da sa (o2 + (s.wsize.toNat - l2.left.toNat)) off2 (clampCopy l2.copy l2.have_ l2.left).toNat ({ s with whave := w }.length - clampCopy l2.copy l2.have_ l2.left)) = μ h2 := by
          apply hF.local_
          intro b hb'
          have hbw : b ≠ win := by
            intro e; subst e; exact hK.disj.1 hb'
          show (upd h2.bytes win (some (copyRange da sa (o2 + (s.wsize.toNat - l2.left.toNat)) off2 (clampCopy l2.copy l2.have_ l2.left).toNat))) b = h2.bytes b
          exact upd_ne _ _ _ _ hbw
        have hH : (l2.have_ - clampCopy l2.copy l2.have_ l2.left).toNat = l2.have_.toNat - (clampCopy l2.copy l2.have_ l2.left).toNat :=
          UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr n2)
        simp only [phi, storedRegs] at Phi2 hphi01 ⊢
        rw [hmu]
        simp only [hH]
        omega

/-- The length of the state record in the heap (0 if there is none): the measure of the copy loop. -/
def stLen (zs : Nat) (h : Heap) : Nat := match h.istates zs with
  | some s => s.length.toNat
  | none => 0

theorem stLen_of {zs : Nat} {h : Heap} {s : InflateState} (hs : h.istates zs = some s) : stLen zs h = s.length.toNat := by
  simp [stLen, hs]

/-- **The copy loop of `case STORED`.** From the registers `l` (no bits held), with `s.length` bytes to go: either `in`/`out`
ended the call (`Z_BUF_ERROR`), or all `length` bytes were copied and the state's `length` is 0. Only `whave` and `length`
change in the state. -/
theorem stored_loop_run (c : BCtx) {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {μ : Heap → Nat} (hF : InFinite c ownI R μ)
    {r : ZStreamRef} {zs : Nat} {h : Heap} {l : IL} {z : ZStream} {s0 : InflateState} {bs : List UInt8}
    (hw0 : 0 < s0.wsize.toNat) (I : LInv c win ownI R r zs h l z s0 bs) :
    ∃ res l' h' s' bs', runX (xwhile (storedCond c) (storedBody c)) l h = .ok ((res, l'), h') ∧
      LInv c win ownI R r zs h' l' z s' bs' ∧ (∃ w n, s' = { s0 with whave := w, length := n }) ∧
      l'.bits = l.bits ∧ l'.hold = l.hold ∧ phi μ h' l' ≤ phi μ h l ∧
      (res = .ok () → s'.length = 0) ∧ (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR) := by
  have key := xwhileBrk_wf (cond := storedCond c) (body := (do storedBody c; pure false : X Bool))
    (fun l1 h1 => ∃ s1 bs1, LInv c win ownI R r zs h1 l1 z s1 bs1 ∧ (∃ w n, s1 = { s0 with whave := w, length := n }) ∧
      l1.bits = l.bits ∧ l1.hold = l.hold ∧ phi μ h1 l1 ≤ phi μ h l)
    (fun res l1 h1 => ∃ s1 bs1, LInv c win ownI R r zs h1 l1 z s1 bs1 ∧ (∃ w n, s1 = { s0 with whave := w, length := n }) ∧
      l1.bits = l.bits ∧ l1.hold = l.hold ∧ phi μ h1 l1 ≤ phi μ h l ∧
      (res = .ok () → s1.length = 0) ∧ (∀ e, res = .error e → e = Ex.leave ∧ l1.ret = Z_BUF_ERROR))
    (fun _ h1 => stLen zs h1)
    (fun l1 h1 hI => by
      obtain ⟨s1, bs1, I1, ⟨w, n, hs1⟩, hb1, hh1, hp1⟩ := hI
      have hwsz : s1.wsize = s0.wsize := by rw [hs1]
      have hw1 : 0 < s1.wsize.toNat := by rw [hwsz]; exact hw0
      have hcond : runX (storedCond c) l1 h1 = .ok ((.ok (s1.length != 0), l1), h1) := by
        unfold storedCond
        rw [runX_bind, runX_lift_ok (rdS_ok I1.cst I1.hs _)]; rfl
      refine ⟨l1, h1, s1.length != 0, hcond, fun hT => ?_, fun hF' => ?_⟩
      · have hne : s1.length ≠ 0 := by simpa using hT
        obtain ⟨res, l2, h2, s2, bs2, hrun, I2, ⟨w2, n2, hs2⟩, hb2, hh2, hok, herr⟩ :=
          stored_body_run c hK hF I1 hw1 hne
        cases res with
        | ok u =>
          cases u
          obtain ⟨hlt, hph⟩ := hok rfl
          refine ⟨.ok false, l2, h2, ?_, ?_⟩
          · rw [runX_bind, hrun]; rfl
          · refine ⟨⟨s2, bs2, I2, ⟨w2, n2, by rw [hs2, hs1]⟩, by rw [hb2, hb1], by rw [hh2, hh1], by omega⟩, ?_⟩
            rw [stLen_of I2.hs, stLen_of I1.hs]; exact hlt
        | error e =>
          obtain ⟨he, hret, hph⟩ := herr e rfl
          subst he
          refine ⟨.error Ex.leave, l2, h2, ?_, ?_⟩
          · rw [runX_bind, hrun]
          · exact ⟨s2, bs2, I2, ⟨w2, n2, by rw [hs2, hs1]⟩, by rw [hb2, hb1], by rw [hh2, hh1], by omega, (fun h0 => by cases h0),
              (fun e he => by cases he; exact ⟨rfl, hret⟩)⟩
      · have h0 : s1.length = 0 := by simpa using hF'
        exact ⟨s1, bs1, I1, ⟨w, n, hs1⟩, hb1, hh1, hp1, fun _ => h0, fun e he => by cases he⟩)
    (l := l) (h := h)
    ⟨s0, bs, I, ⟨s0.whave, s0.length, rfl⟩, rfl, rfl, Nat.le_refl _⟩
    (by rw [stLen_of I.hs]; have := UInt32.toNat_lt s0.length; unfold fuel; omega)
  obtain ⟨res, l', h', hr, s', bs', I', hs', hb', hh', hp', hz, he⟩ := key
  exact ⟨res, l', h', s', bs', by unfold xwhile; exact hr, I', hs', hb', hh', hp', hz, he⟩

/-- **`case STORED`** (stored block): `BYTEBITS`, `NEEDBITS(32)`, the length check, then the copy loop. The result is one of:
`Z_BUF_ERROR` (`in` ended or `out` failed); the lengths do not match ("invalid stored block lengths", mode `BAD`, no input
consumed beyond the alignment bits); or all `length` bytes were copied and the mode is `TYPE`, with at least 32 input bits
consumed. The invariant holds in every case; `wsize` is untouched. -/
theorem stored_run (c : BCtx) {win : Nat} {ownI ownO : Nat → Prop} {R : Heap → Prop}
    (hK : CbContract c.inCb c.inDesc c.outCb c.outDesc win ownI ownO R) {μ : Heap → Nat} (hF : InFinite c ownI R μ)
    {r : ZStreamRef} {zs : Nat} {h : Heap} {l : IL} {z : ZStream} {s : InflateState} {bs : List UInt8}
    (I : LInv c win ownI R r zs h l z s bs) (hw0 : 0 < s.wsize.toNat) :
    ∃ res l' h' z' s' bs', runX (back_STORED c) l h = .ok ((res, l'), h') ∧ LInv c win ownI R r zs h' l' z' s' bs' ∧
      s'.wsize = s.wsize ∧
      (∀ e, res = .error e → e = Ex.leave ∧ l'.ret = Z_BUF_ERROR ∧ phi μ h' l' ≤ phi μ h l) ∧
      (res = .ok () → (s'.mode = BAD ∧ phi μ h' l' ≤ phi μ h l) ∨ (s'.mode = TYPE ∧ phi μ h' l' + 32 ≤ phi μ h l)) := by
  obtain ⟨B1b, -, hb1b⟩ := BYTEBITS_inv I.bin.bit
  have hbl : (bytebits l).bits.toNat ≤ l.bits.toNat := by
    show (l.bits - (l.bits &&& 7)).toNat ≤ _
    rw [UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr (and7_le l))]; omega
  have Ib : LInv c win ownI R r zs h (bytebits l) z s bs :=
    Zlib.Infback.Proofs.LInv.regs I rfl rfl ⟨B1b, I.bin.own⟩ (by have := I.bits; omega)
  have hphib : phi μ h (bytebits l) ≤ phi μ h l := by
    simp only [phi]; have : (bytebits l).have_ = l.have_ := rfl
    rw [this]; omega
  obtain ⟨res0, l1, h1, bs1, hr1, F1, R1, B1, M1, Z1, Hok, Hleave, Herr, Ph1⟩ :=
    NEEDBITS_run c hK hF Ib.bin I.hR 32 (by decide)
  have h32 : (32 : UInt32).toNat = 32 := rfl
  have hb39 : l1.bits.toNat ≤ 39 := by
    have := Ib.bits; rw [h32] at M1; omega
  cases res0 with
  | error e =>
    have he := Herr e rfl
    subst he
    have hE := Hleave rfl
    have hp : l1.put = (bytebits l).put := by rw [hE]
    have hlf : l1.left = (bytebits l).left := by rw [hE]
    have I1 := Zlib.Infback.Proofs.LInv.cb Ib F1 hK.disj.1 R1 hp hlf B1 hb39
    refine ⟨.error Ex.leave, l1, h1, z, s, bs1, ?_, I1, rfl, ?_, fun h0 => by cases h0⟩
    · rw [back_STORED_eq]
      simp only [runX_bind, BYTEBITS_run, hr1]
    · intro e he
      cases he
      exact ⟨rfl, by rw [hE], by omega⟩
  | ok u =>
    cases u
    obtain ⟨h32', hS⟩ := Hok rfl
    have hp : l1.put = (bytebits l).put := by rw [hS]
    have hlf : l1.left = (bytebits l).left := by rw [hS]
    have I1 := Zlib.Infback.Proofs.LInv.cb Ib F1 hK.disj.1 R1 hp hlf B1 hb39
    by_cases hcond : ((l1.hold &&& (0xffff : UInt64)) != ((l1.hold >>> 16) ^^^ (0xffff : UInt64))) = true
    · -- the lengths do not match
      obtain ⟨i, hbad⟩ := badMode_run c I1.cstrm I1.cst I1.hz I1.hs "invalid stored block lengths"
        Zlib.Inflate.Proofs.lit_invalid_stored
      have hRm : R (r.put h1 { z with msg := .ref (.str i) 0 }) :=
        (hK.local_ h1 _ (fun b _ => by simp)).1 I1.hR
      have Iz := Zlib.Infback.Proofs.LInv.putMsg I1 (.ref (.str i) 0) hRm
      have I2 := Zlib.Infback.Proofs.LInv.setS Iz { s with mode := BAD } rfl rfl rfl rfl rfl (LInv.R_setI hK Iz.hR zs _)
      have hbad' : badMode c "invalid stored block lengths" h1 =
          .ok ((), setI (r.put h1 { z with msg := .ref (.str i) 0 }) zs { s with mode := BAD }) := hbad
      refine ⟨.ok (), l1, setI (r.put h1 { z with msg := .ref (.str i) 0 }) zs { s with mode := BAD },
        { z with msg := .ref (.str i) 0 }, { s with mode := BAD }, bs1, ?_, I2, rfl, (fun e he => by cases he),
        fun _ => Or.inl ⟨rfl, ?_⟩⟩
      · rw [back_STORED_eq]
        simp only [runX_bind, BYTEBITS_run, hr1, runX_get, hcond, ↓reduceIte, runX_lift_ok hbad']
        rfl
      · have hmu : μ (setI (r.put h1 { z with msg := .ref (.str i) 0 }) zs { s with mode := BAD }) = μ h1 :=
          hF.local_ _ _ (fun b _ => by simp)
        simp only [phi] at Ph1 hphib ⊢
        rw [hmu]; omega
    · -- the lengths match: copy
      have hcond' : ((l1.hold &&& (0xffff : UInt64)) != ((l1.hold >>> 16) ^^^ (0xffff : UInt64))) = false := by simpa using hcond
      obtain ⟨sL, hsLd⟩ : ∃ sL : InflateState, sL = { s with length := l1.hold.toUInt32 &&& 0xffff } := ⟨_, rfl⟩
      have hI2 := Zlib.Infback.Proofs.LInv.setS I1 sL (by rw [hsLd]) (by rw [hsLd]) (by rw [hsLd]) (by rw [hsLd])
        (by rw [hsLd]) (LInv.R_setI hK I1.hR zs _)
      obtain ⟨Bi, hsi⟩ := INITBITS_inv I1.bin.bit
      have hwL : 0 < sL.wsize.toNat := by rw [hsLd]; exact hw0
      have hIL : LInv c win ownI R r zs (setI h1 zs sL) { l1 with hold := 0, bits := 0 } z sL bs1 :=
        Zlib.Infback.Proofs.LInv.regs hI2 rfl rfl
          (@BIn.congr ownI h1 (setI h1 zs sL) _ bs1 (fun _ _ => rfl) ⟨Bi, I1.bin.own⟩) (by simp)
      obtain ⟨res3, l3, h3, s3, bs3, hr3, I3, ⟨w, n, hs3⟩, hb3, hh3, hp3, hz3, he3⟩ := stored_loop_run c hK hF hwL hIL
      have hmu2 : μ (setI h1 zs sL) = μ h1 := hF.local_ _ _ (fun b _ => rfl)
      have hld : wrS c.st (fun s => { s with length := l1.hold.toUInt32 &&& 0xffff }) h1 = .ok ((), setI h1 zs sL) := by
        rw [wrS_ok I1.cst I1.hs, hsLd]
      have hpre : runX (back_STORED c) l h = runX (xwhile (storedCond c) (storedBody c) >>= fun _ => setMode c.st TYPE)
          { l1 with hold := 0, bits := 0 } (setI h1 zs sL) := by
        rw [back_STORED_eq]
        simp only [runX_bind, BYTEBITS_run, hr1, runX_get, hcond', Bool.false_eq_true, ↓reduceIte, runX_lift_ok hld,
          runX_INITBITS]
      cases res3 with
      | error e =>
        have he := (he3 e rfl).1
        subst he
        refine ⟨.error Ex.leave, l3, h3, z, s3, bs3, ?_, I3, ?_, ?_, fun h0 => by cases h0⟩
        · rw [hpre, runX_bind, hr3]
        · rw [hs3, hsLd]
        · intro e he'
          cases he'
          refine ⟨rfl, (he3 _ rfl).2, ?_⟩
          have : l3.bits = 0 := by rw [hb3]
          simp only [phi] at Ph1 hphib hp3 ⊢
          rw [hmu2] at hp3
          try dsimp only at hp3 ⊢
          have hbb : (l1 : IL).bits.toNat ≥ 32 := h32'
          have hl3b : l3.bits.toNat = 0 := by have := congrArg UInt32.toNat hb3; simpa using this
          have e1' : ({ l1 with hold := 0, bits := 0 } : IL).have_.toNat = l1.have_.toNat := rfl
          have e2' : ({ l1 with hold := 0, bits := 0 } : IL).bits.toNat = 0 := rfl
          have e3' : (bytebits l).have_.toNat = l.have_.toNat := rfl
          have e4' : (bytebits l).bits.toNat ≤ l.bits.toNat := hbl
          have e0 : (0 : UInt32).toNat = 0 := rfl
          omega
      | ok u3 =>
        cases u3
        have hlen3 := hz3 rfl
        have I4 := Zlib.Infback.Proofs.LInv.setS I3 { s3 with mode := TYPE } rfl rfl rfl rfl rfl (LInv.R_setI hK I3.hR zs _)
        have hs3' : ((setI h3 zs { s3 with mode := TYPE }).istates zs) = some { s3 with mode := TYPE } := by simp
        have hst : setMode c.st TYPE h3 = .ok ((), setI h3 zs { s3 with mode := TYPE }) := setMode_ok I3.cst I3.hs TYPE
        refine ⟨.ok (), l3, setI h3 zs { s3 with mode := TYPE }, z, { s3 with mode := TYPE }, bs3, ?_, I4, ?_,
          (fun e he => by cases he), fun _ => Or.inr ⟨rfl, ?_⟩⟩
        · rw [hpre, runX_bind, hr3]
          simp only []
          rw [runX_lift_ok hst]
        · rw [hs3, hsLd]
        · have hmu3 : μ (setI h3 zs { s3 with mode := TYPE }) = μ h3 := hF.local_ _ _ (fun b _ => rfl)
          simp only [phi] at Ph1 hphib hp3 ⊢
          rw [hmu3]
          rw [hmu2] at hp3
          try dsimp only at hp3 ⊢
          have hbb : l1.bits.toNat ≥ 32 := h32'
          have hl3b : l3.bits.toNat = 0 := by have := congrArg UInt32.toNat hb3; simpa using this
          have e1' : ({ l1 with hold := 0, bits := 0 } : IL).have_.toNat = l1.have_.toNat := rfl
          have e2' : ({ l1 with hold := 0, bits := 0 } : IL).bits.toNat = 0 := rfl
          have e3' : (bytebits l).have_.toNat = l.have_.toNat := rfl
          have e4' : (bytebits l).bits.toNat ≤ l.bits.toNat := hbl
          have e0 : (0 : UInt32).toNat = 0 := rfl
          omega

end Zlib.Infback.Proofs
