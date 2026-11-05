import ZlibF.Proof.«inflate.c.main.xloop»

/-!
# inflate.c: the bit-buffer macros

`PULLBYTE`, `NEEDBITS`, `BITS`, `DROPBITS`, `BYTEBITS` and `INITBITS` of `inflate()` against the bit-stream invariant
`BitInv`: the registers `next`, `have`, `hold`, `bits` describe the unconsumed DEFLATE bit stream
`natBits bits hold ++ bytesBits bs`, where `bs` are the input bytes not yet pulled. Migrated from the earlier attempt's
`InflateBits`; the byte-block pointer facts are now facts about `Space.get h r`. None of these macros writes the heap.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate

theorem runX_get (l : IL) (h : Heap) : runX (get : X IL) l h = .ok ((.ok l, l), h) := rfl
theorem runX_set (l l' : IL) (h : Heap) : runX (set l' : X PUnit) l h = .ok ((.ok (), l'), h) := rfl
theorem runX_throw {α : Type} (e : Ex) (l : IL) (h : Heap) : runX (throw e : X α) l h = .ok ((.error e, l), h) := rfl
theorem runX_modify (f : IL → IL) (l : IL) (h : Heap) : runX (modify f : X PUnit) l h = .ok ((.ok (), f l), h) := rfl
theorem runX_lift {α : Type} (m : M α) (l : IL) (h : Heap) :
    runX (monadLift m : X α) l h = match m h with
      | .ok (a, h') => .ok ((.ok a, l), h')
      | .error e => .error e := by
  unfold runX
  rcases hm : m h with e | ⟨a, h'⟩ <;>
    simp [hm, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.run, ExceptT.mk, StateT.lift, StateT.run,
      Functor.map, StateT.map, ExceptT.map, bind_app]

/-- The registers describe the bit stream `natBits bits hold` followed by the bytes `bs` at `next`. -/
structure BitInv (h : Heap) (l : IL) (bs : List UInt8) : Prop where
  have_eq : l.have_.toNat = bs.length
  next : bs = [] ∨ ∃ (r : BRef) (a : Array UInt8) (off : Nat), l.next = .ref r off ∧
    (Space.get h r : Option (Array UInt8)) = some a ∧ off + bs.length ≤ a.size ∧
    bs = (a.toList.drop off).take bs.length
  hold_lt : l.hold.toNat < 2 ^ l.bits.toNat

/-- The unconsumed bit stream. -/
def stream (l : IL) (bs : List UInt8) : List Bool := natBits l.bits.toNat l.hold.toNat ++ bytesBits bs

/-- The registers after one successful `PULLBYTE` of the byte `b`, the pointer now `nx`. -/
def pulled (l : IL) (b : UInt8) (nx : BPtr) : IL :=
  { l with have_ := l.have_ - 1, next := nx, hold := l.hold + (b.toUInt64 <<< l.bits.toUInt64), bits := l.bits + 8 }

/-- `PULLBYTE` with no input left (`have = 0`): `goto inf_leave` with the registers and the heap unchanged. -/
theorem PULLBYTE_zero {l : IL} {h : Heap} (h0 : l.have_ = 0) :
    runX PULLBYTE l h = .ok ((.error Ex.leave, l), h) := by
  unfold PULLBYTE
  simp [runX_bind, runX_get, h0, runX_throw]

theorem runX_lift_ok {α : Type} {m : M α} {a : α} {h h' : Heap} (e : m h = .ok (a, h')) (l : IL) :
    runX (monadLift m : X α) l h = .ok ((.ok a, l), h') := by
  rw [runX_lift, e]

theorem take_succ_drop (a : Array UInt8) (off n : Nat) (h : off + n + 1 ≤ a.size) :
    (a.toList.drop off).take (n + 1) = a[off] :: (a.toList.drop (off + 1)).take n := by
  have : off < a.toList.length := by simp; omega
  rw [List.drop_eq_getElem_cons this]
  simp

theorem hold_add_lt (hold b P : Nat) (hh : hold < P) (hb : b < 256) : hold + b * P < 256 * P := by
  have : (b + 1) * P ≤ 256 * P := Nat.mul_le_mul_right _ hb
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem u32_add8 (x : UInt32) (hx : x.toNat ≤ 56) : (x + 8).toNat = x.toNat + 8 := by
  rw [UInt32.toNat_add]; simp; omega

/-- The hold word after pulling the byte `b` below `bits ≤ 56` held bits. -/
theorem pull_hold (hold : UInt64) (b : UInt8) (bits : UInt32) (hb : bits.toNat ≤ 56) (hh : hold.toNat < 2 ^ bits.toNat) :
    (hold + (b.toUInt64 <<< bits.toUInt64)).toNat = hold.toNat + b.toNat * 2 ^ bits.toNat ∧
    hold.toNat + b.toNat * 2 ^ bits.toNat < 2 ^ (bits.toNat + 8) := by
  have hK : (256 : Nat) * 2 ^ 56 = 2 ^ 64 := by decide
  have hpow : 2 ^ bits.toNat ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hb
  have hlt := hold_add_lt hold.toNat b.toNat _ hh (UInt8.toNat_lt b)
  have h256 : 256 * 2 ^ bits.toNat ≤ 2 ^ 64 := by
    have := Nat.mul_le_mul_left 256 hpow
    omega
  have hm : b.toNat * 2 ^ bits.toNat < 2 ^ 64 := by omega
  have hsh : (b.toUInt64 <<< bits.toUInt64).toNat = b.toNat * 2 ^ bits.toNat := by
    have := shl64_toNat b.toUInt64 bits (by omega) (by simpa using hm)
    simpa using this
  have hsum : (hold + (b.toUInt64 <<< bits.toUInt64)).toNat = hold.toNat + b.toNat * 2 ^ bits.toNat := by
    rw [UInt64.toNat_add, hsh]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hsum, ?_⟩
  rw [Nat.pow_add]
  omega

/-- `PULLBYTE` with the next input byte `b` at `next` (a readable byte array; `bits <= 56` so the shift does not overflow): no fault, the byte is appended to the bit buffer, `next` moves one byte, `have` drops by one, and the bit stream is the same as before. -/
theorem PULLBYTE_succ {h : Heap} {l : IL} {b : UInt8} {bs : List UInt8} (B : BitInv h l (b :: bs))
    (hb : l.bits.toNat ≤ 56) :
    ∃ nx, runX PULLBYTE l h = .ok ((.ok (), pulled l b nx), h) ∧ BitInv h (pulled l b nx) bs ∧
      stream (pulled l b nx) bs = stream l (b :: bs) ∧ (pulled l b nx).bits.toNat = l.bits.toNat + 8 := by
  have hne0 : l.have_ ≠ 0 := fun e => by have := B.have_eq; rw [e] at this; simp at this
  have hne : (l.have_ == 0) = false := by simpa using hne0
  obtain ⟨r, a, off, hnext, hg, hsz, hbs⟩ := B.next.resolve_left (by simp)
  have hsz' : off + bs.length + 1 ≤ a.size := by simp at hsz; omega
  have hlt : off < a.size := by omega
  have hbs' : b :: bs = a[off] :: (a.toList.drop (off + 1)).take bs.length := by
    have := take_succ_drop a off bs.length hsz'
    simp only [List.length_cons] at hbs
    rw [← this]; exact hbs
  have hbb : a[off] = b := by injection hbs' with h1; exact h1.symm
  have hbs2 : bs = (a.toList.drop (off + 1)).take bs.length := by injection hbs' with _ h2
  have hlb : l.bits.toNat < 64 := by omega
  obtain ⟨hsum, hlt2⟩ := pull_hold l.hold b l.bits hb B.hold_lt
  have hadd : OkOn h (l.next.add 1) (.ref r (off + 1)) := by
    rw [hnext]; exact Ptr.add_nat_ok (n := 1) hg (by omega)
  have hld : OkOn h (load8 l.next) b := by
    rw [hnext]
    have := Ptr.load_ok (h := h) (r := r) (off := off) hg hlt
    rw [hbb] at this; exact this
  have hshl : shl64 b.toUInt64 l.bits h = .ok (b.toUInt64 <<< l.bits.toUInt64, h) := by
    rw [shl64_run _ _ hlb]; rfl
  have hbn := u32_add8 l.bits hb
  refine ⟨.ref r (off + 1), ?_, ?_, ?_, by simp [pulled, hbn]⟩
  · unfold PULLBYTE
    rw [runX_bind, runX_get]
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    simp only [runX_bind, runX_set, runX_lift_ok hld, runX_lift_ok hadd, runX_lift_ok hshl]
    rfl
  · refine ⟨?_, Or.inr ⟨r, a, off + 1, rfl, hg, by omega, hbs2⟩, ?_⟩
    · have := B.have_eq
      simp only [pulled, List.length_cons] at this ⊢
      rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; simp; omega)]
      simp; omega
    · simp only [pulled, hbn, hsum]; exact hlt2
  · unfold stream
    simp only [pulled, hbn, hsum]
    rw [natBits_pull _ _ _ B.hold_lt (UInt8.toNat_lt _), List.append_assoc, bytesBits_cons]

/-! ## NEEDBITS -/

theorem runX_cond_lt (n : UInt32) (l : IL) (h : Heap) :
    runX (do return (← get).bits < n : X Bool) l h = .ok ((.ok (decide (l.bits < n)), l), h) := rfl

/-- What every state of the `NEEDBITS` loop satisfies: `j` input bytes of `bs` were pulled from the start registers `l0`. -/
def NBase (h : Heap) (l0 : IL) (bs : List UInt8) (n : UInt32) (l1 : IL) (j : Nat) : Prop :=
  j ≤ bs.length ∧ BitInv h l1 (bs.drop j) ∧ stream l1 (bs.drop j) = stream l0 bs ∧
    l1.bits.toNat = l0.bits.toNat + 8 * j ∧
    l1 = { l0 with next := l1.next, have_ := l1.have_, hold := l1.hold, bits := l1.bits } ∧
    l1.bits.toNat ≤ max l0.bits.toNat (n.toNat + 7) ∧ (j = 0 → l1 = l0)

/-- `NEEDBITS` loop invariant: `k` iterations remain. -/
def NInv (h : Heap) (l0 : IL) (bs : List UInt8) (n : UInt32) (k : Nat) (l1 : IL) (h1 : Heap) : Prop :=
  h1 = h ∧ ∃ j, NBase h l0 bs n l1 j ∧ k = (if l1.bits.toNat < n.toNat then min ((n.toNat - l1.bits.toNat + 7) / 8) (bs.length - j + 1) else 0)

/-- `NEEDBITS(n)` for `n ≤ 49`: either enough bits are held afterwards (`ok`), or the input ran out (`goto inf_leave`, all
input pulled, still fewer than `n` bits). Only `next`, `have`, `hold`, `bits` change, the stream is preserved, and nothing is
pulled when `n` bits are already held. -/
theorem NEEDBITS_run {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs) (n : UInt32) (hn : n.toNat ≤ 49) :
    ∃ r l' j, runX (NEEDBITS n) l h = .ok ((r, l'), h) ∧ j ≤ bs.length ∧ BitInv h l' (bs.drop j) ∧
      stream l' (bs.drop j) = stream l bs ∧ l'.bits.toNat = l.bits.toNat + 8 * j ∧
      l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits } ∧
      l'.bits.toNat ≤ max l.bits.toNat (n.toNat + 7) ∧ (n.toNat ≤ l.bits.toNat → l' = l) ∧
      (r = .ok () → n.toNat ≤ l'.bits.toNat) ∧
      (r = .error Ex.leave → j = bs.length ∧ l'.have_ = 0 ∧ l'.bits.toNat < n.toNat) := by
  have hlen : bs.length < 2 ^ 32 := by
    have := B.have_eq; have := UInt32.toNat_lt l.have_; simp at *; omega
  have key := xwhileBrk_run (cond := (do return (← get).bits < n : X Bool)) (body := (do PULLBYTE; pure false : X Bool))
    (NInv h l bs n)
    (fun r l1 h1 => h1 = h ∧ ∃ j, NBase h l bs n l1 j ∧ (r = .ok () → n.toNat ≤ l1.bits.toNat) ∧
      (r = .error Ex.leave → j = bs.length ∧ l1.have_ = 0 ∧ l1.bits.toNat < n.toNat))
    (fun k l1 h1 hP => by
      obtain ⟨hh, j, hb, hk⟩ := hP
      subst hh
      have hnl : l1.bits.toNat < n.toNat := by
        by_cases hc : l1.bits.toNat < n.toNat
        · exact hc
        · rw [if_neg hc] at hk; omega
      have hnl' : l1.bits < n := UInt32.lt_iff_toNat_lt.mpr hnl
      obtain ⟨hj, hB, hS, hbits, hshape, hmax, hz⟩ := hb
      have hcond : runX (do return (← get).bits < n : X Bool) l1 h1 = .ok ((.ok true, l1), h1) := by
        rw [runX_cond_lt]; simp [hnl']
      refine ⟨l1, h1, hcond, ?_⟩
      by_cases h0 : l1.have_ = 0
      · refine ⟨.error Ex.leave, l1, h1, ?_, ?_⟩
        · rw [runX_bind, PULLBYTE_zero h0]
        · have := hB.have_eq
          have h00 : l1.have_.toNat = 0 := by rw [h0]; rfl
          simp only [List.length_drop] at this
          refine ⟨rfl, j, ⟨hj, hB, hS, hbits, hshape, hmax, hz⟩, (fun e => nomatch e), fun _ => ⟨by omega, h0, hnl⟩⟩
      · have hlenj : j < bs.length := by
          have := hB.have_eq
          simp only [List.length_drop] at this
          apply Decidable.byContradiction
          intro hc
          apply h0
          have : l1.have_.toNat = 0 := by omega
          exact UInt32.toNat_inj.mp (by simpa using this)
        have hdrop : bs.drop j = bs[j] :: bs.drop (j + 1) := List.drop_eq_getElem_cons hlenj
        rw [hdrop] at hB hS
        obtain ⟨nx, hrun, hB2, hS2, hb2⟩ := PULLBYTE_succ hB (by omega)
        refine ⟨.ok false, pulled l1 bs[j] nx, h1, ?_, ?_⟩
        · rw [runX_bind, hrun]; rfl
        · refine ⟨rfl, j + 1, ⟨by omega, hB2, ?_, by omega, ?_, by omega, by omega⟩, ?_⟩
          · rw [hS2, hS]
          · rw [hshape]; simp [pulled]
          · rw [if_pos hnl] at hk
            rw [hb2]
            split <;> omega)

    (fun l1 h1 hP => by
      obtain ⟨hh, j, hb, hk⟩ := hP
      subst hh
      have hnl : ¬ l1.bits.toNat < n.toNat := by intro hl; rw [if_pos hl] at hk; omega
      refine ⟨l1, h1, by rw [runX_cond_lt]; simp [UInt32.lt_iff_toNat_lt, hnl], rfl, j, hb, ?_, ?_⟩
      · intro _
        omega
      · intro e; cases e)
    (k := (if l.bits.toNat < n.toNat then min ((n.toNat - l.bits.toNat + 7) / 8) (bs.length + 1) else 0)) (l := l) (h := h)
    ⟨rfl, 0, ⟨by omega, by simpa using B, by simp [stream], by simp, by simp, by omega, fun _ => rfl⟩, by simp⟩
    (by unfold fuel; split <;> omega)
  obtain ⟨r, l', h', hr, rfl, j, hb, hq1, hq2⟩ := key
  obtain ⟨hj, hB, hS, hbits, hshape, hmax, hz⟩ := hb
  refine ⟨r, l', j, by unfold NEEDBITS xwhile; exact hr, hj, hB, hS, hbits, hshape, hmax, ?_, hq1, hq2⟩
  intro hge
  by_cases hj0 : j = 0
  · exact hz hj0
  · exfalso; omega

/-! ## BITS, DROPBITS, BYTEBITS, INITBITS -/

/-- `BITS(n)` for `n < 32`: no fault, the low `n` bits of `hold`; nothing else changes. -/
theorem BITS_run (l : IL) (h : Heap) (n : UInt32) (hn : n.toNat < 32) :
    runX (BITS n) l h = .ok ((.ok (l.hold.toUInt32 &&& ((1 : UInt32) <<< n - 1)), l), h) := by
  have hs : shl32 1 n h = .ok (1 <<< n, h) := by rw [shl32_run _ _ hn]; rfl
  unfold BITS
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_lift_ok hs]
  rfl

/-- The value of `BITS(n)` is `hold % 2^n`. -/
theorem BITS_toNat (l : IL) (n : UInt32) (hn : n.toNat < 32) :
    (l.hold.toUInt32 &&& ((1 : UInt32) <<< n - 1)).toNat = l.hold.toNat % 2 ^ n.toNat := by
  rw [land_mask32 _ n.toNat _ (mask_toNat n hn)]
  simp only [UInt64.toNat_toUInt32]
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- `DROPBITS(n)` for `n < 64`: no fault, `hold` shifts right and `bits` drops by `n`. -/
theorem DROPBITS_run (l : IL) (h : Heap) (n : UInt32) (hn : n.toNat < 64) :
    runX (DROPBITS n) l h = .ok ((.ok (), { l with hold := l.hold >>> n.toUInt64, bits := l.bits - n }), h) := by
  have hs : shr64 l.hold n h = .ok (l.hold >>> n.toUInt64, h) := by rw [shr64_run _ _ hn]; rfl
  unfold DROPBITS
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_lift_ok hs]
  rfl

/-- `DROPBITS(n)` consumes the first `n` stream bits. -/
theorem DROPBITS_inv {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs) (n : UInt32)
    (hn : n.toNat ≤ l.bits.toNat) (hn64 : n.toNat < 64) :
    BitInv h { l with hold := l.hold >>> n.toUInt64, bits := l.bits - n } bs ∧
    stream { l with hold := l.hold >>> n.toUInt64, bits := l.bits - n } bs = (stream l bs).drop n.toNat ∧
    (l.bits - n).toNat = l.bits.toNat - n.toNat := by
  have hlt := B.hold_lt
  have hsub : (l.bits - n).toNat = l.bits.toNat - n.toNat :=
    UInt32.toNat_sub_of_le _ _ (UInt32.le_iff_toNat_le.mpr hn)
  have hsh := shr64_toNat l.hold n hn64
  refine ⟨⟨B.have_eq, B.next, ?_⟩, ?_, hsub⟩
  · simp only [hsub, hsh]
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel hn]
    exact hlt
  · unfold stream
    simp only [hsub, hsh]
    rw [List.drop_append_of_le_length (by simp [natBits_length]; exact hn), natBits_drop _ _ _ hn]

/-- The registers after `BYTEBITS()`. -/
def bytebits (l : IL) : IL :=
  { l with hold := l.hold >>> (l.bits &&& 7).toUInt64, bits := l.bits - (l.bits &&& 7) }

theorem and7_le (l : IL) : (l.bits &&& 7).toNat ≤ l.bits.toNat := by
  rw [UInt32.toNat_and]; exact Nat.and_le_left

theorem and7_toNat (l : IL) : (l.bits &&& 7).toNat = l.bits.toNat % 8 := by
  rw [UInt32.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 3

theorem and7_lt (l : IL) : (l.bits &&& 7).toNat < 64 := by
  rw [and7_toNat]; omega

/-- `BYTEBITS()`: no fault, the registers become `bytebits`. -/
theorem BYTEBITS_run (l : IL) (h : Heap) : runX BYTEBITS l h = .ok ((.ok (), bytebits l), h) := by
  have hs : shr64 l.hold (l.bits &&& 7) h = .ok (l.hold >>> (l.bits &&& 7).toUInt64, h) := by
    rw [shr64_run _ _ (and7_lt l)]; rfl
  unfold BYTEBITS
  rw [runX_bind, runX_get]
  simp only []
  rw [runX_bind, runX_lift_ok hs]
  rfl

/-- `BYTEBITS()` discards the `bits % 8` stream bits up to the next byte boundary. -/
theorem BYTEBITS_inv {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs) :
    BitInv h (bytebits l) bs ∧ stream (bytebits l) bs = (stream l bs).drop (l.bits.toNat % 8) ∧
    (bytebits l).bits.toNat % 8 = 0 := by
  obtain ⟨B', hs, hsub⟩ := DROPBITS_inv B (l.bits &&& 7) (and7_le l) (and7_lt l)
  rw [and7_toNat] at hs hsub
  refine ⟨B', hs, ?_⟩
  show (l.bits - (l.bits &&& 7)).toNat % 8 = 0
  rw [hsub]
  omega

/-- `INITBITS()` empties the bit buffer. -/
theorem INITBITS_inv {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs) :
    BitInv h { l with hold := 0, bits := 0 } bs ∧
    stream { l with hold := 0, bits := 0 } bs = bytesBits bs := by
  refine ⟨⟨B.have_eq, B.next, by simp⟩, ?_⟩
  simp [stream, natBits]

theorem runX_INITBITS (l : IL) (h : Heap) : runX INITBITS l h = .ok ((.ok (), { l with hold := 0, bits := 0 }), h) := rfl

end Zlib.Inflate.Proofs
