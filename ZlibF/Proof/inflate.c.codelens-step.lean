import ZlibF.Proof.«inflate.c.dynamic-install»
import ZlibF.Proof.«inflate.c.bits-complete»
import ZlibF.Proof.«inflate.c.codelens-repeat»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

def clReadCond (c : Ctx) : X Bool := do
  let s ← ldInflateState c.st
  return s.have < s.nlen + s.ndist

def clAfterLookup (c : Ctx) (here : Code) : X Bool := do
      -- if (here.val < 16) { DROPBITS(here.bits); state->lens[state->have++] = here.val; }
      if here.val < 16 then
        DROPBITS here.bits.toUInt32
        let s ← ldInflateState c.st
        Ptr.store (← (lensP c.st).add (s.have.toNat : Int)) here.val
        wrS c.st fun s => { s with «have» := s.«have» + 1 }
        return false
      else
        if here.val == 16 then
          NEEDBITS (here.bits.toUInt32 + 2)
          DROPBITS here.bits.toUInt32
          -- if (state->have == 0) { "invalid bit length repeat"; BAD; break; }
          let s ← ldInflateState c.st
          if s.«have» == 0 then
            badMode c "invalid bit length repeat"
            return true
          -- len = state->lens[state->have - 1]; copy = 3 + BITS(2); DROPBITS(2);
          let v ← Ptr.index (lensP c.st) ((s.«have» - 1).toNat : Int)
          let b ← BITS 2
          modify fun l => { l with len := v.toUInt32, copy := 3 + b }
          DROPBITS 2
        else if here.val == 17 then
          NEEDBITS (here.bits.toUInt32 + 3)
          DROPBITS here.bits.toUInt32
          let b ← BITS 3
          modify fun l => { l with len := 0, copy := 3 + b }
          DROPBITS 3
        else
          NEEDBITS (here.bits.toUInt32 + 7)
          DROPBITS here.bits.toUInt32
          let b ← BITS 7
          modify fun l => { l with len := 0, copy := 11 + b }
          DROPBITS 7
        -- if (state->have + copy > state->nlen + state->ndist) { "invalid bit length repeat"; BAD; break; }
        let s ← ldInflateState c.st
        if s.«have» + (← get).copy > s.nlen + s.ndist then
          badMode c "invalid bit length repeat"
          return true
        -- while (copy--) state->lens[state->have++] = (unsigned short)len;
        clRepeat c
        return false


def clReadBody (c : Ctx) : X Bool := do
      lookup1 c false
      let here := (← get).here
      -- if (here.val < 16) { DROPBITS(here.bits); state->lens[state->have++] = here.val; }
      if here.val < 16 then
        DROPBITS here.bits.toUInt32
        let s ← ldInflateState c.st
        Ptr.store (← (lensP c.st).add (s.have.toNat : Int)) here.val
        wrS c.st fun s => { s with «have» := s.«have» + 1 }
        return false
      else
        if here.val == 16 then
          NEEDBITS (here.bits.toUInt32 + 2)
          DROPBITS here.bits.toUInt32
          -- if (state->have == 0) { "invalid bit length repeat"; BAD; break; }
          let s ← ldInflateState c.st
          if s.«have» == 0 then
            badMode c "invalid bit length repeat"
            return true
          -- len = state->lens[state->have - 1]; copy = 3 + BITS(2); DROPBITS(2);
          let v ← Ptr.index (lensP c.st) ((s.«have» - 1).toNat : Int)
          let b ← BITS 2
          modify fun l => { l with len := v.toUInt32, copy := 3 + b }
          DROPBITS 2
        else if here.val == 17 then
          NEEDBITS (here.bits.toUInt32 + 3)
          DROPBITS here.bits.toUInt32
          let b ← BITS 3
          modify fun l => { l with len := 0, copy := 3 + b }
          DROPBITS 3
        else
          NEEDBITS (here.bits.toUInt32 + 7)
          DROPBITS here.bits.toUInt32
          let b ← BITS 7
          modify fun l => { l with len := 0, copy := 11 + b }
          DROPBITS 7
        -- if (state->have + copy > state->nlen + state->ndist) { "invalid bit length repeat"; BAD; break; }
        let s ← ldInflateState c.st
        if s.«have» + (← get).copy > s.nlen + s.ndist then
          badMode c "invalid bit length repeat"
          return true
        -- while (copy--) state->lens[state->have++] = (unsigned short)len;
        clRepeat c
        return false

theorem clRead_eq (c : Ctx) : clRead c = xwhileBrk (clReadCond c) (clReadBody c) := rfl

theorem clReadBody_eq (c : Ctx) : clReadBody c = (do
    lookup1 c false
    let here := (← get).here
    clAfterLookup c here) := rfl

theorem BitInv.setI {h : Heap} {l : IL} {bs : List UInt8} (inv : BitInv h l bs)
    (zs : Nat) (s : InflateState) : BitInv (setI h zs s) l bs := by
  refine ⟨inv.have_eq, ?_, inv.hold_lt⟩
  rcases inv.next with empty | ⟨ref, array, offset, pointer, get, bound, contents⟩
  · exact Or.inl empty
  · refine Or.inr ⟨ref, array, offset, pointer, ?_, bound, contents⟩
    cases ref <;> exact get

theorem clWrite_initialized {s : InflateState} {value : UInt16}
    (size : s.lens.size = 320) (inside : s.«have».toNat < 320) (small : value.toNat ≤ 15)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15) :
    (clWrite s value).lens.size = 320 ∧
    (clWrite s value).«have».toNat = s.«have».toNat + 1 ∧
    ∀ k, k < (clWrite s value).«have».toNat → ((clWrite s value).lens.getD k 0).toNat ≤ 15 := by
  have count : (s.«have» + 1).toNat = s.«have».toNat + 1 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_one]
    rw [Nat.mod_eq_of_lt (by omega)]
  refine ⟨by simp only [clWrite, Array.size_set!, size], count, ?_⟩
  intro k bound
  change k < (s.«have» + 1).toNat at bound
  rw [count] at bound
  change ((s.lens.set! s.«have».toNat value).getD k 0).toNat ≤ 15
  rw [Zlib.Inftrees.Proofs.getD_set!]
  by_cases current : s.«have».toNat = k
  · rw [if_pos ⟨current, by omega⟩]
    exact small
  · rw [if_neg (fun both => current both.1)]
    exact initialized k (by omega)

/-- A literal code length executes its bit drop and actual bounded store.
No input byte or other heap storage is changed. -/
theorem clAfterLookup_literal_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat}
    {s : InflateState} {here : Code} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (inside : s.«have».toNat < 320)
    (literal : here.val.toNat < 16) (width : here.bits.toNat ≤ 7)
    (enough : here.bits.toNat ≤ l.bits.toNat) (B : BitInv h l bs)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15) :
    let afterRegs := { l with hold := l.hold >>> here.bits.toUInt32.toUInt64, bits := l.bits - here.bits.toUInt32 }
    runX (clAfterLookup c here) l h =
      .ok ((.ok false, afterRegs), setI h zs (clWrite s here.val)) ∧
    BitInv (setI h zs (clWrite s here.val)) afterRegs bs ∧
    stream afterRegs bs = (stream l bs).drop here.bits.toNat ∧
    (clWrite s here.val).«have».toNat = s.«have».toNat + 1 ∧
    (∀ k, k < (clWrite s here.val).«have».toNat → ((clWrite s here.val).lens.getD k 0).toNat ≤ 15) := by
  dsimp only
  have bits : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
  obtain ⟨dropInv, dropStream, _⟩ := DROPBITS_inv B here.bits.toUInt32
    (by simpa only [UInt8.toNat_toUInt32] using enough) bits
  have update := clWrite_initialized size inside (by omega : here.val.toNat ≤ 15) initialized
  refine ⟨?_, dropInv.setI zs _, by simpa only [UInt8.toNat_toUInt32] using dropStream,
    update.2.1, update.2.2⟩
  have lens := WRef.get_istate_lens hs
  have add := Ptr.add_nat_ok (off := 0) (n := s.«have».toNat) lens (by omega)
  unfold OkOn at add
  simp only [Nat.zero_add] at add
  have store := Ptr.store_ok (off := s.«have».toNat) (v := here.val) lens (by simp) (by omega)
  rw [WRef.put_istate_lens hs] at store
  change Ptr.store (.ref (WRef.istate_lens zs) s.«have».toNat) here.val h =
    .ok ((), setI h zs { s with lens := s.lens.set! s.«have».toNat here.val }) at store
  have test : here.val < 16 := by apply UInt16.lt_iff_toNat_lt.mpr; exact literal
  unfold clAfterLookup
  rw [if_pos test, hc]
  simp [runX_bind, DROPBITS_run l h here.bits.toUInt32 bits, runX_lift, ldI_eq, hs,
    lensP, add, store, wrI_eq, setI_setI, clWrite, runX_pure]

def clRepeatFinish (c : Ctx) : X Bool := do
  let s ← ldInflateState c.st
  if s.«have» + (← get).copy > s.nlen + s.ndist then
    badMode c "invalid bit length repeat"
    return true
  clRepeat c
  return false

/-- The repeat-overrun check uses nonwrapping counters derived from the
mode bounds. Overruns report BAD; permitted repeats execute the proved
write loop and make strict progress in the initialized length prefix. -/
theorem clRepeatFinish_run {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs))
    (hz : r.get h = some z) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (haveBound : s.«have».toNat ≤ s.nlen.toNat + s.ndist.toNat)
    (copyLo : 1 ≤ l.copy.toNat) (copyHi : l.copy.toNat ≤ 138) (value : l.len.toNat ≤ 15)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15) :
    (s.«have».toNat + l.copy.toNat > s.nlen.toNat + s.ndist.toNat →
      ∃ i, strTable[i]? = some "invalid bit length repeat" ∧
        runX (clRepeatFinish c) l h = .ok ((.ok true, l), tcBadHeap h r zs z s i)) ∧
    (s.«have».toNat + l.copy.toNat ≤ s.nlen.toNat + s.ndist.toNat →
      ∃ state,
        runX (clRepeatFinish c) l h =
          .ok ((.ok false, { l with copy := 0xffffffff }), setI h zs state) ∧
        state = { s with lens := state.lens, «have» := state.«have» } ∧
        state.lens.size = 320 ∧ state.«have».toNat = s.«have».toNat + l.copy.toNat ∧
        s.«have».toNat < state.«have».toNat ∧
        (∀ k, k < state.«have».toNat → (state.lens.getD k 0).toNat ≤ 15)) := by
  have sum : (s.nlen + s.ndist).toNat = s.nlen.toNat + s.ndist.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  have added : (s.«have» + l.copy).toNat = s.«have».toNat + l.copy.toNat := by
    rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
  constructor
  · intro overrun
    have test : s.«have» + l.copy > s.nlen + s.ndist := by
      change s.nlen + s.ndist < s.«have» + l.copy
      rw [UInt32.lt_iff_toNat_lt, sum, added]
      exact overrun
    obtain ⟨i, literal, bad⟩ := tcBadMode_run (c := c) "invalid bit length repeat"
      lit_bit_length_repeat hr hc hz hs
    refine ⟨i, literal, ?_⟩
    unfold clRepeatFinish
    rw [hc]
    simp [runX_bind, runX_lift, ldI_eq, hs, runX_get, test, bad, runX_pure]
  · intro room
    have test : ¬ s.«have» + l.copy > s.nlen + s.ndist := by
      change ¬ s.nlen + s.ndist < s.«have» + l.copy
      rw [UInt32.lt_iff_toNat_lt, sum, added]
      omega
    obtain ⟨state, run, frame, sz, count, initialized'⟩ :=
      clRepeat_run hc hs size (by omega) value initialized
    refine ⟨state, ?_, frame, sz, count, by omega, initialized'⟩
    unfold clRepeatFinish
    rw [hc]
    simp [runX_bind, runX_lift, ldI_eq, hs, runX_get, test, run, runX_pure]

def clZeroSetup (here : Code) (extra base : UInt32) : X Unit := do
  NEEDBITS (here.bits.toUInt32 + extra)
  DROPBITS here.bits.toUInt32
  let bits ← BITS extra
  modify fun l => { l with len := 0, copy := base + bits }
  DROPBITS extra

private theorem xbind_assoc {α β γ : Type} (x : X α) (f : α → X β) (g : β → X γ) :
    ((x >>= f) >>= g) = (x >>= fun a => f a >>= g) := by
  apply ExceptT.ext
  apply StateT.ext
  intro l
  funext h
  change runX ((x >>= f) >>= g) l h = runX (x >>= fun a => f a >>= g) l h
  simp only [runX_bind]
  cases run : runX x l h with
  | error fault => simp only [run]
  | ok pair =>
    obtain ⟨⟨value, regs⟩, after⟩ := pair
    cases value <;> simp only [run, runX_bind]

theorem clAfterLookup_zero17 (c : Ctx) (here : Code) (symbol : here.val = 17) :
    clAfterLookup c here = (do clZeroSetup here 3 3; clRepeatFinish c) := by
  unfold clAfterLookup clZeroSetup clRepeatFinish
  simp [symbol, xbind_assoc]

theorem clAfterLookup_zero18 (c : Ctx) (here : Code)
    (notLiteral : ¬ here.val < 16) (not16 : here.val ≠ 16) (not17 : here.val ≠ 17) :
    clAfterLookup c here = (do clZeroSetup here 7 11; clRepeatFinish c) := by
  unfold clAfterLookup clZeroSetup clRepeatFinish
  simp only [notLiteral, not16, not17, beq_iff_eq, ite_false, xbind_assoc]

/-- The zero-repeat branches obtain their length and copy bounds from
the actual extra bits. Input exhaustion remains an actual exception; no
repeat count is assumed as a callee contract. -/
theorem clZeroSetup_run_cursor {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    (here : Code) (extra base : UInt32) (width : here.bits.toNat ≤ 7)
    (extraBound : extra.toNat ≤ 7) (baseLo : 3 ≤ base.toNat) (baseHi : base.toNat ≤ 11) :
    ∃ result regs used,
      runX (clZeroSetup here extra base) l h = .ok ((result, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      regs = { l with next := regs.next, have_ := regs.have_, hold := regs.hold, bits := regs.bits, copy := regs.copy, len := regs.len } ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧
      (result = .ok () → regs.len = 0 ∧ 3 ≤ regs.copy.toNat ∧ regs.copy.toNat ≤ 138) ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  have total : (here.bits.toUInt32 + extra).toNat = here.bits.toNat + extra.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨result, regs, used, needRun, usedBound, needInv, _, bitCount, shape, bitBound, _, enough, _, _, cursor⟩ :=
    NEEDBITS_run_cursor B (here.bits.toUInt32 + extra) (by rw [total]; omega)
  cases result with
  | error fault =>
    refine ⟨.error fault, regs, used, ?_, usedBound, needInv, ?_, ?_, ?_, cursor, by omega⟩
    · unfold clZeroSetup
      rw [runX_bind, needRun]
    · rw [shape]
    · rw [total] at bitBound
      omega
    · intro impossible
      cases impossible
  | ok unit =>
    cases unit
    have available := enough rfl
    rw [total] at available bitBound
    have firstBound : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
    have extraSmall : extra.toNat < 32 := by omega
    let dropped := { regs with hold := regs.hold >>> here.bits.toUInt32.toUInt64, bits := regs.bits - here.bits.toUInt32 }
    obtain ⟨firstInv, _, firstCount⟩ := DROPBITS_inv needInv here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32]; omega) firstBound
    let bits := dropped.hold.toUInt32 &&& ((1 : UInt32) <<< extra - 1)
    have bitsNat : bits.toNat = dropped.hold.toNat % 2 ^ extra.toNat := BITS_toNat dropped extra extraSmall
    have bitsBound : bits.toNat < 128 := by
      have bound := Nat.mod_lt dropped.hold.toNat (Nat.two_pow_pos extra.toNat)
      have power : 2 ^ extra.toNat ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) extraBound
      omega
    have copyNat : (base + bits).toNat = base.toNat + bits.toNat := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    let prepared := { dropped with len := 0, copy := base + bits }
    have preparedInv : BitInv h prepared (bs.drop used) :=
      ⟨firstInv.have_eq, firstInv.next, firstInv.hold_lt⟩
    have secondEnough : extra.toNat ≤ prepared.bits.toNat := by
      change extra.toNat ≤ (regs.bits - here.bits.toUInt32).toNat
      rw [firstCount, UInt8.toNat_toUInt32]
      omega
    obtain ⟨finalInv, _, finalCount⟩ := DROPBITS_inv preparedInv extra secondEnough (by omega)
    let final := { prepared with hold := prepared.hold >>> extra.toUInt64, bits := prepared.bits - extra }
    refine ⟨.ok (), final, used, ?_, usedBound, finalInv, ?_, ?_, ?_, cursor, ?_⟩
    · unfold clZeroSetup
      rw [runX_bind, needRun]
      dsimp only
      rw [runX_bind, DROPBITS_run regs h here.bits.toUInt32 firstBound]
      dsimp only
      rw [runX_bind, BITS_run dropped h extra extraSmall]
      dsimp only
      rw [runX_bind, runX_modify]
      dsimp only
      exact DROPBITS_run prepared h extra (by omega)
    · have original : regs = { l with next := regs.next, have_ := regs.have_, hold := regs.hold, bits := regs.bits } := shape
      dsimp only [final, prepared, dropped]
      rw [original]
    · change (prepared.bits - extra).toNat ≤ _
      rw [finalCount]
      change (regs.bits - here.bits.toUInt32).toNat - extra.toNat ≤ _
      rw [firstCount, UInt8.toNat_toUInt32]
      omega
    · intro _
      exact ⟨rfl, by change 3 ≤ (base + bits).toNat; rw [copyNat]; omega,
        by change (base + bits).toNat ≤ 138; rw [copyNat]; omega⟩
    · change (prepared.bits - extra).toNat ≤ _
      rw [finalCount]
      change (regs.bits - here.bits.toUInt32).toNat - extra.toNat ≤ _
      rw [firstCount, UInt8.toNat_toUInt32]
      omega

/-- Projection retaining the original repeat setup interface. -/
theorem clZeroSetup_run {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    (here : Code) (extra base : UInt32) (width : here.bits.toNat ≤ 7)
    (extraBound : extra.toNat ≤ 7) (baseLo : 3 ≤ base.toNat) (baseHi : base.toNat ≤ 11) :
    ∃ result regs used,
      runX (clZeroSetup here extra base) l h = .ok ((result, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      regs = { l with next := regs.next, have_ := regs.have_, hold := regs.hold, bits := regs.bits, copy := regs.copy, len := regs.len } ∧
      regs.bits.toNat ≤ max l.bits.toNat 21 ∧
      (result = .ok () → regs.len = 0 ∧ 3 ≤ regs.copy.toNat ∧ regs.copy.toNat ≤ 138) := by
  obtain ⟨result, regs, used, run, bound, inv, shape, bits, counts, _, _⟩ :=
    clZeroSetup_run_cursor B here extra base width extraBound baseLo baseHi
  exact ⟨result, regs, used, run, bound, inv, shape, bits, counts⟩

def clPrevBits (c : Ctx) (haveCount : UInt32) : X Unit := do
  let value ← Ptr.index (lensP c.st) ((haveCount - 1).toNat : Int)
  let bits ← BITS 2
  modify fun l => { l with len := value.toUInt32, copy := 3 + bits }
  DROPBITS 2

/-- The previous-length repeat reads an initialized lens cell. The actual
two extra bits supply a repeat count between three and six. -/
theorem clPrevBits_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat}
    {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nonempty : 1 ≤ s.«have».toNat) (haveBound : s.«have».toNat ≤ 320)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (enough : 2 ≤ l.bits.toNat) :
    ∃ regs,
      runX (clPrevBits c s.«have») l h = .ok ((.ok (), regs), h) ∧
      BitInv h regs bs ∧ stream regs bs = (stream l bs).drop 2 ∧
      regs = { l with hold := regs.hold, bits := regs.bits, copy := regs.copy, len := regs.len } ∧
      regs.bits.toNat = l.bits.toNat - 2 ∧
      regs.len.toNat ≤ 15 ∧ 3 ≤ regs.copy.toNat ∧ regs.copy.toNat ≤ 6 := by
  have index : (s.«have» - 1).toNat = s.«have».toNat - 1 := by
    rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; exact nonempty)]
    rfl
  have inside : (s.«have» - 1).toNat < s.lens.size := by rw [index]; omega
  have lens := WRef.get_istate_lens hs
  have read := Ptr.index_ok (off := 0) (i := (s.«have» - 1).toNat) lens (by simpa using inside)
  let previous := s.lens.getD (s.«have».toNat - 1) 0
  have cell : s.lens[0 + (s.«have» - 1).toNat] = previous := by
    dsimp only [previous]
    rw [← index, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
    simp only [Nat.zero_add]
  have previousBound : previous.toNat ≤ 15 := initialized _ (by omega)
  let bits := l.hold.toUInt32 &&& ((1 : UInt32) <<< 2 - 1)
  have bitsNat : bits.toNat = l.hold.toNat % 4 := BITS_toNat l 2 (by decide)
  have copyNat : ((3 : UInt32) + bits).toNat = 3 + bits.toNat := by
    rw [UInt32.toNat_add]
    change (3 + bits.toNat) % 2 ^ 32 = 3 + bits.toNat
    rw [Nat.mod_eq_of_lt (by have := Nat.mod_lt l.hold.toNat (by decide : 0 < 4); omega)]
  let prepared := { l with len := previous.toUInt32, copy := 3 + bits }
  have preparedInv : BitInv h prepared bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  obtain ⟨finalInv, sameStream, count⟩ := DROPBITS_inv preparedInv 2 enough (by decide)
  let regs := { prepared with hold := prepared.hold >>> (2 : UInt32).toUInt64, bits := prepared.bits - 2 }
  refine ⟨regs, ?_, finalInv, sameStream, rfl, count, ?_, ?_, ?_⟩
  · unfold clPrevBits
    rw [hc]
    simp only [lensP, runX_bind, runX_lift_ok read, cell, BITS_run l h 2 (by decide), runX_modify]
    exact DROPBITS_run prepared h 2 (by decide)
  · change previous.toUInt32.toNat ≤ 15
    rw [UInt16.toNat_toUInt32]
    exact previousBound
  · change 3 ≤ ((3 : UInt32) + bits).toNat
    rw [copyNat]
    omega
  · change ((3 : UInt32) + bits).toNat ≤ 6
    rw [copyNat, bitsNat]
    have := Nat.mod_lt l.hold.toNat (by decide : 0 < 4)
    omega

def clNeedDrop (here : Code) (extra : UInt32) : X Unit := do
  NEEDBITS (here.bits.toUInt32 + extra)
  DROPBITS here.bits.toUInt32

theorem clNeedDrop_run_cursor {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    (here : Code) (extra : UInt32) (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7) :
    ∃ result regs used,
      runX (clNeedDrop here extra) l h = .ok ((result, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      TcRegShape l regs ∧ regs.bits.toNat ≤ max l.bits.toNat (extra.toNat + 14) ∧
      (result = .ok () → extra.toNat ≤ regs.bits.toNat) ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  have total : (here.bits.toUInt32 + extra).toNat = here.bits.toNat + extra.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨result, regs, used, run, usedBound, inv, _, bitCount, shape, bitBound, _, enough, _, _, cursor⟩ :=
    NEEDBITS_run_cursor B (here.bits.toUInt32 + extra) (by rw [total]; omega)
  rw [total] at bitBound
  cases result with
  | error fault =>
    refine ⟨.error fault, regs, used, ?_, usedBound, inv, shape, by omega, ?_, cursor, by omega⟩
    · unfold clNeedDrop
      rw [runX_bind, run]
    · intro impossible
      cases impossible
  | ok unit =>
    cases unit
    have available := enough rfl
    rw [total] at available
    have small : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
    obtain ⟨afterInv, _, count⟩ := DROPBITS_inv inv here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32]; omega) small
    refine ⟨.ok (), _, used, ?_, usedBound, afterInv, ?_, ?_, ?_, cursor, ?_⟩
    · unfold clNeedDrop
      rw [runX_bind, run]
      exact DROPBITS_run regs h here.bits.toUInt32 small
    · exact TcRegShape.drop shape _ _
    · rw [count, UInt8.toNat_toUInt32]
      omega
    · intro _
      rw [count, UInt8.toNat_toUInt32]
      omega
    · change (regs.bits - here.bits.toUInt32).toNat ≤ _
      rw [count, UInt8.toNat_toUInt32]
      omega

/-- Projection retaining the original read/drop interface. -/
theorem clNeedDrop_run {h : Heap} {l : IL} {bs : List UInt8} (B : BitInv h l bs)
    (here : Code) (extra : UInt32) (width : here.bits.toNat ≤ 7) (extraBound : extra.toNat ≤ 7) :
    ∃ result regs used,
      runX (clNeedDrop here extra) l h = .ok ((result, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      TcRegShape l regs ∧ regs.bits.toNat ≤ max l.bits.toNat (extra.toNat + 14) ∧
      (result = .ok () → extra.toNat ≤ regs.bits.toNat) := by
  obtain ⟨result, regs, used, run, bound, inv, shape, bits, enough, _, _⟩ :=
    clNeedDrop_run_cursor B here extra width extraBound
  exact ⟨result, regs, used, run, bound, inv, shape, bits, enough⟩

def clRepeat16 (c : Ctx) (here : Code) : X Bool := do
  clNeedDrop here 2
  let s ← ldInflateState c.st
  if s.«have» == 0 then
    badMode c "invalid bit length repeat"
    return true
  clPrevBits c s.«have»
  clRepeatFinish c

theorem clAfterLookup_repeat16 (c : Ctx) (here : Code) (symbol : here.val = 16) :
    clAfterLookup c here = clRepeat16 c here := by
  unfold clAfterLookup clRepeat16 clNeedDrop clPrevBits clRepeatFinish
  simp [symbol, xbind_assoc]

/-- With a nonempty initialized prefix, repeat 16 reads its preceding
length after the actual bit check. Every successful setup supplies the
range check with a proved copy count and length bound. -/
theorem clRepeat16_nonempty_run_cursor {c : Ctx} {l : IL} {h : Heap} {zs : Nat}
    {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nonempty : 1 ≤ s.«have».toNat) (haveBound : s.«have».toNat ≤ 320)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7) :
    ∃ (result : Except Ex Unit) (regs : IL) (used : Nat),
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      regs = { l with next := regs.next, have_ := regs.have_, hold := regs.hold, bits := regs.bits, copy := regs.copy, len := regs.len } ∧
      regs.bits.toNat ≤ max l.bits.toNat 16 ∧
      (result = .ok () →
        runX (clRepeat16 c here) l h = runX (clRepeatFinish c) regs h ∧
        regs.len.toNat ≤ 15 ∧ 3 ≤ regs.copy.toNat ∧ regs.copy.toNat ≤ 6) ∧
      (∀ fault, result = .error fault → runX (clRepeat16 c here) l h = .ok ((.error fault, regs), h)) ∧ regs.next = inputAdvance l.next used ∧
      regs.bits.toNat ≤ l.bits.toNat + 8 * used := by
  obtain ⟨result, regs, used, prefixRun, usedBound, inv, shape, bound, enough, cursor, budget⟩ :=
    clNeedDrop_run_cursor B here 2 width (by decide)
  change regs.bits.toNat ≤ max l.bits.toNat 16 at bound
  cases result with
  | error fault =>
    refine ⟨.error fault, regs, used, usedBound, inv, ?_, bound, ?_, ?_, cursor, budget⟩
    · rw [shape]
    · intro impossible
      cases impossible
    · intro other same
      cases same
      unfold clRepeat16
      rw [runX_bind, prefixRun]
  | ok unit =>
    cases unit
    obtain ⟨prepared, run, afterInv, _, frame, bits, lenBound, copyLo, copyHi⟩ :=
      clPrevBits_run hc hs size nonempty haveBound initialized inv (enough rfl)
    have zero : s.«have» ≠ 0 := by intro zero; rw [zero] at nonempty; simp at nonempty
    refine ⟨.ok (), prepared, used, usedBound, afterInv, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [frame, shape]
    · rw [bits]
      omega
    · intro _
      refine ⟨?_, lenBound, copyLo, copyHi⟩
      unfold clRepeat16
      rw [runX_bind, prefixRun]
      dsimp only
      rw [hc]
      have load : ldInflateState (some (.tab zs)) h = .ok (s, h) := by simp [ldI_eq, hs]
      simp only [runX_bind, runX_lift_ok load, zero, beq_iff_eq, ite_false, run]
    · intro fault impossible
      cases impossible
    · rw [frame]
      exact cursor
    · rw [bits]
      omega

/-- Projection retaining the original previous-length repeat interface. -/
theorem clRepeat16_nonempty_run {c : Ctx} {l : IL} {h : Heap} {zs : Nat}
    {s : InflateState} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (size : s.lens.size = 320) (nonempty : 1 ≤ s.«have».toNat) (haveBound : s.«have».toNat ≤ 320)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7) :
    ∃ (result : Except Ex Unit) (regs : IL) (used : Nat),
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      regs = { l with next := regs.next, have_ := regs.have_, hold := regs.hold, bits := regs.bits, copy := regs.copy, len := regs.len } ∧
      regs.bits.toNat ≤ max l.bits.toNat 16 ∧
      (result = .ok () →
        runX (clRepeat16 c here) l h = runX (clRepeatFinish c) regs h ∧
        regs.len.toNat ≤ 15 ∧ 3 ≤ regs.copy.toNat ∧ regs.copy.toNat ≤ 6) ∧
      (∀ fault, result = .error fault → runX (clRepeat16 c here) l h = .ok ((.error fault, regs), h)) := by
  obtain ⟨result, regs, used, bound, inv, shape, bits, success, failure, _, _⟩ :=
    clRepeat16_nonempty_run_cursor hc hs size nonempty haveBound initialized B here width
  exact ⟨result, regs, used, bound, inv, shape, bits, success, failure⟩

end Zlib.Inflate.Proofs
