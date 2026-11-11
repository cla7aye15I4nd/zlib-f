import ZlibF.Proof.«inflate.c.meaning-length»
import ZlibF.Proof.«inflate.c.code-length-zero-repeat»
import ZlibF.Proof.«inflate.c.code-length-previous-repeat»
import ZlibF.Proof.«inflate.c.code-length-repeat-meaning»
import ZlibF.Proof.«inflate.c.codelens-loop»

/-!
# inflate.c: one code-length item of `CODELENS`

The format side of a `CODELENS` iteration. An item is a code-length symbol
and its repeat bits (`CodeLenItem`). From a stored length prefix `P`, a
`CodeLens` parse of bits that start with an item takes that item first
(`codeLens_first`): this gives both directions of the partial parse at a
completed item, and rules out every parse at a repeat that runs past the
total or repeats nothing. An item is found in a prefix of the bits exactly
when the prefix is at least as long as the item (`item_take`,
`item_short`).

`cl_after` runs the part of the loop body after the root lookup on a
nonempty code-length code, with the selected symbol decoded from the bits:
it waits for the repeat bits, or goes to `BAD` with no parse of the bits
read, or completes the item with fewer than 8 held bits left.
-/

namespace Zlib.Inflate.Proofs.MeaningCodeLens
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec Zlib.Inffast.Proofs
open Zlib.Inflate.Proofs.MeaningBlock
set_option autoImplicit false

/-! ## Words and symbols -/

theorem rb_word {k x : Nat} {R : List Bool} (b : x < 2 ^ k) :
    readBits k (bitsOfNat x k ++ R) = some (x, R) := by
  simpa only [Nat.mod_eq_of_lt b, Nat.sub_self, bitsOfNat_zero, List.nil_append] using
    readBits_bitsOfNat k k x R (Nat.le_refl _)

theorem rb_split {k : Nat} {X : List Bool} {x : Nat} {r : List Bool}
    (read : readBits k X = some (x, r)) : X = bitsOfNat x k ++ r ∧ x < 2 ^ k := by
  obtain ⟨b, w⟩ := ZlibF.Math.CodeLengthPrefix.read_word read
  exact ⟨w, b⟩

theorem codeOf_length (cl : List Nat) (s : Nat) : (codeOf cl s).length = cl.getD s 0 := by
  simp only [codeOf, ZlibF.Spec.Proofs.natToBitsMSB_length]

theorem dec_split {cl : List Nat} {X r : List Bool} {s : Nat}
    (d : decodeSym cl X = some (s, r)) : X = codeOf cl s ++ r ∧ cl.getD s 0 ≠ 0 ∧ s < cl.length :=
  ⟨ZlibF.Math.CodeLengthPrefix.decoded_word d, (Zlib.Inftrees.Proofs.decoded_symbol_prefix d).2.1,
    (Zlib.Inftrees.Proofs.decoded_symbol_prefix d).1⟩

theorem dec_ext {cl : List Nat} (acc : Acceptable .codeLength cl) {X Y r : List Bool} {s : Nat}
    (d : decodeSym cl X = some (s, r)) : decodeSym cl (X ++ Y) = some (s, r ++ Y) := by
  obtain ⟨w, nz, _⟩ := dec_split d
  rw [w, List.append_assoc]
  exact ZlibF.Math.InflateDecode.decode_canonical_word acc s nz _

theorem dec_word {cl : List Nat} (acc : Acceptable .codeLength cl) {s : Nat} (nz : cl.getD s 0 ≠ 0)
    (W : List Bool) : decodeSym cl (codeOf cl s ++ W) = some (s, W) :=
  ZlibF.Math.InflateDecode.decode_canonical_word acc s nz W

theorem none_take {cl : List Nat} (acc : Acceptable .codeLength cl) {X : List Bool}
    (nd : decodeSym cl X = none) (m : Nat) : decodeSym cl (X.take m) = none := by
  cases d : decodeSym cl (X.take m) with
  | none => rfl
  | some pair =>
    obtain ⟨s, r⟩ := pair
    have e := dec_ext acc (Y := X.drop m) d
    rw [List.take_append_drop, nd] at e
    cases e

/-- The bits of one item. -/
def itemBits (cl : List Nat) (sym x : Nat) : List Bool :=
  codeOf cl sym ++ bitsOfNat x (codeLenExtra sym)

theorem itemBits_length (cl : List Nat) (sym x : Nat) :
    (itemBits cl sym x).length = cl.getD sym 0 + codeLenExtra sym := by
  simp only [itemBits, List.length_append, codeOf_length, bitsOfNat_length]

/-- A prefix as long as the item holds the item. -/
theorem item_take {cl : List Nat} (acc : Acceptable .codeLength cl) {sym x : Nat} {R : List Bool}
    (nz : cl.getD sym 0 ≠ 0) (b : x < 2 ^ codeLenExtra sym) {m : Nat}
    (le : (itemBits cl sym x).length ≤ m) :
    CodeLenItem cl ((itemBits cl sym x ++ R).take m) := by
  rw [List.take_append, List.take_of_length_le le, itemBits, List.append_assoc]
  exact ⟨sym, _, x, _, dec_word acc nz _, rb_word b⟩

/-- A prefix shorter than the first item holds no item. -/
theorem item_short {cl : List Nat} (acc : Acceptable .codeLength cl) {S r : List Bool} {sym : Nat}
    (dS : decodeSym cl S = some (sym, r)) {m : Nat}
    (lt : m < cl.getD sym 0 + codeLenExtra sym) : ¬ CodeLenItem cl (S.take m) := by
  rintro ⟨s', r1, x', r2, d', rd'⟩
  have e := dec_ext acc (Y := S.drop m) d'
  rw [List.take_append_drop, dS] at e
  simp only [Option.some.injEq, Prod.mk.injEq] at e
  obtain ⟨rfl, _⟩ := e
  obtain ⟨w, _, _⟩ := dec_split d'
  obtain ⟨w2, _⟩ := rb_split rd'
  have len := congrArg List.length w
  rw [List.length_append, codeOf_length, w2, List.length_append, bitsOfNat_length, List.length_take] at len
  omega

/-! ## The first item of a parse -/

/-- A `CodeLens` parse from a prefix shorter than the total starts with the
item decoded from its bits. -/
theorem codeLens_first {cl : List Nat} {T : Nat} {P : List Nat} {X rest r1 : List Bool}
    {lens : List Nat} {sym : Nat}
    (parse : CodeLens cl T P X rest lens) (lt : P.length < T) (d : decodeSym cl X = some (sym, r1)) :
    (sym < 16 ∧ CodeLens cl T (P ++ [sym]) r1 rest lens) ∨
    (sym = 16 ∧ P ≠ [] ∧ ∃ x r2, readBits 2 r1 = some (x, r2) ∧ P.length + (3 + x) ≤ T ∧
      CodeLens cl T (P ++ List.replicate (3 + x) (P.getLastD 0)) r2 rest lens) ∨
    (sym = 17 ∧ ∃ x r2, readBits 3 r1 = some (x, r2) ∧ P.length + (3 + x) ≤ T ∧
      CodeLens cl T (P ++ List.replicate (3 + x) 0) r2 rest lens) ∨
    (sym = 18 ∧ ∃ x r2, readBits 7 r1 = some (x, r2) ∧ P.length + (11 + x) ≤ T ∧
      CodeLens cl T (P ++ List.replicate (11 + x) 0) r2 rest lens) := by
  cases parse with
  | done e => omega
  | len _ d' small next =>
    rw [d] at d'
    simp only [Option.some.injEq, Prod.mk.injEq] at d'
    obtain ⟨rfl, rfl⟩ := d'
    exact Or.inl ⟨small, next⟩
  | rep16 _ d' ne rb room next =>
    rw [d] at d'
    simp only [Option.some.injEq, Prod.mk.injEq] at d'
    obtain ⟨rfl, rfl⟩ := d'
    exact Or.inr (Or.inl ⟨rfl, ne, _, _, rb, room, next⟩)
  | rep17 _ d' rb room next =>
    rw [d] at d'
    simp only [Option.some.injEq, Prod.mk.injEq] at d'
    obtain ⟨rfl, rfl⟩ := d'
    exact Or.inr (Or.inr (Or.inl ⟨rfl, _, _, rb, room, next⟩))
  | rep18 _ d' rb room next =>
    rw [d] at d'
    simp only [Option.some.injEq, Prod.mk.injEq] at d'
    obtain ⟨rfl, rfl⟩ := d'
    exact Or.inr (Or.inr (Or.inr ⟨rfl, _, _, rb, room, next⟩))

/-- No parse from fewer than the total lengths reads bits with no symbol. -/
theorem codeLens_none {cl : List Nat} {T : Nat} {P : List Nat} {X rest : List Bool} {lens : List Nat}
    (parse : CodeLens cl T P X rest lens) (lt : P.length < T) (nd : decodeSym cl X = none) : False := by
  cases parse with
  | done e => omega
  | len _ d => rw [nd] at d; cases d
  | rep16 _ d => rw [nd] at d; cases d
  | rep17 _ d => rw [nd] at d; cases d
  | rep18 _ d => rw [nd] at d; cases d

/-! ## After the lookup -/

/-- The result of the loop body after the lookup, on a nonempty code: wait
with the bits kept, `BAD` with no parse of the bits read, or a completed
item with both directions of the partial parse and fewer than 8 held bits. -/
def AfterResult (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (cl : List Nat) (l : IL) (bs : List UInt8) (result : Except Ex Bool) (regs : IL) (after : Heap)
    (used : Nat) : Prop :=
  (result = .error Ex.leave ∧ after = h ∧ regs.have_ = 0 ∧ stream regs (bs.drop used) = stream l bs ∧
      (regs.bits.toNat < 8 ∨ ¬ CodeLenItem cl ((stream l bs).take (regs.bits.toNat - 8)))) ∨
  (result = .ok true ∧ (∃ i, after = tcBadHeap h r zs z s i) ∧
      ∀ F rest lens, ¬ CodeLens cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s)
        ((stream l bs).take (l.bits.toNat + 8 * used) ++ F) rest lens) ∨
  (result = .ok false ∧ ∃ state cbits, after = setI h zs state ∧ ClWriteResult s state ∧
      stream l bs = cbits ++ stream regs (bs.drop used) ∧ regs.bits.toNat < 8 ∧
      ZlibF.Math.CodeLengthPrefix.Trace cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) cbits
        (actualLengthPrefix state) ∧
      ∀ F rest lens, CodeLens cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (cbits ++ F) rest lens →
        CodeLens cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix state) F rest lens)

theorem take_item {cl : List Nat} {sym x : Nat} {S R F : List Bool} {m : Nat}
    (itemEq : S = itemBits cl sym x ++ R) (le : (itemBits cl sym x).length ≤ m) :
    S.take m ++ F = codeOf cl sym ++ (bitsOfNat x (codeLenExtra sym) ++ (R.take (m - (itemBits cl sym x).length) ++ F)) := by
  rw [itemEq, List.take_append, List.take_of_length_le le, itemBits]
  simp only [List.append_assoc]

set_option maxHeartbeats 4000000 in
/-- A zero repeat (symbol 17 or 18) after the lookup. -/
theorem cl_zero {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {bs : List UInt8} {cl : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (size : s.lens.size = 320)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7)
    (acc : Acceptable .codeLength cl)
    (dec : decodeSym cl (stream l bs) = some (here.val.toNat, (stream l bs).drop here.bits.toNat))
    (hbEq : cl.getD here.val.toNat 0 = here.bits.toNat)
    (pre : l.bits.toNat < 8 ∨ ¬ CodeLenItem cl ((stream l bs).take (l.bits.toNat - 8)))
    (extra base : UInt32) (extraBound : extra.toNat ≤ 7) (baseLo : 3 ≤ base.toNat) (baseHi : base.toNat ≤ 11)
    (shapeRun : clAfterLookup c here = (do clZeroSetup here extra base; clRepeatFinish c))
    (kEq : codeLenExtra here.val.toNat = extra.toNat)
    (first : ∀ F rest lens, CodeLens cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s)
        (codeOf cl here.val.toNat ++ F) rest lens →
      ∃ x r2, readBits extra.toNat F = some (x, r2) ∧
        (actualLengthPrefix s).length + (base.toNat + x) ≤ s.nlen.toNat + s.ndist.toNat ∧
        CodeLens cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s ++ List.replicate (base.toNat + x) 0)
          r2 rest lens)
    (trace : ∀ x, x < 2 ^ extra.toNat →
      (actualLengthPrefix s).length + (base.toNat + x) ≤ s.nlen.toNat + s.ndist.toNat →
      ZlibF.Math.CodeLengthPrefix.Trace cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s)
        (codeOf cl here.val.toNat ++ bitsOfNat x extra.toNat)
        (actualLengthPrefix s ++ List.replicate (base.toNat + x) 0)) :
    ∃ result regs after used, runX (clAfterLookup c here) l h = .ok ((result, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧ RegsKeep l regs ∧
      regs.next = inputAdvance l.next used ∧ AfterResult h r zs z s cl l bs result regs after used := by
  obtain ⟨wS, nz, _⟩ := dec_split dec
  have lenP : (actualLengthPrefix s).length = s.«have».toNat := Zlib.Inftrees.Proofs.lensOf_length _ _
  have total : (here.bits.toUInt32 + extra).toNat = here.bits.toNat + extra.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨result, l1, j, needRun, jle, inv1, str1, cnt1, shape1, bnd1, _, ok1, lv1, kinds, nxt1⟩ :=
    NEEDBITS_run_cursor B (here.bits.toUInt32 + extra) (by rw [total]; omega)
  rw [total] at bnd1 ok1 lv1
  have keep1 : RegsKeep l l1 := RegsKeep.of_shape shape1
  rcases kinds with rfl | rfl
  · -- the repeat bits are held
    have avail := ok1 rfl
    have firstBound : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
    have extraSmall : extra.toNat < 32 := by omega
    let dropped : IL :=
      { l1 with hold := l1.hold >>> here.bits.toUInt32.toUInt64, bits := l1.bits - here.bits.toUInt32 }
    obtain ⟨inv2, str2, cnt2⟩ := DROPBITS_inv inv1 here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32]; omega) firstBound
    rw [UInt8.toNat_toUInt32] at cnt2 str2
    let bits := dropped.hold.toUInt32 &&& ((1 : UInt32) <<< extra - 1)
    have bitsNat : bits.toNat = dropped.hold.toNat % 2 ^ extra.toNat := BITS_toNat dropped extra extraSmall
    have bitsBound : bits.toNat < 2 ^ extra.toNat := by
      rw [bitsNat]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have pow7 : 2 ^ extra.toNat ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) extraBound
    have copyNat : (base + bits).toNat = base.toNat + bits.toNat := by
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by have : (2 : Nat) ^ 7 = 128 := rfl; omega)]
    let prepared : IL := { dropped with len := 0, copy := base + bits }
    have preparedInv : BitInv h prepared (bs.drop j) := ⟨inv2.have_eq, inv2.next, inv2.hold_lt⟩
    have secondEnough : extra.toNat ≤ prepared.bits.toNat := by
      change extra.toNat ≤ (l1.bits - here.bits.toUInt32).toNat
      rw [cnt2]; omega
    obtain ⟨inv3, str3, cnt3⟩ := DROPBITS_inv preparedInv extra secondEnough (by omega)
    let final : IL :=
      { prepared with hold := prepared.hold >>> extra.toUInt64, bits := prepared.bits - extra }
    have setupRun : runX (clZeroSetup here extra base) l h = .ok ((.ok (), final), h) := by
      unfold clZeroSetup
      rw [runX_bind, needRun]
      dsimp only
      rw [runX_bind, DROPBITS_run l1 h here.bits.toUInt32 firstBound]
      dsimp only
      rw [runX_bind, BITS_run dropped h extra extraSmall]
      dsimp only
      rw [runX_bind, runX_modify]
      dsimp only
      exact DROPBITS_run prepared h extra (by omega)
    have run0 : runX (clAfterLookup c here) l h = runX (clRepeatFinish c) final h := by
      rw [shapeRun, runX_bind, setupRun]
    have finalBits : final.bits.toNat = l1.bits.toNat - here.bits.toNat - extra.toNat := by
      change (prepared.bits - extra).toNat = _
      rw [cnt3]
      change (l1.bits - here.bits.toUInt32).toNat - extra.toNat = _
      rw [cnt2]
    have dropStream : stream dropped (bs.drop j) = (stream l bs).drop here.bits.toNat := by
      rw [← str1]; exact str2
    have finalStream : stream final (bs.drop j) = ((stream l bs).drop here.bits.toNat).drop extra.toNat := by
      rw [← dropStream]; exact str3
    have read : readBits extra.toNat ((stream l bs).drop here.bits.toNat) =
        some (bits.toNat, stream final (bs.drop j)) := by
      have rd := readBits_held_stream dropped (bs.drop j) extra.toNat
        (by change extra.toNat ≤ (l1.bits - here.bits.toUInt32).toNat; rw [cnt2]; omega)
      rw [dropStream] at rd
      rw [rd, finalStream, bitsNat]
    obtain ⟨wR, _⟩ := rb_split read
    have bitsBound' : bits.toNat < 2 ^ codeLenExtra here.val.toNat := by rw [kEq]; exact bitsBound
    have itemEq : stream l bs = itemBits cl here.val.toNat bits.toNat ++ stream final (bs.drop j) := by
      rw [itemBits, kEq, List.append_assoc, ← wR]
      exact wS
    have itemLen : (itemBits cl here.val.toNat bits.toNat).length = here.bits.toNat + extra.toNat := by
      rw [itemBits_length, hbEq, kEq]
    have longItem : 8 ≤ l.bits.toNat → l.bits.toNat - 8 < here.bits.toNat + extra.toNat := by
      intro ge
      rcases pre with lt | ni
      · omega
      · apply Decidable.byContradiction
        intro hge
        apply ni
        rw [itemEq]
        exact item_take acc nz bitsBound' (by rw [itemLen]; omega)
    have shortFinal : final.bits.toNat < 8 := by
      rw [finalBits]
      by_cases small : l1.bits.toNat ≤ here.bits.toNat + extra.toNat + 7
      · omega
      · have j0 : j = 0 := by omega
        have := longItem (by omega)
        omega
    have keepF : RegsKeep l final := keep1
    have copyLo : 1 ≤ final.copy.toNat := by change 1 ≤ (base + bits).toNat; rw [copyNat]; omega
    have copyHi : final.copy.toNat ≤ 138 := by
      change (base + bits).toNat ≤ 138; rw [copyNat]
      have : (2 : Nat) ^ 7 = 128 := rfl
      omega
    have copyEq : final.copy.toNat = base.toNat + bits.toNat := copyNat
    obtain ⟨overrun, room⟩ := clRepeatFinish_run hr hc hz hs size nlen ndist (by omega) copyLo copyHi
      (by change (0 : UInt32).toNat ≤ 15; decide) initialized
    by_cases ov : s.«have».toNat + final.copy.toNat > s.nlen.toNat + s.ndist.toNat
    · obtain ⟨i, _, badRun⟩ := overrun ov
      refine ⟨.ok true, final, tcBadHeap h r zs z s i, j, run0.trans badRun, jle,
        (inv3.put_stream r _).setI zs _, keepF, nxt1, Or.inr (Or.inl ⟨rfl, ⟨i, rfl⟩, ?_⟩)⟩
      intro F rest lens p
      rw [← cnt1, take_item itemEq (by rw [itemLen]; omega)] at p
      obtain ⟨x, r2, rd, roomX, _⟩ := first _ _ _ p
      rw [kEq, rb_word bitsBound] at rd
      simp only [Option.some.injEq, Prod.mk.injEq] at rd
      obtain ⟨rfl, _⟩ := rd
      omega
    · obtain ⟨state, finRun, frame, sz, count, progress, vals⟩ := room (by omega)
      have actual := run0.trans finRun
      obtain ⟨used', state', value', _, heapEq, _, _, _, _, _, read', prefixEq⟩ :=
        clZeroRepeat_contents_of_run hr hc hz hs size nlen ndist (by omega) B here extra base width
          extraBound baseLo baseHi (by rw [← shapeRun]; exact actual)
      have sameState : state' = state := by
        have := congrArg (fun hh : Heap => hh.istates zs) heapEq
        simp only [setI_istates_same, Option.some.injEq] at this
        exact this.symm
      subst sameState
      rw [read] at read'
      simp only [Option.some.injEq, Prod.mk.injEq] at read'
      obtain ⟨rfl, _⟩ := read'
      refine ⟨.ok false, { final with copy := 0xffffffff }, setI h zs state', j, actual, jle,
        (show BitInv h { final with copy := 0xffffffff } (bs.drop j) from
          ⟨inv3.have_eq, inv3.next, inv3.hold_lt⟩).setI zs state', keepF, nxt1,
        Or.inr (Or.inr ⟨rfl, state', itemBits cl here.val.toNat bits.toNat, rfl,
          ⟨frame, sz, by omega, progress, vals⟩, itemEq, shortFinal, ?_, ?_⟩)⟩
      · rw [prefixEq, itemBits, kEq]
        exact trace _ bitsBound (by omega)
      · intro F rest lens p
        rw [itemBits, List.append_assoc, kEq] at p
        obtain ⟨x, r2, rd, _, next⟩ := first _ _ _ p
        rw [rb_word bitsBound] at rd
        simp only [Option.some.injEq, Prod.mk.injEq] at rd
        obtain ⟨rfl, rfl⟩ := rd
        rw [prefixEq]
        exact next
  · -- waiting for the repeat bits
    obtain ⟨_, have0, bitsLt⟩ := lv1 rfl
    have setupRun : runX (clZeroSetup here extra base) l h = .ok ((.error Ex.leave, l1), h) := by
      unfold clZeroSetup
      rw [runX_bind, needRun]
    have run0 : runX (clAfterLookup c here) l h = .ok ((.error Ex.leave, l1), h) := by
      rw [shapeRun, runX_bind, setupRun]
    exact ⟨.error Ex.leave, l1, h, j, run0, jle, inv1, keep1, nxt1,
      Or.inl ⟨rfl, rfl, have0, str1, Or.inr (item_short acc dec (by rw [hbEq, kEq]; omega))⟩⟩

#print axioms cl_zero

set_option maxHeartbeats 4000000 in
/-- A repeat of the previous length (symbol 16) after the lookup. -/
theorem cl_prev {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {bs : List UInt8} {cl : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (size : s.lens.size = 320)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7) (sym16 : here.val = 16)
    (acc : Acceptable .codeLength cl)
    (dec : decodeSym cl (stream l bs) = some (here.val.toNat, (stream l bs).drop here.bits.toNat))
    (hbEq : cl.getD here.val.toNat 0 = here.bits.toNat)
    (pre : l.bits.toNat < 8 ∨ ¬ CodeLenItem cl ((stream l bs).take (l.bits.toNat - 8))) :
    ∃ result regs after used, runX (clAfterLookup c here) l h = .ok ((result, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧ RegsKeep l regs ∧
      regs.next = inputAdvance l.next used ∧ AfterResult h r zs z s cl l bs result regs after used := by
  obtain ⟨wS, nz, _⟩ := dec_split dec
  have symNat : here.val.toNat = 16 := by rw [sym16]; rfl
  have kEq : codeLenExtra here.val.toNat = 2 := by rw [symNat]; rfl
  have lenP : (actualLengthPrefix s).length = s.«have».toNat := Zlib.Inftrees.Proofs.lensOf_length _ _
  have ltP : (actualLengthPrefix s).length < s.nlen.toNat + s.ndist.toNat := by omega
  rw [clAfterLookup_repeat16 c here sym16]
  have total : (here.bits.toUInt32 + 2).toNat = here.bits.toNat + 2 := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32]
    change (here.bits.toNat + 2) % 2 ^ 32 = _
    omega
  obtain ⟨result, l1, j, needRun, jle, inv1, str1, cnt1, shape1, bnd1, _, ok1, lv1, kinds, nxt1⟩ :=
    NEEDBITS_run_cursor B (here.bits.toUInt32 + 2) (by rw [total]; omega)
  rw [total] at bnd1 ok1 lv1
  have keep1 : RegsKeep l l1 := RegsKeep.of_shape shape1
  -- the first item is symbol 16, whatever the repeat bits
  have first : ∀ m F rest lens, here.bits.toNat ≤ m → m ≤ (stream l bs).length →
      CodeLens cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) ((stream l bs).take m ++ F) rest lens →
      actualLengthPrefix s ≠ [] ∧ ∃ x r2, readBits 2 (((stream l bs).drop here.bits.toNat).take (m - here.bits.toNat) ++ F) = some (x, r2) ∧
        (actualLengthPrefix s).length + (3 + x) ≤ s.nlen.toNat + s.ndist.toNat ∧
        CodeLens cl (s.nlen.toNat + s.ndist.toNat)
          (actualLengthPrefix s ++ List.replicate (3 + x) ((actualLengthPrefix s).getLastD 0)) r2 rest lens := by
    intro m F rest lens le _ p
    have split : (stream l bs).take m ++ F =
        codeOf cl here.val.toNat ++ (((stream l bs).drop here.bits.toNat).take (m - here.bits.toNat) ++ F) := by
      have e : (stream l bs).take m = (codeOf cl here.val.toNat ++ (stream l bs).drop here.bits.toNat).take m :=
        congrArg (List.take m) wS
      rw [e, List.take_append, List.take_of_length_le (by rw [codeOf_length, hbEq]; exact le), codeOf_length, hbEq,
        List.append_assoc]
    rw [split] at p
    rcases codeLens_first p ltP (dec_word acc nz _) with ⟨lt, _⟩ | ⟨_, ne, x, r2, rd, roomX, next⟩ |
      ⟨e, _⟩ | ⟨e, _⟩
    · omega
    · exact ⟨ne, x, r2, rd, roomX, next⟩
    · omega
    · omega
  rcases kinds with rfl | rfl
  · -- the repeat bits are held
    have avail := ok1 rfl
    have firstBound : here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
    let dropped : IL :=
      { l1 with hold := l1.hold >>> here.bits.toUInt32.toUInt64, bits := l1.bits - here.bits.toUInt32 }
    obtain ⟨inv2, str2, cnt2⟩ := DROPBITS_inv inv1 here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32]; omega) firstBound
    rw [UInt8.toNat_toUInt32] at cnt2 str2
    have dropRun : runX (clNeedDrop here 2) l h = .ok ((.ok (), dropped), h) := by
      unfold clNeedDrop
      rw [runX_bind, needRun]
      exact DROPBITS_run l1 h here.bits.toUInt32 firstBound
    have dropStream : stream dropped (bs.drop j) = (stream l bs).drop here.bits.toNat := by
      rw [← str1]; exact str2
    have sLen := tcStream_length B
    have l1Len : l1.bits.toNat ≤ (stream l bs).length := by
      have := tcStream_length inv1
      rw [str1] at this
      omega
    by_cases empty : s.«have» = 0
    · -- nothing to repeat
      obtain ⟨i, _, bad⟩ := tcBadMode_run (c := c) "invalid bit length repeat" lit_bit_length_repeat hr hc hz hs
      have badRun : runX (clRepeat16 c here) l h = .ok ((.ok true, dropped), tcBadHeap h r zs z s i) := by
        unfold clRepeat16
        rw [runX_bind, dropRun]
        dsimp only
        rw [hc]
        simp [runX_bind, runX_lift, ldI_eq, hs, empty, bad, runX_pure]
      refine ⟨.ok true, dropped, tcBadHeap h r zs z s i, j, badRun, jle,
        (inv2.put_stream r _).setI zs _, keep1, nxt1, Or.inr (Or.inl ⟨rfl, ⟨i, rfl⟩, ?_⟩)⟩
      intro F rest lens p
      rw [← cnt1] at p
      obtain ⟨ne, _⟩ := first _ _ _ _ (by omega) l1Len p
      apply ne
      apply List.eq_nil_of_length_eq_zero
      rw [lenP, empty]
      rfl
    · have nonempty : 1 ≤ s.«have».toNat := by
        have : s.«have».toNat ≠ 0 := fun e => empty (UInt32.toNat_inj.mp e)
        omega
      have enough2 : 2 ≤ dropped.bits.toNat := by
        change 2 ≤ (l1.bits - here.bits.toUInt32).toNat; rw [cnt2]; omega
      obtain ⟨regs2, run2, inv3, str3, shape3, bits3, len3, copyLo, copyHi⟩ :=
        clPrevBits_run hc hs size nonempty (by omega) initialized inv2 enough2
      obtain ⟨regs2', value, run2', _, _, read2, copy2⟩ :=
        clPrevBits_read hc hs size nonempty (by omega) inv2 enough2
      have same := Except.ok.inj (run2.symm.trans run2')
      have e2 : regs2 = regs2' := congrArg (fun p => p.1.2) same
      subst e2
      rw [dropStream] at read2
      obtain ⟨wR, valueBound⟩ := rb_split read2
      have zero : s.«have» ≠ 0 := empty
      have run16 : runX (clRepeat16 c here) l h = runX (clRepeatFinish c) regs2 h := by
        unfold clRepeat16
        rw [runX_bind, dropRun]
        dsimp only
        rw [hc]
        have load : ldInflateState (some (.tab zs)) h = .ok (s, h) := by simp [ldI_eq, hs]
        simp only [runX_bind, runX_lift_ok load, zero, beq_iff_eq, ite_false]
        rw [run2]
      have keep2 : RegsKeep l regs2 := by
        rw [shape3]; exact keep1
      have nxt2 : regs2.next = inputAdvance l.next j := by rw [shape3]; exact nxt1
      have bits2 : regs2.bits.toNat = l1.bits.toNat - here.bits.toNat - 2 := by
        rw [bits3]
        change (l1.bits - here.bits.toUInt32).toNat - 2 = _
        rw [cnt2]
      have valueBound' : value < 2 ^ codeLenExtra here.val.toNat := by rw [kEq]; exact valueBound
      have itemEq : stream l bs = itemBits cl here.val.toNat value ++ stream regs2 (bs.drop j) := by
        rw [itemBits, kEq, List.append_assoc, ← wR]
        exact wS
      have itemLen : (itemBits cl here.val.toNat value).length = here.bits.toNat + 2 := by
        rw [itemBits_length, hbEq, kEq]
      have shortFinal : regs2.bits.toNat < 8 := by
        rw [bits2]
        by_cases small : l1.bits.toNat ≤ here.bits.toNat + 2 + 7
        · omega
        · have j0 : j = 0 := by omega
          rcases pre with lt | ni
          · omega
          · exfalso
            apply ni
            rw [itemEq]
            exact item_take acc nz valueBound' (by rw [itemLen]; omega)
      obtain ⟨overrun, room⟩ := clRepeatFinish_run hr hc hz hs size nlen ndist (by omega)
        (by omega) (by omega) len3 initialized
      by_cases ov : s.«have».toNat + regs2.copy.toNat > s.nlen.toNat + s.ndist.toNat
      · obtain ⟨i, _, badRun⟩ := overrun ov
        refine ⟨.ok true, regs2, tcBadHeap h r zs z s i, j, run16.trans badRun, jle,
          (inv3.put_stream r _).setI zs _, keep2, nxt2, Or.inr (Or.inl ⟨rfl, ⟨i, rfl⟩, ?_⟩)⟩
        intro F rest lens p
        rw [← cnt1] at p
        obtain ⟨_, x, r2, rd, roomX, _⟩ := first _ _ _ _ (by omega) l1Len p
        rw [wR, List.take_append, List.take_of_length_le (by rw [bitsOfNat_length]; omega),
          List.append_assoc, rb_word valueBound] at rd
        simp only [Option.some.injEq, Prod.mk.injEq] at rd
        obtain ⟨rfl, _⟩ := rd
        omega
      · obtain ⟨state, finRun, frame, sz, count, progress, vals⟩ := room (by omega)
        have actual := run16.trans finRun
        obtain ⟨used', state', value', _, heapEq, _, _, _, _, _, _, read', prefixEq⟩ :=
          clPreviousRepeat_contents_of_run hr hc hz hs size nlen ndist (by omega) B here width actual
        have sameState : state' = state := by
          have := congrArg (fun hh : Heap => hh.istates zs) heapEq
          simp only [setI_istates_same, Option.some.injEq] at this
          exact this.symm
        subst sameState
        rw [read2] at read'
        simp only [Option.some.injEq, Prod.mk.injEq] at read'
        obtain ⟨rfl, _⟩ := read'
        refine ⟨.ok false, { regs2 with copy := 0xffffffff }, setI h zs state', j, actual, jle,
          (show BitInv h { regs2 with copy := 0xffffffff } (bs.drop j) from
            ⟨inv3.have_eq, inv3.next, inv3.hold_lt⟩).setI zs state', keep2, nxt2,
          Or.inr (Or.inr ⟨rfl, state', itemBits cl here.val.toNat value, rfl,
            ⟨frame, sz, by omega, progress, vals⟩, itemEq, shortFinal, ?_, ?_⟩)⟩
        · rw [prefixEq, itemBits, kEq, symNat]
          have ne : actualLengthPrefix s ≠ [] := by
            intro e
            have := congrArg List.length e
            simp only [List.length_nil] at this
            omega
          exact ZlibF.Math.CodeLengthPrefix.Trace.previous acc ltP (by rw [← symNat]; exact nz) ne
            valueBound (by omega)
        · intro F rest lens p
          rw [itemBits, kEq, List.append_assoc] at p
          rcases codeLens_first p ltP (dec_word acc nz _) with ⟨lt, _⟩ | ⟨_, _, x, r2, rd, _, next⟩ |
            ⟨e, _⟩ | ⟨e, _⟩
          · omega
          · rw [rb_word valueBound] at rd
            simp only [Option.some.injEq, Prod.mk.injEq] at rd
            obtain ⟨rfl, rfl⟩ := rd
            rw [prefixEq]
            exact next
          · omega
          · omega
  · -- waiting for the repeat bits
    obtain ⟨_, have0, bitsLt⟩ := lv1 rfl
    have dropRun : runX (clNeedDrop here 2) l h = .ok ((.error Ex.leave, l1), h) := by
      unfold clNeedDrop
      rw [runX_bind, needRun]
    have run0 : runX (clRepeat16 c here) l h = .ok ((.error Ex.leave, l1), h) := by
      unfold clRepeat16
      rw [runX_bind, dropRun]
    exact ⟨.error Ex.leave, l1, h, j, run0, jle, inv1, keep1, nxt1,
      Or.inl ⟨rfl, rfl, have0, str1, Or.inr (item_short acc dec (by rw [hbEq, kEq]; omega))⟩⟩

#print axioms cl_prev

/-- A literal length (symbol below 16) after the lookup. -/
theorem cl_lit {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {bs : List UInt8} {cl : List Nat}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s) (size : s.lens.size = 320)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) (haveBound : s.«have».toNat < 320)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7)
    (enough : here.bits.toNat ≤ l.bits.toNat) (literal : here.val.toNat < 16)
    (acc : Acceptable .codeLength cl)
    (dec : decodeSym cl (stream l bs) = some (here.val.toNat, (stream l bs).drop here.bits.toNat))
    (pre : l.bits.toNat < 8 ∨ ¬ CodeLenItem cl ((stream l bs).take (l.bits.toNat - 8))) :
    ∃ result regs after used, runX (clAfterLookup c here) l h = .ok ((result, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧ RegsKeep l regs ∧
      regs.next = inputAdvance l.next used ∧ AfterResult h r zs z s cl l bs result regs after used := by
  obtain ⟨wS, nz, _⟩ := dec_split dec
  have lenP : (actualLengthPrefix s).length = s.«have».toNat := Zlib.Inftrees.Proofs.lensOf_length _ _
  have ltP : (actualLengthPrefix s).length < s.nlen.toNat + s.ndist.toNat := by omega
  obtain ⟨run, inv, remaining, count, values⟩ :=
    clAfterLookup_literal_run hc hs size haveBound literal width enough B initialized
  have kLit : codeLenExtra here.val.toNat = 0 := by
    simp only [codeLenExtra]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have prefixEq := clWrite_lens_prefix (s := s) (value := here.val) haveBound (by omega)
  change actualLengthPrefix (clWrite s here.val) = actualLengthPrefix s ++ [here.val.toNat] at prefixEq
  refine ⟨.ok false, _, setI h zs (clWrite s here.val), 0, run, by omega,
    by simpa only [List.drop_zero] using inv, ⟨rfl, rfl, rfl, rfl, rfl⟩, (inputAdvance_zero _).symm,
    Or.inr (Or.inr ⟨rfl, clWrite s here.val, codeOf cl here.val.toNat, rfl,
      ⟨rfl, by simp [clWrite, size], by rw [count]; omega, by rw [count]; omega, values⟩, ?_, ?_, ?_, ?_⟩)⟩
  · rw [List.drop_zero, remaining]
    exact wS
  · change (l.bits - here.bits.toUInt32).toNat < 8
    rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; rw [UInt8.toNat_toUInt32]; exact enough),
      UInt8.toNat_toUInt32]
    rcases pre with lt | ni
    · omega
    · apply Decidable.byContradiction
      intro ge
      apply ni
      have itemEq : stream l bs = itemBits cl here.val.toNat 0 ++ (stream l bs).drop here.bits.toNat := by
        rw [itemBits, kLit, bitsOfNat_zero, List.append_nil]
        exact wS
      rw [itemEq]
      have hbEq : (codeOf cl here.val.toNat).length = here.bits.toNat := by
        have := congrArg List.length wS
        rw [List.length_append, List.length_drop] at this
        have := tcStream_length B
        omega
      exact item_take acc nz (by rw [kLit]; decide)
        (by rw [itemBits, kLit, bitsOfNat_zero, List.append_nil, hbEq]; omega)
  · rw [prefixEq]
    exact ZlibF.Math.CodeLengthPrefix.Trace.literal acc ltP nz literal
  · intro F rest lens p
    rcases codeLens_first p ltP (dec_word acc nz F) with ⟨_, next⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩
    · rw [prefixEq]; exact next
    · omega
    · omega
    · omega

/-- The loop body after a fitted lookup on a nonempty code-length code. -/
theorem cl_after {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {bs : List UInt8} {cl : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (size : s.lens.size = 320)
    (nlen : s.nlen.toNat ≤ 286) (ndist : s.ndist.toNat ≤ 30)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (initialized : ∀ k, k < s.«have».toNat → (s.lens.getD k 0).toNat ≤ 15)
    (B : BitInv h l bs) (here : Code) (width : here.bits.toNat ≤ 7)
    (enough : here.bits.toNat ≤ l.bits.toNat) (small : here.val.toNat < 19)
    (acc : Acceptable .codeLength cl)
    (dec : decodeSym cl (stream l bs) = some (here.val.toNat, (stream l bs).drop here.bits.toNat))
    (hbEq : cl.getD here.val.toNat 0 = here.bits.toNat)
    (pre : l.bits.toNat < 8 ∨ ¬ CodeLenItem cl ((stream l bs).take (l.bits.toNat - 8))) :
    ∃ result regs after used, runX (clAfterLookup c here) l h = .ok ((result, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧ RegsKeep l regs ∧
      regs.next = inputAdvance l.next used ∧ AfterResult h r zs z s cl l bs result regs after used := by
  obtain ⟨_, nz, _⟩ := dec_split dec
  have lenP : (actualLengthPrefix s).length = s.«have».toNat := Zlib.Inftrees.Proofs.lensOf_length _ _
  have ltP : (actualLengthPrefix s).length < s.nlen.toNat + s.ndist.toNat := by omega
  by_cases literal : here.val < 16
  · exact cl_lit hc hs size more (by omega) initialized B here width enough
      (UInt16.lt_iff_toNat_lt.mp literal) acc dec pre
  by_cases sym16 : here.val = 16
  · exact cl_prev hr hc hz hs size nlen ndist more initialized B here width sym16 acc dec hbEq pre
  have notLit : ¬ here.val.toNat < 16 := (not_congr UInt16.lt_iff_toNat_lt).mp literal
  have not16 : here.val.toNat ≠ 16 := fun e => sym16 (UInt16.toNat_inj.mp e)
  by_cases zero17 : here.val = 17
  · have symNat : here.val.toNat = 17 := by rw [zero17]; rfl
    refine cl_zero hr hc hz hs size nlen ndist more initialized B here width acc dec hbEq pre 3 3
      (by decide) (by decide) (by decide) (clAfterLookup_zero17 c here zero17) (by rw [symNat]; rfl) ?_ ?_
    · intro F rest lens p
      rcases codeLens_first p ltP (dec_word acc nz F) with ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, x, r2, rd, roomX, next⟩ | ⟨e, _⟩
      · omega
      · omega
      · exact ⟨x, r2, rd, roomX, next⟩
      · omega
    · intro x xb roomX
      rw [symNat]
      exact ZlibF.Math.CodeLengthPrefix.Trace.zero_short acc ltP (by rw [← symNat]; exact nz) xb roomX
  · have not17 : here.val.toNat ≠ 17 := fun e => zero17 (UInt16.toNat_inj.mp e)
    have symNat : here.val.toNat = 18 := by omega
    refine cl_zero hr hc hz hs size nlen ndist more initialized B here width acc dec hbEq pre 7 11
      (by decide) (by decide) (by decide) (clAfterLookup_zero18 c here literal sym16 zero17)
      (by rw [symNat]; rfl) ?_ ?_
    · intro F rest lens p
      rcases codeLens_first p ltP (dec_word acc nz F) with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨_, x, r2, rd, roomX, next⟩
      · omega
      · omega
      · omega
      · exact ⟨x, r2, rd, roomX, next⟩
    · intro x xb roomX
      rw [symNat]
      exact ZlibF.Math.CodeLengthPrefix.Trace.zero_long acc ltP (by rw [← symNat]; exact nz) xb roomX

#print axioms cl_after

/-! ## One iteration of the length loop -/

/-- The result of one iteration of the `CODELENS` length loop. -/
def IterResult (h : Heap) (r : ZStreamRef) (zs : Nat) (z : ZStream) (s : InflateState)
    (cl : List Nat) (l : IL) (bs : List UInt8) (result : Except Ex Bool) (regs : IL) (after : Heap)
    (used : Nat) : Prop :=
  (result = .error Ex.leave ∧ after = h ∧ regs.have_ = 0 ∧ stream regs (bs.drop used) = stream l bs ∧
      (regs.bits.toNat < 8 ∨ ((¬ ∀ k, cl.getD k 0 = 0) ∧
        ¬ CodeLenItem cl (natBits (regs.bits.toNat - 8) regs.hold.toNat)))) ∨
  (result = .ok true ∧ (∃ i, after = tcBadHeap h r zs z s i) ∧
      ∀ F rest lens, ¬ CodeLens cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s)
        ((stream l bs).take (l.bits.toNat + 8 * used) ++ F) rest lens) ∨
  (result = .ok false ∧ ∃ state cbits, after = setI h zs state ∧ ClWriteResult s state ∧
      stream l bs = cbits ++ stream regs (bs.drop used) ∧ regs.bits.toNat < 8 ∧
      ((¬ ∀ k, cl.getD k 0 = 0) →
        ZlibF.Math.CodeLengthPrefix.Trace cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) cbits
          (actualLengthPrefix state) ∧
        ∀ F rest lens, CodeLens cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) (cbits ++ F) rest lens →
          CodeLens cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix state) F rest lens) ∧
      ((∀ k, cl.getD k 0 = 0) → (∀ k, k < s.«have».toNat → s.lens.getD k 0 = 0) →
        ∀ k, k < state.«have».toNat → state.lens.getD k 0 = 0))

set_option maxHeartbeats 8000000 in
/-- One iteration of the `CODELENS` length loop: the root lookup, pulling a
byte only while the selected entry does not fit, then the item. The empty
code-length code reads every bit as length 0. -/
theorem cl_iter {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {bs : List UInt8} {cl : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s)
    (meaning : Zlib.Inftrees.Proofs.CodeLengthMeaning s.codes 0 s.lenbits.toNat cl)
    (ordinary : (¬ ∀ k, cl.getD k 0 = 0) → ∀ i, i < 2 ^ s.lenbits.toNat →
      ∃ e, s.codes[i]? = some e ∧ e.op = 0)
    (emptyCells : (∀ k, cl.getD k 0 = 0) → ∀ i, i < 2 ^ s.lenbits.toNat →
      s.codes[0 + i]? = some ⟨64, 1, 0⟩)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat) (B : BitInv h l bs)
    (bound : l.bits.toNat < 8 ∨ ((¬ ∀ k, cl.getD k 0 = 0) ∧
      ¬ CodeLenItem cl (natBits (l.bits.toNat - 8) l.hold.toNat))) :
    ∃ result regs after used, runX (clReadBody c) l h = .ok ((result, regs), after) ∧
      used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧ RegsKeep l regs ∧
      regs.next = inputAdvance l.next used ∧ IterResult h r zs z s cl l bs result regs after used := by
  obtain ⟨pointer, table, nlen, ndist, haveB, initialized⟩ := stateInv mode
  have get := CodeRef.get_istate_codes hs
  have acc := meaning.acceptable
  have root7 : s.lenbits.toNat ≤ 7 := table.2.1
  have readable : RootTableReadable s.codes 0 s.lenbits.toNat := by
    refine ⟨by omega, table.2.2.1, fun i inside => ?_⟩
    have cell := table.2.2.2 i inside
    dsimp only at cell
    omega
  have pointer' : (if false then s.distcode else s.lencode) = .ref (CodeRef.istate_codes zs) 0 := pointer
  -- a cell that does not fit the held bits: no symbol in them
  have nofitNone : ∀ (cur : IL) (bsx : List UInt8), BitInv h cur bsx → stream cur bsx = stream l bs →
      cur.bits.toNat < (codeLookupValue s.codes 0 s.lenbits.toNat cur).bits.toNat →
      decodeSym cl ((stream l bs).take cur.bits.toNat) = none := by
    intro cur bsx inv same lt
    cases d : decodeSym cl ((stream l bs).take cur.bits.toNat) with
    | none => rfl
    | some pair =>
      exfalso
      obtain ⟨sym, rr⟩ := pair
      rw [← MeaningDistance.short_take inv same _ (Nat.le_refl _)] at d
      obtain ⟨value, suffix, entry, rd, cellGet, _, _, _, fits, _⟩ := meaning.forward _ _ _ d
      rw [MeaningLookup.padded_natBits inv.hold_lt] at rd
      obtain ⟨rest, rd'⟩ := MeaningLookup.readBits_natBits_prefix (v := cur.hold.toNat)
        (show s.lenbits.toNat ≤ cur.bits.toNat + (15 - cur.bits.toNat) by omega)
      rw [rd'] at rd
      simp only [Option.some.injEq, Prod.mk.injEq] at rd
      obtain ⟨rfl, _⟩ := rd
      have same' : codeLookupValue s.codes 0 s.lenbits.toNat cur = entry := by
        unfold codeLookupValue
        simp only [Array.getD_eq_getD_getElem?, cellGet, Option.getD_some]
      rw [same'] at lt
      rw [natBits_length] at fits
      omega
  let Fail : Nat → Prop := fun k => decodeSym cl ((stream l bs).take k) = none ∧ ((∀ k, cl.getD k 0 = 0) → k = 0)
  obtain ⟨result, looked, used1, run1, u1le, inv1, same1, shape1, cnt1, _, sel1, kinds1, ok1, lv1, nxt1, fails1⟩ :=
    MeaningDistance.lookupLoop_fail (body := dataLookupBody c false)
      (query := codeLookupValue s.codes 0 s.lenbits.toNat)
      (need := fun entry => entry.bits.toUInt32) (fun _ => rfl)
      (by intro current; rw [UInt8.toNat_toUInt32]; exact readable.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (by intro current _; exact dataLookupBody_run false current hc hs pointer' get readable) B Fail
      (by
        intro current used shape inv same cnt nofit
        have lt : current.bits.toNat < (codeLookupValue s.codes 0 s.lenbits.toNat current).bits.toNat := by
          have := (not_congr UInt32.le_iff_toNat_le).mp nofit
          rw [UInt8.toNat_toUInt32] at this
          omega
        refine ⟨nofitNone current _ inv same lt, fun empty => ?_⟩
        have cell := emptyCells empty _ (Nat.mod_lt current.hold.toNat (Nat.two_pow_pos s.lenbits.toNat))
        have value : codeLookupValue s.codes 0 s.lenbits.toNat current = ⟨64, 1, 0⟩ := by
          unfold codeLookupValue
          simp only [Array.getD_eq_getD_getElem?, cell, Option.getD_some]
        rw [value] at lt
        change current.bits.toNat < 1 at lt
        omega)
  have keep1 : RegsKeep l looked := MeaningDistance.keep_of_lookup shape1
  have lookRun : runX (lookup1 c false) l h = .ok ((result, looked), h) := by
    rw [lookup1_data_eq]; exact run1
  have sLen := tcStream_length B
  have lookedShort : ∀ k, k ≤ looked.bits.toNat → natBits k looked.hold.toNat = (stream l bs).take k :=
    fun k le => MeaningDistance.short_take inv1 same1 k le
  rcases kinds1 with rfl | rfl
  · -- the selected entry fits
    have fit := ok1 rfl
    rw [UInt8.toNat_toUInt32] at fit
    have run0 : runX (clReadBody c) l h = runX (clAfterLookup c looked.here) looked h := by
      rw [clReadBody_eq, runX_bind, lookRun]
      dsimp only
      rw [runX_bind, runX_get]
    have idx : looked.hold.toNat % 2 ^ s.lenbits.toNat < 2 ^ s.lenbits.toNat := Nat.mod_lt _ (Nat.two_pow_pos _)
    by_cases empty : ∀ k, cl.getD k 0 = 0
    · -- the empty code: a zero length per bit
      have cell := emptyCells empty _ idx
      have hereEq : looked.here = ⟨64, 1, 0⟩ := by
        rw [sel1]
        unfold codeLookupValue
        simp only [Array.getD_eq_getD_getElem?, cell, Option.getD_some]
      have literal : looked.here.val.toNat < 16 := by rw [hereEq]; decide
      have width : looked.here.bits.toNat ≤ 7 := by rw [hereEq]; decide
      obtain ⟨run2, inv2, remaining, count, values⟩ :=
        clAfterLookup_literal_run hc hs size (by omega) literal width fit inv1 initialized
      have hb1 : looked.here.bits.toNat = 1 := by rw [hereEq]; rfl
      refine ⟨.ok false, _, setI h zs (clWrite s looked.here.val), used1 + 0, run0.trans run2, by omega,
        by simpa only [List.drop_drop, Nat.add_zero] using inv2, keep1, by rw [Nat.add_zero]; exact nxt1,
        Or.inr (Or.inr ⟨rfl, clWrite s looked.here.val, (stream l bs).take 1, rfl,
          ⟨rfl, by simp [clWrite, size], by rw [count]; omega, by rw [count]; omega, values⟩, ?_, ?_,
          fun ne => absurd empty ne, ?_⟩)⟩
      · rw [Nat.add_zero, remaining, same1, hb1, List.take_append_drop]
      · change (looked.bits - looked.here.bits.toUInt32).toNat < 8
        rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; rw [UInt8.toNat_toUInt32]; exact fit),
          UInt8.toNat_toUInt32, hb1]
        rcases Nat.eq_zero_or_pos used1 with u0 | upos
        · rcases bound with lt | ⟨ne, _⟩
          · omega
          · exact absurd empty ne
        · obtain ⟨_, zero⟩ := fails1 (used1 - 1) (by omega)
          have := zero empty
          omega
      · intro _ zeros k inside
        change (s.lens.set! s.«have».toNat looked.here.val).getD k 0 = 0
        rw [Zlib.Inftrees.Proofs.getD_set!]
        split
        · rw [hereEq]
        · have : k < s.«have».toNat := by
            change k < (s.«have» + 1).toNat at inside
            rw [UInt32.toNat_add, UInt32.toNat_one, Nat.mod_eq_of_lt (by omega)] at inside
            rename_i ne
            have : ¬ k = s.«have».toNat := fun e => ne ⟨e.symm, by omega⟩
            omega
          exact zeros k this
    · -- a nonempty code: the symbol of the held bits
      obtain ⟨e, cellE, opE⟩ := ordinary empty _ idx
      have hereEq : looked.here = e := by
        rw [sel1]
        unfold codeLookupValue
        simp only [Nat.zero_add, Array.getD_eq_getD_getElem?, cellE, Option.getD_some]
      have cellGet : s.codes[0 + looked.hold.toNat % 2 ^ s.lenbits.toNat]? = some looked.here := by
        rw [Nat.zero_add, hereEq]; exact cellE
      obtain ⟨rest, rd'⟩ := MeaningLookup.readBits_natBits_prefix (v := looked.hold.toNat)
        (show s.lenbits.toNat ≤ looked.bits.toNat + (15 - looked.bits.toNat) by omega)
      have rd : readBits s.lenbits.toNat (Zlib.Inftrees.Spec.DecodeShort.padded
          (natBits looked.bits.toNat looked.hold.toNat)) =
          some (looked.hold.toNat % 2 ^ s.lenbits.toNat, rest) := by
        rw [MeaningLookup.padded_natBits inv1.hold_lt]
        exact rd'
      obtain ⟨symbol, small, valEq, bitsEq, decInp⟩ := meaning.sound _ _ _ _ rd cellGet
        (by rw [hereEq]; exact opE) (by rw [natBits_length]; exact fit)
      have width : looked.here.bits.toNat ≤ 7 := by
        have cell := table.2.2.2 _ idx
        dsimp only at cell
        rw [Nat.zero_add] at cell
        have g : s.codes.getD (looked.hold.toNat % 2 ^ s.lenbits.toNat) default = looked.here := by
          rw [hereEq]; simp only [Array.getD_eq_getD_getElem?, cellE, Option.getD_some]
        rw [g] at cell
        omega
      have dec : decodeSym cl (stream looked (bs.drop used1)) =
          some (looked.here.val.toNat, (stream looked (bs.drop used1)).drop looked.here.bits.toNat) := by
        unfold stream
        rw [dec_ext acc decInp, List.drop_append_of_le_length (by rw [natBits_length]; exact fit), valEq]
      have pre : looked.bits.toNat < 8 ∨
          ¬ CodeLenItem cl ((stream looked (bs.drop used1)).take (looked.bits.toNat - 8)) := by
        rw [same1]
        rcases Nat.eq_zero_or_pos used1 with u0 | upos
        · rcases bound with lt | ⟨_, ni⟩
          · left; omega
          · right
            rw [← lookedShort _ (by omega)]
            have bitsEq' : looked.bits.toNat = l.bits.toNat := by omega
            have holdEq : natBits (looked.bits.toNat - 8) looked.hold.toNat =
                natBits (l.bits.toNat - 8) l.hold.toNat := by
              rw [lookedShort _ (by omega), bitsEq', MeaningDistance.short_take B rfl _ (by omega)]
            rw [holdEq]
            exact ni
        · right
          obtain ⟨none, _⟩ := fails1 (used1 - 1) (by omega)
          rw [show l.bits.toNat + 8 * (used1 - 1) = looked.bits.toNat - 8 by omega] at none
          rintro ⟨_, _, _, _, d, _⟩
          rw [none] at d
          cases d
      obtain ⟨result2, regs, after, used2, run2, u2le, inv2, keep2, nxt2, res⟩ :=
        cl_after hr hc hz hs size nlen ndist more initialized inv1 looked.here width fit
          (by rw [valEq]; exact small) acc dec (by rw [valEq, ← bitsEq]) pre
      refine ⟨result2, regs, after, used1 + used2, run0.trans run2, by simp only [List.length_drop] at u2le; omega,
        by simpa only [List.drop_drop, Nat.add_comm] using inv2, keep1.trans keep2,
        by rw [nxt2, nxt1, inputAdvance_add], ?_⟩
      have dropEq : (bs.drop used1).drop used2 = bs.drop (used1 + used2) := by
        rw [List.drop_drop, Nat.add_comm]
      unfold AfterResult at res
      unfold IterResult
      rw [same1, dropEq] at res
      rcases res with ⟨e1, e2, e3, e4, e5⟩ | ⟨e1, e2, e3⟩ | ⟨e1, state, cbits, e2, e3, e4, e5, e6, e7⟩
      · refine Or.inl ⟨e1, e2, e3, e4, ?_⟩
        rcases e5 with lt | ni
        · exact Or.inl lt
        · refine Or.inr ⟨empty, ?_⟩
          have invR : BitInv h regs (bs.drop (used1 + used2)) := by rw [e2] at inv2; rwa [dropEq] at inv2
          rw [MeaningDistance.short_take invR e4 _ (by omega)]
          exact ni
      · refine Or.inr (Or.inl ⟨e1, e2, ?_⟩)
        rw [show l.bits.toNat + 8 * (used1 + used2) = looked.bits.toNat + 8 * used2 by omega]
        exact e3
      · exact Or.inr (Or.inr ⟨e1, state, cbits, e2, e3, e4, e5, fun _ => ⟨e6, e7⟩,
          fun allZero => absurd allZero empty⟩)
  · -- waiting for input
    obtain ⟨have0, nofit⟩ := lv1 rfl
    have lt : looked.bits.toNat < looked.here.bits.toNat := by
      have := (not_congr UInt32.le_iff_toNat_le).mp nofit
      rw [UInt8.toNat_toUInt32] at this
      omega
    have run0 : runX (clReadBody c) l h = .ok ((.error Ex.leave, looked), h) := by
      rw [clReadBody_eq, runX_bind, lookRun]
    refine ⟨.error Ex.leave, looked, h, used1, run0, u1le, inv1, keep1, nxt1, Or.inl ⟨rfl, rfl, have0, same1, ?_⟩⟩
    by_cases empty : ∀ k, cl.getD k 0 = 0
    · left
      have cell := emptyCells empty _ (Nat.mod_lt looked.hold.toNat (Nat.two_pow_pos s.lenbits.toNat))
      have hereEq : looked.here = ⟨64, 1, 0⟩ := by
        rw [sel1]
        unfold codeLookupValue
        simp only [Array.getD_eq_getD_getElem?, cell, Option.getD_some]
      rw [hereEq] at lt
      change looked.bits.toNat < 1 at lt
      omega
    · right
      refine ⟨empty, ?_⟩
      rw [lookedShort _ (by omega)]
      rintro ⟨_, _, _, _, d, _⟩
      have none := nofitNone looked _ inv1 same1 (by rw [← sel1]; exact lt)
      have e := dec_ext acc (Y := ((stream l bs).take looked.bits.toNat).drop (looked.bits.toNat - 8)) d
      rw [show (stream l bs).take (looked.bits.toNat - 8) =
          ((stream l bs).take looked.bits.toNat).take (looked.bits.toNat - 8) by
        rw [List.take_take, Nat.min_eq_left (by omega)], List.take_append_drop, none] at e
      cases e

#print axioms cl_iter

/-! ## The length loop -/

theorem dec_none_zero {cl : List Nat} (zero : ∀ k, cl.getD k 0 = 0) (inp : List Bool) :
    decodeSym cl inp = none := by
  unfold decodeSym
  rw [List.find?_eq_none.mpr (fun s _ => by
    have z := zero s
    rw [List.getD_eq_getElem?_getD] at z
    simp [z])]

theorem take_split {S C Y : List Bool} (eq : S = C ++ Y) (m : Nat) :
    S.take (C.length + m) = C ++ Y.take m := by
  rw [eq, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left]

/-- The facts of a nonempty code that the loop keeps. -/
def LoopTrace (cl : List Nat) (T : Nat) (P0 : List Nat) (consumed : List Bool) (P : List Nat) : Prop :=
  (¬ ∀ k, cl.getD k 0 = 0) →
    ZlibF.Math.CodeLengthPrefix.Trace cl T P0 consumed P ∧
    ∀ F rest lens, CodeLens cl T P0 (consumed ++ F) rest lens → CodeLens cl T P F rest lens

set_option maxHeartbeats 8000000 in
/-- The `CODELENS` length loop from a state with fewer than all lengths. It
leaves for input with the parse of the bits read so far, goes to `BAD` with
no parse of the bits read, or reads all lengths with fewer than 8 held bits. -/
theorem cl_loop {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} {bs : List UInt8} {cl : List Nat}
    (hr : c.strm = some r) (hc : c.st = some (.tab zs)) (hz : r.get h = some z)
    (hs : h.istates zs = some s) (size : s.lens.size = 320) (mode : s.mode = CODELENS)
    (stateInv : CodeLengthInvariant zs s)
    (meaning : Zlib.Inftrees.Proofs.CodeLengthMeaning s.codes 0 s.lenbits.toNat cl)
    (ordinary : (¬ ∀ k, cl.getD k 0 = 0) → ∀ i, i < 2 ^ s.lenbits.toNat →
      ∃ e, s.codes[i]? = some e ∧ e.op = 0)
    (emptyCells : (∀ k, cl.getD k 0 = 0) → ∀ i, i < 2 ^ s.lenbits.toNat →
      s.codes[0 + i]? = some ⟨64, 1, 0⟩)
    (more : s.«have».toNat < s.nlen.toNat + s.ndist.toNat)
    (zeros : (∀ k, cl.getD k 0 = 0) → ∀ k, k < s.«have».toNat → s.lens.getD k 0 = 0)
    (B : BitInv h l bs)
    (bound : l.bits.toNat < 8 ∨ ((¬ ∀ k, cl.getD k 0 = 0) ∧
      ¬ CodeLenItem cl (natBits (l.bits.toNat - 8) l.hold.toNat))) :
    ∃ (result : Except Ex Unit) (regs : IL) (after : Heap) (lensA : Array UInt16) (haveA : UInt32) (used : Nat)
      (consumed : List Bool),
      runX (clRead c) l h = .ok ((result, regs), after) ∧ used ≤ bs.length ∧ RegsKeep l regs ∧
      regs.next = inputAdvance l.next used ∧
      lensA.size = 320 ∧ haveA.toNat ≤ s.nlen.toNat + s.ndist.toNat ∧
      (∀ k, k < haveA.toNat → (lensA.getD k 0).toNat ≤ 15) ∧
      ((result = .error Ex.leave ∧ after = setI h zs { s with lens := lensA, «have» := haveA } ∧
          BitInv after regs (bs.drop used) ∧ regs.have_ = 0 ∧
          haveA.toNat < s.nlen.toNat + s.ndist.toNat ∧ stream l bs = consumed ++ stream regs (bs.drop used) ∧
          LoopTrace cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) consumed
            (actualLengthPrefix { s with lens := lensA, «have» := haveA }) ∧
          ((∀ k, cl.getD k 0 = 0) → ∀ k, k < haveA.toNat → lensA.getD k 0 = 0) ∧
          (regs.bits.toNat < 8 ∨ ((¬ ∀ k, cl.getD k 0 = 0) ∧
            ¬ CodeLenItem cl (natBits (regs.bits.toNat - 8) regs.hold.toNat)))) ∨
       (result = .ok () ∧ (∃ sB, after.istates zs = some sB ∧ sB.mode = BAD) ∧
          (∀ zs' s', c.st = some (.tab zs') → after.istates zs' = some s' → s'.mode = BAD) ∧
          BitInv after regs (bs.drop used) ∧
          ∀ F rest lens, ¬ CodeLens cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s)
            ((stream l bs).take (l.bits.toNat + 8 * used) ++ F) rest lens) ∨
       (result = .ok () ∧ after = setI h zs { s with lens := lensA, «have» := haveA } ∧
          BitInv after regs (bs.drop used) ∧
          haveA.toNat = s.nlen.toNat + s.ndist.toNat ∧ stream l bs = consumed ++ stream regs (bs.drop used) ∧
          LoopTrace cl (s.nlen.toNat + s.ndist.toNat) (actualLengthPrefix s) consumed
            (actualLengthPrefix { s with lens := lensA, «have» := haveA }) ∧
          ((∀ k, cl.getD k 0 = 0) → ∀ k, k < haveA.toNat → lensA.getD k 0 = 0) ∧
          regs.bits.toNat < 8)) := by
  obtain ⟨pointer, table, nlen, ndist, haveB, initialized⟩ := stateInv mode
  let T := s.nlen.toNat + s.ndist.toNat
  let St : Array UInt16 → UInt32 → InflateState := fun lensA haveA => { s with lens := lensA, «have» := haveA }
  let P : IL → Heap → Prop := fun regs heap => ∃ (lensA : Array UInt16) (haveA : UInt32) (used : Nat) (consumed : List Bool),
    heap = setI h zs (St lensA haveA) ∧ lensA.size = 320 ∧ haveA.toNat ≤ T ∧
    (∀ k, k < haveA.toNat → (lensA.getD k 0).toNat ≤ 15) ∧ used ≤ bs.length ∧
    BitInv heap regs (bs.drop used) ∧ RegsKeep l regs ∧ regs.next = inputAdvance l.next used ∧
    stream l bs = consumed ++ stream regs (bs.drop used) ∧
    LoopTrace cl T (actualLengthPrefix s) consumed (actualLengthPrefix (St lensA haveA)) ∧
    ((∀ k, cl.getD k 0 = 0) → ∀ k, k < haveA.toNat → lensA.getD k 0 = 0) ∧
    (regs.bits.toNat < 8 ∨ ((¬ ∀ k, cl.getD k 0 = 0) ∧
      ¬ CodeLenItem cl (natBits (regs.bits.toNat - 8) regs.hold.toNat))) ∧
    (haveA = s.«have» ∨ regs.bits.toNat < 8)
  let rank : IL → Heap → Nat := fun _ heap => T - ((heap.istates zs).getD default).«have».toNat
  let Q : Except Ex Unit → IL → Heap → Prop := fun result regs after =>
    ∃ (lensA : Array UInt16) (haveA : UInt32) (used : Nat) (consumed : List Bool),
      used ≤ bs.length ∧ RegsKeep l regs ∧ regs.next = inputAdvance l.next used ∧
      lensA.size = 320 ∧ haveA.toNat ≤ T ∧ (∀ k, k < haveA.toNat → (lensA.getD k 0).toNat ≤ 15) ∧
      ((result = .error Ex.leave ∧ after = setI h zs (St lensA haveA) ∧
          BitInv after regs (bs.drop used) ∧ regs.have_ = 0 ∧
          haveA.toNat < T ∧ stream l bs = consumed ++ stream regs (bs.drop used) ∧
          LoopTrace cl T (actualLengthPrefix s) consumed (actualLengthPrefix (St lensA haveA)) ∧
          ((∀ k, cl.getD k 0 = 0) → ∀ k, k < haveA.toNat → lensA.getD k 0 = 0) ∧
          (regs.bits.toNat < 8 ∨ ((¬ ∀ k, cl.getD k 0 = 0) ∧
            ¬ CodeLenItem cl (natBits (regs.bits.toNat - 8) regs.hold.toNat)))) ∨
       (result = .ok () ∧ (∃ sB, after.istates zs = some sB ∧ sB.mode = BAD) ∧
          (∀ zs' s', c.st = some (.tab zs') → after.istates zs' = some s' → s'.mode = BAD) ∧
          BitInv after regs (bs.drop used) ∧
          ∀ F rest lens, ¬ CodeLens cl T (actualLengthPrefix s)
            ((stream l bs).take (l.bits.toNat + 8 * used) ++ F) rest lens) ∨
       (result = .ok () ∧ after = setI h zs (St lensA haveA) ∧ BitInv after regs (bs.drop used) ∧
          haveA.toNat = T ∧ stream l bs = consumed ++ stream regs (bs.drop used) ∧
          LoopTrace cl T (actualLengthPrefix s) consumed (actualLengthPrefix (St lensA haveA)) ∧
          ((∀ k, cl.getD k 0 = 0) → ∀ k, k < haveA.toNat → lensA.getD k 0 = 0) ∧
          regs.bits.toNat < 8))
  have sLen := tcStream_length B
  have lenP0 : (actualLengthPrefix s).length = s.«have».toNat := Zlib.Inftrees.Proofs.lensOf_length _ _
  have loop := xwhileBrk_rank (cond := clReadCond c) (body := clReadBody c) P rank Q ?_ (l := l) (h := h) ?_ ?_
  · obtain ⟨result, regs, after, run, lensA, haveA, used, consumed, ub, keep, nxt, sz, hb, vals, res⟩ := loop
    exact ⟨result, regs, after, lensA, haveA, used, consumed, by rw [clRead_eq]; exact run, ub, keep, nxt,
      sz, hb, vals, res⟩
  · intro regs heap inv
    obtain ⟨lensA, haveA, used, consumed, heapEq, sz, hb, vals, ub, binv, keep, nxt, source, tr, zs0, bnd, first⟩ := inv
    subst heapEq
    have get : (setI h zs (St lensA haveA)).istates zs = some (St lensA haveA) := by simp
    have hz' : r.get (setI h zs (St lensA haveA)) = some z := by simpa using hz
    have sum : ((St lensA haveA).nlen + (St lensA haveA).ndist).toNat = T := by
      change (s.nlen + s.ndist).toNat = _
      rw [UInt32.toNat_add, Nat.mod_eq_of_lt (by omega)]
    have condRun : runX (clReadCond c) regs (setI h zs (St lensA haveA)) =
        .ok ((.ok (decide ((St lensA haveA).«have» < (St lensA haveA).nlen + (St lensA haveA).ndist)), regs),
          setI h zs (St lensA haveA)) := by
      unfold clReadCond
      rw [hc]
      simp [runX_bind, runX_lift, ldI_eq, get, runX_pure]
    by_cases moreA : (St lensA haveA).«have» < (St lensA haveA).nlen + (St lensA haveA).ndist
    · have moreNat : haveA.toNat < T := by
        have := UInt32.lt_iff_toNat_lt.mp moreA
        rw [sum] at this
        exact this
      have invA : CodeLengthInvariant zs (St lensA haveA) := by
        intro _
        exact ⟨pointer, table, nlen, ndist, hb, vals⟩
      obtain ⟨result, regs2, after, u, run2, uLe, inv2, keep2, nxt2, res⟩ :=
        cl_iter hr hc hz' get sz mode invA meaning ordinary emptyCells moreNat binv bnd
      refine ⟨.ok true, regs, _, by simpa only [moreA, decide_true] using condRun, result, regs2, after, run2, ?_⟩
      have uLe' : used + u ≤ bs.length := by simp only [List.length_drop] at uLe; omega
      have dropEq : (bs.drop used).drop u = bs.drop (used + u) := by rw [List.drop_drop, Nat.add_comm]
      have nxt' : regs2.next = inputAdvance l.next (used + u) := by rw [nxt2, nxt, inputAdvance_add]
      have lenP : (actualLengthPrefix (St lensA haveA)).length = haveA.toNat := Zlib.Inftrees.Proofs.lensOf_length _ _
      unfold IterResult at res
      rcases res with ⟨rfl, rfl, have0, str, bnd2⟩ | ⟨rfl, ⟨i, rfl⟩, doom⟩ | ⟨rfl, state, cbits, rfl, frame, str, small, tr2, zs2⟩
      · refine ⟨lensA, haveA, used + u, consumed, uLe', keep.trans keep2, nxt', sz, hb, vals,
          Or.inl ⟨rfl, rfl, by rw [← dropEq]; exact inv2, have0, moreNat, ?_, tr, zs0, bnd2⟩⟩
        rw [← dropEq, str]; exact source
      · refine ⟨lensA, haveA, used + u, consumed, uLe', keep.trans keep2, nxt', sz, hb, vals,
          Or.inr (Or.inl ⟨rfl, ⟨{ St lensA haveA with mode := BAD }, by simp [tcBadHeap], rfl⟩, ?_,
            by rw [← dropEq]; exact inv2, ?_⟩)⟩
        · intro zs' s' st' hs'
          rw [hc] at st'
          cases st'
          simp only [tcBadHeap, setI_istates_same, Option.some.injEq] at hs'
          rw [← hs']
        · intro F rest lens p
          have lenEq : consumed.length + regs.bits.toNat = l.bits.toNat + 8 * used := by
            have a := congrArg List.length source
            rw [List.length_append, tcStream_length binv, List.length_drop] at a
            omega
          by_cases empty : ∀ k, cl.getD k 0 = 0
          · exact codeLens_none p (by omega) (dec_none_zero empty _)
          · rw [show l.bits.toNat + 8 * (used + u) = consumed.length + (regs.bits.toNat + 8 * u) by omega,
              take_split source, List.append_assoc] at p
            exact doom F rest lens ((tr empty).2 _ _ _ p)
      · obtain ⟨frameEq, sz2, hb2, progress, vals2⟩ := frame
        have stEq : state = St state.lens state.«have» := by
          rw [frameEq]
        refine ⟨⟨state.lens, state.«have», used + u, consumed ++ cbits,
          by rw [setI_setI]; exact congrArg (setI h zs) stEq, sz2,
          by change _ ≤ (St lensA haveA).nlen.toNat + (St lensA haveA).ndist.toNat at hb2; omega,
          vals2, uLe', by rw [← dropEq]; exact inv2, keep.trans keep2, nxt', ?_, ?_, ?_, Or.inl small,
          Or.inr small⟩, ?_⟩
        · rw [source, str, dropEq, List.append_assoc]
        · intro ne
          obtain ⟨t1, c1⟩ := tr ne
          obtain ⟨t2, c2⟩ := tr2 ne
          rw [← stEq]
          exact ⟨t1.trans t2, fun F rest lens p => c2 F rest lens (c1 _ _ _ (by rwa [List.append_assoc] at p))⟩
        · intro empty k inside
          exact zs2 empty (zs0 empty) k inside
        · dsimp only [rank]
          simp only [setI_istates_same, Option.getD_some]
          have e1 : (St lensA haveA).«have».toNat = haveA.toNat := rfl
          have e2 : (St lensA haveA).nlen.toNat + (St lensA haveA).ndist.toNat =
              s.nlen.toNat + s.ndist.toNat := rfl
          rw [e1] at progress
          rw [e2] at hb2
          show s.nlen.toNat + s.ndist.toNat - state.«have».toNat < s.nlen.toNat + s.ndist.toNat - haveA.toNat
          omega
    · have doneNat : haveA.toNat = T := by
        have := (not_congr UInt32.lt_iff_toNat_lt).mp moreA
        rw [sum] at this
        change ¬ haveA.toNat < T at this
        omega
      refine ⟨.ok false, regs, _, by simpa only [moreA, decide_false] using condRun,
        lensA, haveA, used, consumed, ub, keep, nxt, sz, hb, vals,
        Or.inr (Or.inr ⟨rfl, rfl, binv, doneNat, source, tr, zs0, ?_⟩)⟩
      rcases first with e | small
      · subst e; omega
      · exact small
  · refine ⟨s.lens, s.«have», 0, [], ?_, size, haveB, initialized, by omega, by simpa using B,
      ⟨rfl, rfl, rfl, rfl, rfl⟩, (inputAdvance_zero _).symm, by simp, ?_, zeros, bound, Or.inl rfl⟩
    · exact (tcSetI_same hs).symm
    · intro _
      refine ⟨ZlibF.Math.CodeLengthPrefix.Trace.refl _ _ _, fun F rest lens p => ?_⟩
      simpa using p
  · dsimp only [rank]
    rw [hs]
    simp only [Option.getD_some]
    unfold fuel
    omega

#print axioms cl_loop

end Zlib.Inflate.Proofs.MeaningCodeLens
