import ZlibF.Proof.«inflate.c.meaning-distance»
import ZlibF.Proof.«inflate.c.length-finish»

/-!
# inflate.c: the slow `LEN` and `LEN_` keep the format meaning

On the slow branch (not enough input or output for `inflate_fast`, or held
bits left over), `case LEN` sets `back = 0` and looks up the literal/length
symbol in the root table and, through a link, in a second-level table,
pulling a byte only while the selected entry does not fit the held bits
(`lookupLoop_fail`). When the call leaves for input, the held bits without
their last byte hold no valid literal/length symbol (the bound of
`BodyMatches` at `.none`, P13). A fitted entry is classified as zlib does:

* a literal (`op = 0`) goes to `LIT` with the literal pending
  (`DeflateParsed.partialLiteral`);
* the end of the block (`op & 32`) goes to `TYPE` at a block boundary
  (`endOfBlock`) or after the final block (`endOfFinal`), with fewer than 8
  held bits: the code of the end-of-block symbol is longer than the held bits
  without their last byte;
* an invalid code (`op & 64`) goes to `BAD`, and no continuation of the input
  is valid (`Token.Rejected.length`);
* a length (`op & 16`) goes to `LENEXT` (`Pending.lengthExtra`) and falls
  through to `lenext_step`.

`case LEN_` sets the mode `LEN` and runs `case LEN`. The fast branch is a
separate lemma.
-/

namespace Zlib.Inflate.Proofs.MeaningLength
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.MeaningLit Zlib.Inflate.Proofs.MeaningCopy Zlib.Inflate.Proofs.MeaningBits
open Zlib.Inflate.Proofs.MeaningBlock Zlib.Inflate.Proofs.MeaningMatch ZlibF.Spec.Proofs Zlib.Inffast.Spec
open Zlib.Inflate.Proofs.MeaningDistance
set_option autoImplicit false

/-! ## Lookups in the literal/length table -/

/-- The root literal/length lookup with the reason for every pulled byte. -/
theorem lookup1_len_fail {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat) (B : BitInv h l bs) (Fail : Nat → Prop)
    (fail : ∀ current used, LookupRegShape l current → BitInv h current (bs.drop used) →
      stream current (bs.drop used) = stream l bs →
      current.bits.toNat = l.bits.toNat + 8 * used →
      current.bits.toNat < (codeLookupValue ca offset s.lenbits.toNat current).bits.toNat →
      Fail current.bits.toNat) :
    ∃ result regs used,
      runX (lookup1 c false) l h = .ok ((result, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.here = codeLookupValue ca offset s.lenbits.toNat regs ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧ regs.bits.toNat < regs.here.bits.toNat) ∧
      regs.next = inputAdvance l.next used ∧
      ∀ k, k < used → Fail (l.bits.toNat + 8 * k) := by
  have readable := lenTableSafe_readable safe
  rw [lookup1_data_eq]
  obtain ⟨result, regs, used, run, usedBound, inv, sameStream, shape, count, _, selected, kinds,
    enough, empty, cursor, fails⟩ :=
    lookupLoop_fail (query := codeLookupValue ca offset s.lenbits.toNat)
      (need := fun entry => entry.bits.toUInt32) (fun _ => rfl)
      (by intro current; rw [UInt8.toNat_toUInt32]; exact readable.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _)))
      (by intro current _; exact dataLookupBody_run false current hc hs pointer get readable) B Fail
      (by
        intro current used shape inv same cnt nofit
        apply fail current used shape inv same cnt
        have := (not_congr UInt32.le_iff_toNat_le).mp nofit
        rw [UInt8.toNat_toUInt32] at this
        omega)
  refine ⟨result, regs, used, run, usedBound, inv, sameStream, shape, count, selected, kinds,
    fun ok => by have := enough ok; rwa [UInt8.toNat_toUInt32] at this, fun leave => ?_, cursor, fails⟩
  obtain ⟨e, nofit⟩ := empty leave
  refine ⟨e, ?_⟩
  have := (not_congr UInt32.le_iff_toNat_le).mp nofit
  rw [UInt8.toNat_toUInt32] at this
  omega

/-- The second-level literal/length lookup with the reason for every pulled byte. -/
theorem lookup2_len_fail {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8} (last : Code)
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (remembered : l.last = last) (link : LinkOK LenLeaf ca offset last)
    (B : BitInv h l bs) (Fail : Nat → Prop)
    (fail : ∀ current used, LookupRegShape l current → BitInv h current (bs.drop used) →
      stream current (bs.drop used) = stream l bs →
      current.bits.toNat = l.bits.toNat + 8 * used →
      current.bits.toNat < last.bits.toNat + (subLookupValue ca offset last current).bits.toNat →
      Fail current.bits.toNat) :
    ∃ result regs used,
      runX (lookup2 c false) l h = .ok ((result, regs), h) ∧
      used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.here = subLookupValue ca offset last regs ∧ LenLeaf last.bits.toNat regs.here ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → last.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0 ∧
        regs.bits.toNat < last.bits.toNat + regs.here.bits.toNat) ∧
      regs.next = inputAdvance l.next used ∧
      ∀ k, k < used → Fail (l.bits.toNat + 8 * k) := by
  have leaf : ∀ current, LenLeaf last.bits.toNat (subLookupValue ca offset last current) := by
    intro current
    exact link.2.2.2.2 _ (subLookupIndex_lt _ _)
  have needNat : ∀ current, (last.bits.toUInt32 + (subLookupValue ca offset last current).bits.toUInt32).toNat =
      last.bits.toNat + (subLookupValue ca offset last current).bits.toNat := by
    intro current
    have bound := (leaf current).1
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have pointer' : (if false then s.distcode else s.lencode) = .ref ref offset := pointer
  rw [lookup2_data_eq]
  obtain ⟨result, regs, used, run, usedBound, inv, sameStream, shape, count, _, selected, kinds,
    enough, empty, cursor, fails⟩ :=
    lookupLoop_fail (query := subLookupValue ca offset last)
      (need := fun entry => last.bits.toUInt32 + entry.bits.toUInt32) (fun _ => rfl)
      (by intro current; rw [needNat]; have := (leaf current).1; omega)
      (by
        intro current frame
        have lastEq : current.last = last := by rw [frame, remembered]
        exact dataSubLookupBody_run false current last hc hs pointer' get lastEq link) B Fail
      (by
        intro current used shape inv same cnt nofit
        apply fail current used shape inv same cnt
        have := (not_congr UInt32.le_iff_toNat_le).mp nofit
        rw [needNat] at this
        omega)
  refine ⟨result, regs, used, run, usedBound, inv, sameStream, shape, count, selected,
    by rw [selected]; exact leaf regs, kinds,
    fun ok => by have := enough ok; rwa [selected, needNat, ← selected] at this, fun leave => ?_,
    cursor, fails⟩
  obtain ⟨e, nofit⟩ := empty leave
  refine ⟨e, ?_⟩
  have := (not_congr UInt32.le_iff_toNat_le).mp nofit
  rw [selected, needNat, ← selected] at this
  omega

/-! ## The meaning of a literal/length lookup -/

section LenMeaning
open Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inflate.Proofs.MeaningLookup

theorem lensValid {symbol : Nat} : ValidSymbol LENS symbol ↔ symbol ≤ 285 := by
  unfold ValidSymbol
  rw [if_pos rfl]

theorem lensAccepted {entry : Code} :
    LeafAccepted LENS entry ↔ (entry.op &&& 32 != 0) = true ∨ entry.op &&& 64 = 0 := by
  unfold LeafAccepted
  rw [if_pos rfl]

theorem u8_and_zero (o k : UInt8) : o &&& k = 0 ↔ o.toNat &&& k.toNat = 0 := by
  rw [← UInt8.toNat_inj, UInt8.toNat_and]
  rfl

theorem length_op_bits : ∀ x, x ≤ 5 → (16 + x) &&& 32 = 0 ∧ (16 + x) &&& 64 = 0 ∧ (16 + x) % 16 = x := by
  decide

theorem lengthExtras_le' : ∀ i < 29, lengthExtras.getD i 0 ≤ 5 := by decide

/-- The meaning of an accepted leaf by zlib's classification. -/
theorem lensEntry {symbol : Nat} {entry : Code} (le : symbol ≤ 285) (meaning : SymbolEntry LENS symbol entry) :
    (symbol < 256 ∧ entry.op = 0 ∧ entry.val.toNat = symbol) ∨
    (symbol = 256 ∧ entry.op = 96) ∨
    (257 ≤ symbol ∧ entry.op.toNat = 16 + lengthExtras.getD (symbol - 257) 0 ∧
      entry.val.toNat = lengthBases.getD (symbol - 257) 0) := by
  unfold SymbolEntry at meaning
  rw [if_pos rfl] at meaning
  by_cases a : symbol < 256
  · rw [if_pos a] at meaning
    exact Or.inl ⟨a, meaning⟩
  · rw [if_neg a] at meaning
    by_cases b : symbol = 256
    · rw [if_pos b] at meaning
      exact Or.inr (Or.inl ⟨b, meaning.1⟩)
    · rw [if_neg b, if_pos le] at meaning
      exact Or.inr (Or.inr ⟨by omega, meaning⟩)

/-- A query that does not fit the held bits: they hold no valid symbol. -/
theorem nofit_invalid_len {ca : Array Code} {offset root used : Nat} {L : List Nat}
    (inv : Inv LENS ca offset root used L) {inp : List Bool} {entry : Code} {consumed : Nat}
    (query : tableRead LENS ca offset root (DecodeShort.padded inp) = some (entry, consumed))
    (nofit : inp.length < consumed) :
    ∀ symbol rest, decodeSym L inp = some (symbol, rest) → 285 < symbol := by
  intro symbol rest decoded
  apply Classical.byContradiction
  intro le
  obtain ⟨e', c', q', _, _, _, fits, _⟩ :=
    Zlib.Inftrees.Proofs.DecodeForward.lookup_of_decode inv decoded (lensValid.mpr (by omega))
  rw [query] at q'
  simp only [Option.some.injEq, Prod.mk.injEq] at q'
  omega

theorem slow_isLink_len {entry : Code} : Subtable.IsLink LENS entry = true ↔ SlowLenLink entry := by
  unfold Subtable.IsLink SlowLenLink
  rw [if_pos rfl]
  simp

/-- The query of the held bits at a state, as zlib's root and link reads see it. -/
theorem len_query {ca : Array Code} {offset root used : Nat} {L : List Nat}
    (inv : Inv LENS ca offset root used L) (safe : LenTableSafe ca offset root)
    {bits hold : Nat} (lt : hold < 2 ^ bits) :
    (¬ SlowLenLink (ca.getD (offset + hold % 2 ^ root) default) →
      LenLeaf 0 (ca.getD (offset + hold % 2 ^ root) default) ∧
      tableRead LENS ca offset root (DecodeShort.padded (natBits bits hold)) =
        some (ca.getD (offset + hold % 2 ^ root) default,
          (ca.getD (offset + hold % 2 ^ root) default).bits.toNat)) ∧
    (SlowLenLink (ca.getD (offset + hold % 2 ^ root) default) →
      (ca.getD (offset + hold % 2 ^ root) default).bits.toNat = root ∧
      LinkOK LenLeaf ca offset (ca.getD (offset + hold % 2 ^ root) default) ∧
      tableRead LENS ca offset root (DecodeShort.padded (natBits bits hold)) =
        some (ca.getD (offset + (ca.getD (offset + hold % 2 ^ root) default).val.toNat +
            subLookupIndexNat (ca.getD (offset + hold % 2 ^ root) default) hold) default,
          (ca.getD (offset + hold % 2 ^ root) default).bits.toNat +
            (ca.getD (offset + (ca.getD (offset + hold % 2 ^ root) default).val.toNat +
              subLookupIndexNat (ca.getD (offset + hold % 2 ^ root) default) hold)
              default).bits.toNat)) := by
  have root15 : root ≤ 15 := safe.1
  have idx : hold % 2 ^ root < 2 ^ root := Nat.mod_lt _ (Nat.two_pow_pos _)
  have inside : offset + hold % 2 ^ root < ca.size := by have := safe.2.1; omega
  have cell := safe.2.2 _ idx
  generalize e0def : ca.getD (offset + hold % 2 ^ root) default = e0 at cell ⊢
  have get0 : ca[offset + hold % 2 ^ root]? = some e0 := by
    rw [← e0def]; simp [Array.getD, inside]
  constructor
  · intro nl
    have leaf : LenLeaf 0 e0 := by
      split at cell
      · rename_i lk
        exact absurd (lenLink_slow lk cell) nl
      · exact cell
    refine ⟨leaf, ?_⟩
    have notLink : Subtable.IsLink LENS e0 = false := by
      cases hl : Subtable.IsLink LENS e0
      · rfl
      · exact absurd (slow_isLink_len.mp hl) nl
    have := tableRead_root (type := LENS) (ca := ca) (offset := offset) (root := root) lt root15 inside
      (by rw [e0def]; exact notLink)
    rw [e0def] at this
    exact this
  · intro sl
    have isLink : Subtable.IsLink LENS e0 = true := slow_isLink_len.mpr sl
    obtain ⟨bitsEq, sub⟩ := inv.subtables _ e0 idx get0 isLink
    have link : LinkOK LenLeaf ca offset e0 := by
      split at cell
      · exact cell
      · rename_i nlink
        exact absurd (slowLenLink_fast sl) nlink
    refine ⟨bitsEq, link, ?_⟩
    have := tableRead_link (type := LENS) (ca := ca) (offset := offset) (root := root) lt root15 inside
      (by rw [e0def]; exact isLink) (by rw [e0def]; exact sub.2.2.1)
      (by
        rw [e0def]
        have := sub.2.2.2.1
        have : subLookupIndexNat e0 hold < 2 ^ e0.op.toNat := ZlibF.Math.InflateLookup.slice_lt _ _ _
        omega)
    rw [e0def] at this
    exact this

/-- After a valid symbol of `consumed` bits fits the held bits, fewer than 8
are left when the held bits without their last byte hold no valid symbol. -/
theorem left_short_len {L : List Nat} (ext : Ext L) {inp rest : List Bool} {symbol : Nat}
    (decoded : decodeSym L inp = some (symbol, rest)) (valid : symbol ≤ 285)
    (short : inp.length < 8 ∨ ∀ s r, decodeSym L (inp.take (inp.length - 8)) = some (s, r) → 285 < s) :
    inp.length - L.getD symbol 0 < 8 := by
  rcases short with lt | none
  · omega
  · apply Classical.byContradiction
    intro ge
    have := decode_take ext decoded (k := inp.length - 8) (by omega)
    have := none _ _ this
    omega

end LenMeaning

/-! ## The runs of the slow `LEN` -/

theorem len_prefix {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (l : IL) :
    runX (lenSlow c) l h = runX (do lenLookup c; lenFinish c) l (setI h zs { s with back := 0 }) := by
  rw [lenSlow_split]
  simp only [runX_bind, runX_wrS E]

theorem len_run_leave {c : Ctx} {h : Heap} {l r1 : IL}
    (run1 : runX (lookup1 c false) l h = .ok ((.error Ex.leave, r1), h)) :
    runX (do lenLookup c; lenFinish c) l h = .ok ((.error Ex.leave, r1), h) := by
  unfold lenLookup
  simp only [runX_bind, run1]

theorem len_run_leaf {c : Ctx} {h : Heap} {l r1 : IL}
    (run1 : runX (lookup1 c false) l h = .ok ((.ok (), r1), h)) (leaf : ¬ SlowLenLink r1.here) :
    runX (do lenLookup c; lenFinish c) l h = runX (lenFinish c) r1 h := by
  unfold lenLookup
  simp only [runX_bind, run1, runX_get, lenRootTail_leaf c _ leaf, runX_pure]

theorem len_run_sub_leave {c : Ctx} {h : Heap} {l r1 r2 : IL}
    (run1 : runX (lookup1 c false) l h = .ok ((.ok (), r1), h)) (link : SlowLenLink r1.here)
    (run2 : runX (lookup2 c false) { r1 with last := r1.here } h = .ok ((.error Ex.leave, r2), h)) :
    runX (do lenLookup c; lenFinish c) l h = .ok ((.error Ex.leave, r2), h) := by
  unfold lenLookup
  simp only [runX_bind, run1, runX_get, lenRootTail_link c _ link]
  unfold lenSubLookup
  simp only [runX_bind, runX_modify, run2]

theorem len_run_sub_ok {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) {l r1 r2 : IL} (n : Nat)
    (run1 : runX (lookup1 c false) l h = .ok ((.ok (), r1), h)) (link : SlowLenLink r1.here)
    (run2 : runX (lookup2 c false) { r1 with last := r1.here } h = .ok ((.ok (), r2), h))
    (lastEq : r2.last = r1.here) (backEq : s.back = Int32.ofNat n) (small : r1.here.bits.toNat ≤ 15)
    (nb : n + 15 < 2147483648) :
    runX (do lenLookup c; lenFinish c) l h =
      runX (lenFinish c)
        { r2 with hold := r2.hold >>> r1.here.bits.toUInt32.toUInt64, bits := r2.bits - r1.here.bits.toUInt32 }
        (setI h zs { s with back := Int32.ofNat (n + r1.here.bits.toNat) }) := by
  have small64 : r1.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
  have load : ldInflateState c.st h = .ok (s, h) := by rw [E.st, ldI_eq, E.hs]
  have checked := chk_back n r1.here.bits.toNat (by omega) h
  rw [← backEq] at checked
  have write : wrS c.st (fun s => { s with back := Int32.ofNat (n + r1.here.bits.toNat) }) h =
      .ok ((), setI h zs { s with back := Int32.ofNat (n + r1.here.bits.toNat) }) := by
    rw [E.st, wrI_eq, E.hs]
  unfold lenLookup
  simp only [runX_bind, run1, runX_get, lenRootTail_link c _ link]
  unfold lenSubLookup
  simp only [runX_bind, runX_modify, run2, runX_get, lastEq, DROPBITS_run _ h _ small64,
    runX_lift_ok load, runX_lift_ok checked, runX_lift_ok write]

theorem len_run_finish {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (l : IL) (n : Nat) (backEq : s.back = Int32.ofNat n)
    (small : l.here.bits.toNat ≤ 15) (nb : n + 15 < 2147483648) :
    runX (lenFinish c) l h =
      runX (lenLeafTail c l.here)
        { l with hold := l.hold >>> l.here.bits.toUInt32.toUInt64, bits := l.bits - l.here.bits.toUInt32 }
        (setI h zs { s with back := Int32.ofNat (n + l.here.bits.toNat), length := l.here.val.toUInt32 }) := by
  have small64 : l.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
  have load : ldInflateState c.st h = .ok (s, h) := by rw [E.st, ldI_eq, E.hs]
  have checked := chk_back n l.here.bits.toNat (by omega) h
  rw [← backEq] at checked
  have write : wrS c.st (fun s => { s with back := Int32.ofNat (n + l.here.bits.toNat), length := l.here.val.toUInt32 }) h =
      .ok ((), setI h zs { s with back := Int32.ofNat (n + l.here.bits.toNat), length := l.here.val.toUInt32 }) := by
    rw [E.st, wrI_eq, E.hs]
  unfold lenFinish lenLeafTail
  simp only [runX_bind, runX_get, DROPBITS_run l h _ small64,
    runX_lift_ok load, runX_lift_ok checked, runX_lift_ok write]

theorem lenTail_lit {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (here : Code) (l : IL) (zero : here.op = 0) :
    runX (lenLeafTail c here) l h = .ok ((.ok (), l), setI h zs { s with mode := LIT }) := by
  unfold lenLeafTail
  have z0 : (here.op.toNat == 0) = true := by simp [zero]
  simp only [z0, ite_true, runX_bind, runX_setMode E, runX_pure]

theorem lenTail_eob {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (here : Code) (l : IL) (nz : here.op ≠ 0)
    (eob : here.op &&& 32 ≠ 0) :
    runX (lenLeafTail c here) l h =
      .ok ((.ok (), l), setI h zs { s with back := -1, mode := TYPE }) := by
  unfold lenLeafTail
  have z0 : (here.op.toNat == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    exact nz (UInt8.toNat_inj.mp (by simpa using e))
  have e32 : (here.op &&& 32 != 0) = true := by simpa using eob
  simp only [z0, Bool.false_eq_true, ite_false, e32, ite_true, runX_bind, runX_wrS E, runX_pure]

theorem lenTail_bad {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (here : Code) (l : IL) (nz : here.op ≠ 0)
    (no32 : here.op &&& 32 = 0) (bad : here.op &&& 64 ≠ 0) :
    ∃ i, runX (lenLeafTail c here) l h = .ok ((.ok (), l), badHeap h r zs z s i) := by
  obtain ⟨i, _, run⟩ := runX_badMode E (msg := "invalid literal/length code") (by decide +kernel) l
  refine ⟨i, ?_⟩
  unfold lenLeafTail
  have z0 : (here.op.toNat == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    exact nz (UInt8.toNat_inj.mp (by simpa using e))
  have e32 : (here.op &&& 32 != 0) = false := by simp [no32]
  have e64 : (here.op &&& 64 != 0) = true := by simpa using bad
  simp only [z0, Bool.false_eq_true, ite_false, e32, e64, ite_true, runX_bind, run, runX_pure]

/-- The state `LEN` leaves for `LENEXT`. -/
def lenState (s : InflateState) (here : Code) : InflateState :=
  { s with extra := here.op.toUInt32 &&& 15, mode := LENEXT }

theorem lenTail_length {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (here : Code) (l : IL) (nz : here.op ≠ 0)
    (no32 : here.op &&& 32 = 0) (no64 : here.op &&& 64 = 0) :
    runX (lenLeafTail c here) l h = runX (inflate_LENEXT c) l (setI h zs (lenState s here)) := by
  unfold lenLeafTail
  have z0 : (here.op.toNat == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e
    exact nz (UInt8.toNat_inj.mp (by simpa using e))
  have e32 : (here.op &&& 32 != 0) = false := by simp [no32]
  have e64 : (here.op &&& 64 != 0) = false := by simp [no64]
  simp only [z0, Bool.false_eq_true, ite_false, e32, e64, runX_bind, runX_wrS E]
  rfl


theorem bitInv_unsetI {h : Heap} {zs : Nat} {s : InflateState} {l : IL} {bs : List UInt8}
    (inv : BitInv (setI h zs s) l bs) : BitInv h l bs := by
  refine ⟨inv.have_eq, ?_, inv.hold_lt⟩
  rcases inv.next with empty | ⟨r, a, off, next, get, fits, view⟩
  · exact Or.inl empty
  · exact Or.inr ⟨r, a, off, next, by rw [byte_view_get_setI] at get; exact get, fits, view⟩

/-- The only stage a `LEN` or `LEN_` state can stand for. -/
theorem stage_of_len {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage)
    (mode : s.mode = LEN ∨ s.mode = LEN_) :
    ∃ header out final L D, stage = .body header ⟨out, final, .codes L D .none⟩ := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨lo, hi⟩ := stageFacts
    rcases mode with m | m <;> rw [m] at lo hi <;> exact absurd hi (by decide)
  · have := stageFacts
    simp only [LoopStageMatches] at this
    rcases mode with m | m <;> rw [m] at this <;> exact absurd this (by decide)
  · obtain ⟨body, _, _⟩ := stageFacts
    rcases pos with _ | _ | remaining | header' | ⟨L, D, pending⟩ | _
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m <;> rw [m] at m' <;> rcases m' with m' | m' <;> exact absurd m' (by decide)
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m <;> rw [m] at m' <;> rcases m' with m' | m' <;> exact absurd m' (by decide)
    · obtain ⟨dyn, _⟩ := body
      rcases dynamic_mode dyn with m' | m' | m' <;> rcases mode with m | m <;>
        (rw [m] at m'; exact absurd m' (by decide))
    · obtain ⟨_, _, _, rest⟩ := body
      rcases pending with _ | symbol | length | ⟨length, ds⟩ | ⟨remaining, dist⟩ | byte
      · exact ⟨header, out, final, L, D, rfl⟩
      all_goals (rcases mode with m | m <;> rw [m] at rest <;> exact absurd rest.1 (by decide))
    · obtain ⟨m', _⟩ := body
      rcases mode with m | m <;> rw [m] at m' <;> rcases m' with m' | m' <;> exact absurd m' (by decide)
  · obtain ⟨m', _⟩ := stageFacts
    rcases mode with m | m <;> rw [m] at m' <;> rcases m' with m' | m' <;> exact absurd m' (by decide)
  · have m' : s.mode = DONE := stageFacts
    rcases mode with m | m <;> rw [m] at m' <;> exact absurd m' (by decide)

section LenStep
open Zlib.Inftrees Zlib.Inftrees.Spec Zlib.Inftrees.Proofs
open Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open Zlib.Inftrees.Spec.DecodeTableInvariant Zlib.Inftrees.Spec.DecodeTableStability
open Zlib.Inflate.Proofs.MeaningLookup

set_option maxHeartbeats 16000000 in
/-- `case LEN` on the slow branch keeps the format meaning. It sets `back = 0`
and looks up the literal/length symbol in the root table and, through a link,
in a second-level table, pulling a byte only while the selected entry does not
fit the held bits. Without input it leaves (`have = 0`) at the token boundary,
and the held bits without their last byte hold no valid symbol. Otherwise the
symbol's code is dropped: a literal goes to `LIT`, the end of the block to
`TYPE` at the block boundary or after the final block with fewer than 8 held
bits, an invalid code to `BAD` with no valid continuation of the input, and a
length to `LENEXT` and on (`lenext_step`).

`slow` is the negation of the condition of the fast branch. The safety
invariant of the decoder state supplies `tables` (`DataTablesSafe`); the other
hypotheses are those of `match_step`. -/
theorem len_slow_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (lenMode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LEN ∨ s.mode = LEN_)
    (tables : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → DataTablesSafe h s)
    (bounds : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize)
    (sane : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.sane ≠ 0)
    (wsizeBits : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wsize ≠ 0 → s.wsize.toNat = 2 ^ s.wbits.toNat)
    (ring : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.whave < s.wsize → s.wnext = s.whave)
    (privateWindow : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      ∀ w o d i, s.window = .ref w o → l.put = .ref d i → w ≠ d)
    (rawWidth : f.wrap = .raw → f.configured ≠ 0) :
    ∃ result l' h', runX (inflate_LEN c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ l.left = 0) ∧ LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (LoopMatches c f h' l' ∨
          ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
            LoopDoomed f l')))) := by
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have mode := lenMode zs s st hs
  obtain ⟨header, out, final, L, D, rfl⟩ := stage_of_len stageM mode
  have pendBase := pendLe.2 _ _ rfl
  obtain ⟨⟨last, lenTable, distTable, modeNone, p7⟩, window, check⟩ := stageM
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  obtain ⟨extL, extD⟩ := deflateParsed_codes_ext deflate L D .none rfl
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
  subst heldEq
  have lenTable0 := lenTable
  obtain ⟨ref, offset, ca, used0, ptr, get, inv0, stable0⟩ := lenTable
  have inv : Inv LENS ca offset s.lenbits.toNat used0 L := inv0
  have stable : StableQuery LENS ca offset s.lenbits.toNat := stable0.1
  have ptr0 : s.lencode = .ref ref offset := ptr
  obtain ⟨ref', offset', ca', ptr', get', safe⟩ := (tables zs s st hs).lengthTable
  rw [ptr0] at ptr'
  obtain ⟨rfl, rfl⟩ := Ptr.ref.inj ptr'
  rw [get] at get'
  cases get'
  -- the state after `back = 0`
  have hs0 : (setI h zs { s with back := 0 }).istates zs = some { s with back := 0 } :=
    setI_istates_same _ _ _
  have E0 : Env c (setI h zs { s with back := 0 }) r zs z { s with back := 0 } :=
    ⟨strm, st, by simpa using hz, hs0⟩
  have get0 : Space.get (setI h zs { s with back := 0 }) ref = some ca := by
    rw [code_get_setI (s' := { s with back := 0 }) hs rfl]; exact get
  have ptrS : ({ s with back := 0 } : InflateState).lencode = .ref ref offset := ptr0
  have binv0 : BitInv (setI h zs { s with back := 0 }) l (f.inp.drop (loopRead l)) := bitInv_setI binv
  have runPre := (inflate_LEN_slow_cut (c := c) (l := l) (h := h) slow).trans (len_prefix E l)
  have backZero : ({ s with back := 0 } : InflateState).back = Int32.ofNat 0 := rfl
  have window' := fun (s' : InflateState) (l' : IL) (wnd : s'.window = s.window)
      (ws : s'.wsize = s.wsize) (wn : s'.wnext = s.wnext) (wh : s'.whave = s.whave) =>
    window_transfer (s := loopState s l) (s' := loopState s' l') wnd ws wn wh
      (fun q => byte_view_get_setI h zs s' q) window
  let Fail : Nat → Prop := fun k => ∀ sym rest,
    decodeSym L ((stream l (f.inp.drop (loopRead l))).take k) = some (sym, rest) → 285 < sym
  have entryShort : l.bits.toNat < 8 ∨ Fail (l.bits.toNat - 8) := by
    rcases p7 with lt | none
    · exact Or.inl lt
    · right
      intro sym rest dec
      apply none sym rest
      rw [heldShort_eq]
      show decodeSym L (natBits (l.bits.toNat - 8) l.hold.toNat) = _
      rw [short_take binv rfl _ (by omega)]
      exact dec
  have shortOf : ∀ (reg : IL) (u : Nat), reg.bits.toNat = l.bits.toNat + 8 * u →
      (∀ k, k < u → Fail (l.bits.toNat + 8 * k)) → reg.bits.toNat < 8 ∨ Fail (reg.bits.toNat - 8) := by
    intro reg u cnt fails
    cases u with
    | zero =>
      rw [cnt]
      simpa using entryShort
    | succ u =>
      right
      rw [show reg.bits.toNat - 8 = l.bits.toNat + 8 * u by omega]
      exact fails u (by omega)
  have sameS : ∀ (s2 : InflateState) zs' s', c.st = some (.tab zs') →
      (setI h zs s2).istates zs' = some s' → s' = s2 := by
    intro s2 zs' s' st' hs'
    rw [st] at st'
    cases st'
    rw [setI_istates_same] at hs'
    cases hs'
    rfl
  -- leaving for input
  have leaveLoop : ∀ (reg : IL) (u : Nat), u ≤ (f.inp.drop (loopRead l)).length →
      BitInv h reg ((f.inp.drop (loopRead l)).drop u) →
      stream reg ((f.inp.drop (loopRead l)).drop u) = stream l (f.inp.drop (loopRead l)) →
      RegsKeep l reg → reg.next = inputAdvance l.next u → reg.bits.toNat = l.bits.toNat + 8 * u →
      (∀ k, k < u → Fail (l.bits.toNat + 8 * k)) →
      LoopMatches c f (setI h zs { s with back := 0 }) reg := by
    intro reg u ule inv' same' keep next' cnt fails
    have haveOld := binv.have_eq
    have haveNew := inv'.have_eq
    simp only [List.length_drop, loopRead] at haveOld haveNew ule
    have readEq : loopRead reg = loopRead l + u := by simp only [loopRead, keep.1]; omega
    have usedE : reg.have_.toNat + u = l.have_.toNat := by omega
    have bitsR := bits_pull bitsEq readEq same'
    have binvR : BitInv h reg (f.inp.drop (loopRead reg)) := by
      rw [readEq, ← List.drop_drop]; exact inv'
    have p7' : reg.bits.toNat < 8 ∨ ∀ sym rest,
        decodeSym L (heldShort (loopState { s with back := 0 } reg)) = some (sym, rest) → 285 < sym := by
      rcases shortOf reg u cnt fails with lt | fl
      · exact Or.inl lt
      · right
        intro sym rest dec
        apply fl sym rest
        rw [heldShort_eq] at dec
        rw [← short_take inv' same' _ (by omega)]
        exact dec
    exact loop_move (s' := { s with back := 0 }) (l' := reg) (j := u)
      (pos := ⟨out, final, .codes L D .none⟩) st retOk
      ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, config.2.2.2.2.2⟩
      haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn keep usedE next' binvR
      (by rw [bitsR]; rfl)
      (HeldBits.of_natBits (s := loopState { s with back := 0 } reg) binvR.hold_lt) wrapHeader consumedEq
      deflate
      ⟨last, table_setI (s' := { s with back := 0 }) hs rfl lenTable0,
        table_setI (s' := { s with back := 0 }) hs rfl distTable, modeNone, p7'⟩
      (window' _ _ rfl rfl rfl rfl) check wrapM outputEq
  -- the common end: a fitted leaf, its code dropped
  have tail : ∀ (rF rD : IL) (uF cons bn : Nat) (e : Code),
      uF ≤ (f.inp.drop (loopRead l)).length →
      BitInv h rF ((f.inp.drop (loopRead l)).drop uF) →
      stream rF ((f.inp.drop (loopRead l)).drop uF) = stream l (f.inp.drop (loopRead l)) →
      RegsKeep l rF → RegsKeep rF rD → rD.have_ = rF.have_ → rD.next = inputAdvance l.next uF →
      rF.bits.toNat = l.bits.toNat + 8 * uF → (∀ k, k < uF → Fail (l.bits.toNat + 8 * k)) →
      tableRead LENS ca offset s.lenbits.toNat (DecodeShort.padded (natBits rF.bits.toNat rF.hold.toNat)) =
        some (e, cons) → cons ≤ rF.bits.toNat →
      BitInv h rD ((f.inp.drop (loopRead l)).drop uF) →
      natBits rF.bits.toNat rF.hold.toNat = natBits cons rF.hold.toNat ++ natBits rD.bits.toNat rD.hold.toNat →
      bn ≤ 15 →
      runX (inflate_LEN c) l h =
        runX (lenLeafTail c e) rD (setI h zs { s with back := Int32.ofNat bn, length := e.val.toUInt32 }) →
      ∃ result l' h', runX (inflate_LEN c) l h = .ok ((result, l'), h') ∧
        ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ l.left = 0) ∧ LoopMatches c f h' l') ∨
         (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
           (LoopMatches c f h' l' ∨
            ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
              LoopDoomed f l')))) := by
    intro rF rD uF cons bn e ule invF sameF keepF keepD haveD nextD cntF failsF query fit invD split bnle run
    have haveOld := binv.have_eq
    have haveNew := invF.have_eq
    simp only [List.length_drop, loopRead] at haveOld haveNew ule
    have readF : loopRead rF = loopRead l + uF := by simp only [loopRead, keepF.1]; omega
    have readD : loopRead rD = loopRead l + uF := by
      simp only [loopRead, keepD.1, haveD]; exact readF
    have bitsF := bits_pull bitsEq readF sameF
    have bitsD : bytesToBits (f.logIn ++ f.inp.take (loopRead rD)) =
        (consumed ++ natBits cons rF.hold.toNat) ++ natBits rD.bits.toNat rD.hold.toNat := by
      rw [readD, ← readF, bitsF, split, List.append_assoc]
    have consumedD : consumed ++ natBits cons rF.hold.toNat =
        bytesToBits header ++ (bitsP ++ natBits cons rF.hold.toNat) := by
      rw [consumedEq, List.append_assoc]
    have fitted := fitted_leaf_meaning inv stable query (by rw [natBits_length]; exact fit)
    let sB : InflateState := { s with back := Int32.ofNat bn, length := e.val.toUInt32 }
    have EB : Env c (setI h zs sB) r zs z sB := ⟨strm, st, by simpa using hz, by simp⟩
    have binvD : BitInv h rD (f.inp.drop (loopRead rD)) := by
      rw [readD, ← List.drop_drop]; exact invD
    have keepT := keepF.trans keepD
    have lenD : rD.bits.toNat = rF.bits.toNat - cons := by
      have := congrArg List.length split
      simp only [List.length_append, natBits_length] at this
      omega
    -- an accepted leaf: its symbol, its code, and fewer than 8 bits left
    have accepted : LeafAccepted LENS e → ∃ sym, sym ≤ 285 ∧ SymbolEntry LENS sym e ∧
        decodeSym L (natBits cons rF.hold.toNat) = some (sym, []) ∧ rD.bits.toNat < 8 := by
      intro acc
      obtain ⟨sym, valid, meaning, cEq, decAll⟩ := fitted.1 acc
      have valid' : sym ≤ 285 := lensValid.mp valid
      have dec0 : decodeSym L (natBits rF.bits.toNat rF.hold.toNat) =
          some (sym, (natBits rF.bits.toNat rF.hold.toNat).drop cons) := by
        simpa using decAll []
      have decX : decodeSym L (natBits cons rF.hold.toNat) = some (sym, []) := by
        have := decode_take extL dec0 (k := cons) (by omega)
        rw [natBits_take _ _ _ fit, ← cEq] at this
        rw [this, List.drop_eq_nil_of_le (by rw [natBits_length]; exact Nat.le_refl _)]
      have shortF : (natBits rF.bits.toNat rF.hold.toNat).length < 8 ∨ ∀ s' r',
          decodeSym L ((natBits rF.bits.toNat rF.hold.toNat).take
            ((natBits rF.bits.toNat rF.hold.toNat).length - 8)) = some (s', r') → 285 < s' := by
        rw [natBits_length]
        rcases shortOf rF uF cntF failsF with lt | fl
        · exact Or.inl lt
        · right
          intro s' r' dec
          rw [natBits_take _ _ _ (by omega), short_take invF sameF _ (by omega)] at dec
          exact fl s' r' dec
      have leftLt := left_short_len extL dec0 valid' shortF
      rw [natBits_length, ← cEq] at leftLt
      exact ⟨sym, valid', meaning, decX, by omega⟩
    have stepTo : ∀ (s2 : InflateState) (pos : DeflatePos) (tbits : List Bool),
        s2.window = s.window → s2.wsize = s.wsize → s2.wnext = s.wnext → s2.whave = s.whave →
        ConfigMatches (loopState s2 rD) f.wrap f.configured →
        DeflateParsed bodyDict (bitsP ++ tbits) pos → tbits = natBits cons rF.hold.toNat →
        BodyMatches (setI h zs s2) (loopState s2 rD) pos → pos.out = f.logOut ++ callOut →
        CheckMeaning (loopState s2 rD) f.wrap header
          ((f.logOut ++ callOut).take ((f.logOut ++ callOut).length - loopPending l)) →
        (FlagsMatch (loopState s2 rD) f.wrap header ∧ HeaderWidth (loopState s2 rD) f.configured header ∧
          (f.dict = [] ∨ f.wrap = .raw ∨ header.length = 6)) →
        LoopMatches c f (setI h zs s2) rD := by
      intro s2 pos tbits wnd ws wn wh cfg parsed2 tEq body outEq2 chk wm
      subst tEq
      exact loop_move (s' := s2) (l' := rD) (j := uF) (pos := pos) st retOk cfg
        haveLe inLen leftLe pendBase putEq outBytes writable sepIn (by rw [wnd, ws]; exact sepWin) sepOutIn keepT
        (by rw [haveD]; omega) nextD binvD (by rw [bitsD, consumedD]; rfl)
        (HeldBits.of_natBits (s := loopState s2 rD) binvD.hold_lt) wrapHeader rfl parsed2 body
        (window' _ _ wnd ws wn wh) chk wm outEq2
    by_cases z0 : e.op = 0
    · -- a literal
      obtain ⟨sym, valid, meaning, decX, bitsLt⟩ := accepted (lensAccepted.mpr (Or.inr (by rw [z0]; rfl)))
      rcases lensEntry valid meaning with ⟨lt, _, valEq⟩ | ⟨_, op96⟩ | ⟨_, opEq, _⟩
      · have runL := run.trans (lenTail_lit EB e rD z0)
        rw [setI_setI] at runL
        refine ⟨_, _, _, runL, Or.inr ⟨rfl, by rw [readD]; omega, Or.inl ?_⟩⟩
        refine stepTo { sB with mode := LIT } ⟨out, final, .codes L D (.literal sym.toUInt8)⟩ _
          rfl rfl rfl rfl
          ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show LIT ≠ SYNC by decide⟩
          (DeflateParsed.partialLiteral deflate (Token.Step.literal decX lt)) rfl
          ⟨last, table_setI (s' := { sB with mode := LIT }) hs rfl lenTable0,
            table_setI (s' := { sB with mode := LIT }) hs rfl distTable, rfl, ?_, bitsLt⟩ outputEq check wrapM
        show e.val.toUInt32.toNat = (sym.toUInt8).toNat
        rw [UInt16.toNat_toUInt32, valEq, Nat.toUInt8, UInt8.toNat_ofNat']
        exact (Nat.mod_eq_of_lt (by omega)).symm
      · exact absurd (op96.symm.trans z0) (by decide)
      · have : e.op.toNat = 0 := by rw [z0]; rfl
        omega
    by_cases e32 : e.op &&& 32 ≠ 0
    · -- the end of the block
      obtain ⟨sym, valid, meaning, decX, bitsLt⟩ := accepted (lensAccepted.mpr (Or.inl (by simpa using e32)))
      have sym256 : sym = 256 := by
        rcases lensEntry valid meaning with ⟨_, opz, _⟩ | ⟨eq, _⟩ | ⟨ge, opEq, _⟩
        · exact absurd (by rw [opz]; rfl) e32
        · exact eq
        · exfalso
          apply e32
          rw [u8_and_zero, opEq]
          exact (length_op_bits _ (lengthExtras_le' _ (by omega))).1
      subst sym256
      have runE := run.trans (lenTail_eob EB e rD z0 e32)
      rw [setI_setI] at runE
      refine ⟨_, _, _, runE, Or.inr ⟨rfl, by rw [readD]; omega, Or.inl ?_⟩⟩
      cases final with
      | false =>
        exact stepTo { sB with back := -1, mode := TYPE } ⟨out, false, .boundary⟩ _ rfl rfl rfl rfl
          ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show TYPE ≠ SYNC by decide⟩
          (DeflateParsed.endOfBlock deflate (Token.Step.eob decX)) rfl
          ⟨Or.inl rfl, rfl, last, bitsLt⟩ outputEq check wrapM
      | true =>
        exact stepTo { sB with back := -1, mode := TYPE } ⟨out, true, .finished⟩ _ rfl rfl rfl rfl
          ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show TYPE ≠ SYNC by decide⟩
          (DeflateParsed.endOfFinal deflate (Token.Step.eob decX)) rfl
          ⟨Or.inl rfl, rfl, last, bitsLt⟩ outputEq check wrapM
    have no32 : e.op &&& 32 = 0 := by simpa using e32
    by_cases e64 : e.op &&& 64 ≠ 0
    · -- an invalid code: `BAD`
      obtain ⟨i, runB⟩ := lenTail_bad EB e rD z0 no32 e64
      refine ⟨.ok (), rD, _, run.trans runB, Or.inr ⟨rfl, by rw [readD]; omega, Or.inr ⟨?_, ?_⟩⟩⟩
      · intro zs' s' st' hs'
        rw [st] at st'
        cases st'
        simp only [badHeap, setI_istates_same, Option.some.injEq] at hs'
        rw [← hs']
      · have notAcc : ¬ LeafAccepted LENS e := by
          intro acc
          rcases lensAccepted.mp acc with a | a
          · simp [no32] at a
          · exact e64 a
        apply doomed_of_aligned (rest := natBits rF.bits.toNat rF.hold.toNat) wrapHeader deflate
        · rw [show loopRead rD = loopRead rF by rw [readD, readF], bitsF, consumedEq]
        · intro more tail outF _ resid
          obtain ⟨_, _, r', h'', symbols, _⟩ := resid
          have rej : Token.Rejected L D bodyDict out (natBits rF.bits.toNat rF.hold.toNat ++ more) := by
            refine .length ?_
            intro more' found
            obtain ⟨sym, rest, dec, le⟩ := found
            exact fitted.2 notAcc (more ++ more')
              ⟨sym, rest, by simpa only [List.append_assoc] using dec, lensValid.mpr le⟩
          exact ZlibF.Spec.Token.rejected_has_no_symbols _ _ _ _ _ rej r' h'' symbols
    have no64 : e.op &&& 64 = 0 := by simpa using e64
    -- a length: `LENEXT`
    obtain ⟨sym, valid, meaning, decX, bitsLt⟩ := accepted (lensAccepted.mpr (Or.inr no64))
    rcases lensEntry valid meaning with ⟨_, opz, _⟩ | ⟨_, op96⟩ | ⟨ge, opEq, valEq⟩
    · exact absurd opz z0
    · exfalso
      apply e32
      rw [op96]
      decide
    have xle := lengthExtras_le' (sym - 257) (by omega)
    have extraNat : (e.op.toUInt32 &&& 15).toNat = lengthExtras.getD (sym - 257) 0 := by
      rw [op_and_mask, opEq]
      exact (length_op_bits _ xle).2.2
    have ppX : PendingParsed L D (natBits cons rF.hold.toNat) (.lengthExtra sym) := ⟨ge, valid, decX⟩
    have runX' := run.trans (lenTail_length EB e rD z0 no32 no64)
    rw [setI_setI] at runX'
    have loop3 := stepTo (lenState sB e) ⟨out, final, .codes L D (.lengthExtra sym)⟩ _ rfl rfl rfl rfl
      ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show LENEXT ≠ SYNC by decide⟩
      (DeflateParsed.partialToken _ deflate ppX) rfl
      ⟨last, table_setI (s' := lenState sB e) hs rfl lenTable0,
        table_setI (s' := lenState sB e) hs rfl distTable, rfl, extraNat,
        by show e.val.toUInt32.toNat = _; rw [UInt16.toNat_toUInt32, valEq],
        by show rD.bits.toNat < 8 + (e.op.toUInt32 &&& 15).toNat; omega⟩ outputEq check wrapM
    obtain ⟨result, l', h', runT, rest⟩ := lenext_step loop3 strm
      (by rw [ZStreamRef.get_setI]; exact hz)
      (fun zs' s' st' hs' => by rw [sameS _ zs' s' st' hs']; rfl)
      (fun zs' s' st' hs' => by
        rw [sameS _ zs' s' st' hs']; exact (tables zs s st hs).decode_update hs rfl)
      (fun zs' s' st' hs' => by rw [sameS _ zs' s' st' hs']; exact ⟨bn, bnle, rfl⟩)
      (fun zs' s' st' hs' => by rw [sameS _ zs' s' st' hs']; exact bounds zs s st hs)
      (fun zs' s' st' hs' => by rw [sameS _ zs' s' st' hs']; exact sane zs s st hs)
      (fun zs' s' st' hs' => by rw [sameS _ zs' s' st' hs']; exact wsizeBits zs s st hs)
      (fun zs' s' st' hs' => by rw [sameS _ zs' s' st' hs']; exact ring zs s st hs)
      (fun zs' s' st' hs' w o d i hw hp => by
        rw [sameS _ zs' s' st' hs'] at hw
        rw [keepT.2.2.2.1] at hp
        exact privateWindow zs s st hs w o d i hw hp)
      rawWidth
    refine ⟨result, l', h', runX'.trans runT, ?_⟩
    rcases rest with ⟨leave, cause, m⟩ | ⟨ok, more, m⟩
    · exact Or.inl ⟨leave, cause.imp id (fun e => keepT.2.2.1.symm.trans e), m⟩
    · exact Or.inr ⟨ok, by rw [readD] at more; omega, m⟩
  -- the root lookup
  have fail1 : ∀ current used, LookupRegShape l current →
      BitInv (setI h zs { s with back := 0 }) current ((f.inp.drop (loopRead l)).drop used) →
      stream current ((f.inp.drop (loopRead l)).drop used) = stream l (f.inp.drop (loopRead l)) →
      current.bits.toNat = l.bits.toNat + 8 * used →
      current.bits.toNat < (codeLookupValue ca offset s.lenbits.toNat current).bits.toNat →
      Fail current.bits.toNat := by
    intro cur u _ inv' same' _ nofit sym rest dec
    rw [← held_take inv' same'] at dec
    have q := len_query inv safe (bits := cur.bits.toNat) (hold := cur.hold.toNat) inv'.hold_lt
    have nofit' : cur.bits.toNat < (ca.getD (offset + cur.hold.toNat % 2 ^ s.lenbits.toNat) default).bits.toNat :=
      nofit
    by_cases sl : SlowLenLink (ca.getD (offset + cur.hold.toNat % 2 ^ s.lenbits.toNat) default)
    · obtain ⟨_, _, query⟩ := q.2 sl
      exact nofit_invalid_len inv query
        (by rw [natBits_length]; exact Nat.lt_of_lt_of_le nofit' (Nat.le_add_right _ _)) sym rest dec
    · obtain ⟨_, query⟩ := q.1 sl
      exact nofit_invalid_len inv query (by rw [natBits_length]; exact nofit') sym rest dec
  obtain ⟨res1, r1, u1, run1, u1le, inv1, same1, shape1, count1, sel1, kinds1, ok1, leave1, cur1,
    fails1⟩ := lookup1_len_fail st hs0 ptrS get0 safe binv0 Fail fail1
  have inv1h : BitInv h r1 ((f.inp.drop (loopRead l)).drop u1) := bitInv_unsetI inv1
  have keep1 := keep_of_lookup shape1
  by_cases isLeave : res1 = .error Ex.leave
  · subst isLeave
    exact ⟨_, _, _, runPre.trans (len_run_leave run1), Or.inl ⟨rfl, Or.inl (leave1 rfl).1,
      leaveLoop r1 u1 u1le inv1h same1 keep1 cur1 count1 fails1⟩⟩
  have isOk : res1 = .ok () := kinds1.resolve_right isLeave
  subst isOk
  have fit1 := ok1 rfl
  have hereEq : r1.here = ca.getD (offset + r1.hold.toNat % 2 ^ s.lenbits.toNat) default := sel1
  have q1 := len_query inv safe (bits := r1.bits.toNat) (hold := r1.hold.toNat) inv1.hold_lt
  rw [← hereEq] at q1
  have haveOld := binv.have_eq
  have have1 := inv1.have_eq
  simp only [List.length_drop, loopRead] at haveOld have1 u1le
  by_cases sl : SlowLenLink r1.here
  · -- a link: the second-level lookup
    obtain ⟨rootBits, link0, _⟩ := q1.2 sl
    have B1 : BitInv (setI h zs { s with back := 0 }) { r1 with last := r1.here }
        ((f.inp.drop (loopRead l)).drop u1) := ⟨inv1.have_eq, inv1.next, inv1.hold_lt⟩
    have idxAt : ∀ (cur : IL) (bs' : List UInt8), BitInv (setI h zs { s with back := 0 }) cur bs' →
        stream cur bs' = stream l (f.inp.drop (loopRead l)) → r1.bits.toNat ≤ cur.bits.toNat →
        cur.hold.toNat % 2 ^ s.lenbits.toNat = r1.hold.toNat % 2 ^ s.lenbits.toNat := by
      intro cur bs' inv' same' le
      have a := short_take inv' same' s.lenbits.toNat (by omega)
      have b := short_take inv1 same1 s.lenbits.toNat (by omega)
      have := congrArg MeaningBits.heldValue (a.trans b.symm)
      rw [MeaningBits.heldValue_natBits, MeaningBits.heldValue_natBits] at this
      exact this
    have fail2 : ∀ current used, LookupRegShape { r1 with last := r1.here } current →
        BitInv (setI h zs { s with back := 0 }) current (((f.inp.drop (loopRead l)).drop u1).drop used) →
        stream current (((f.inp.drop (loopRead l)).drop u1).drop used) =
          stream { r1 with last := r1.here } ((f.inp.drop (loopRead l)).drop u1) →
        current.bits.toNat = ({ r1 with last := r1.here } : IL).bits.toNat + 8 * used →
        current.bits.toNat < r1.here.bits.toNat + (subLookupValue ca offset r1.here current).bits.toNat →
        Fail current.bits.toNat := by
      intro cur u _ inv' same' cnt nofit sym rest dec
      have same'' : stream cur (((f.inp.drop (loopRead l)).drop u1).drop u) =
          stream l (f.inp.drop (loopRead l)) := same'.trans same1
      rw [← held_take inv' same''] at dec
      have q := len_query inv safe (bits := cur.bits.toNat) (hold := cur.hold.toNat) inv'.hold_lt
      rw [idxAt cur _ inv' same'' (by change cur.bits.toNat = r1.bits.toNat + 8 * u at cnt; omega),
        ← hereEq] at q
      obtain ⟨_, _, query⟩ := q.2 sl
      exact nofit_invalid_len inv query (by rw [natBits_length]; exact nofit) sym rest dec
    obtain ⟨res2, r2, u2, run2, u2le, inv2, same2, shape2, count2, sel2, leaf2, kinds2, ok2, leave2,
      cur2, fails2⟩ := lookup2_len_fail r1.here st hs0 ptrS get0 rfl link0 B1 Fail fail2
    have keep2 : RegsKeep l r2 :=
      keep1.trans ((show RegsKeep r1 { r1 with last := r1.here } from ⟨rfl, rfl, rfl, rfl, rfl⟩).trans
        (keep_of_lookup shape2))
    have dropEq : ((f.inp.drop (loopRead l)).drop u1).drop u2 = (f.inp.drop (loopRead l)).drop (u1 + u2) :=
      List.drop_drop
    rw [dropEq] at inv2 same2
    have same2' : stream r2 ((f.inp.drop (loopRead l)).drop (u1 + u2)) = stream l (f.inp.drop (loopRead l)) :=
      same2.trans same1
    have inv2h : BitInv h r2 ((f.inp.drop (loopRead l)).drop (u1 + u2)) := bitInv_unsetI inv2
    have u2le' : u2 ≤ ((f.inp.drop (loopRead l)).drop u1).length := u2le
    simp only [List.length_drop, loopRead] at u2le'
    have next2 : r2.next = inputAdvance l.next (u1 + u2) := by
      rw [cur2, show ({ r1 with last := r1.here } : IL).next = r1.next from rfl, cur1, inputAdvance_add]
    have count2' : r2.bits.toNat = l.bits.toNat + 8 * (u1 + u2) := by
      change r2.bits.toNat = r1.bits.toNat + 8 * u2 at count2
      omega
    have failsT : ∀ k, k < u1 + u2 → Fail (l.bits.toNat + 8 * k) := by
      intro k lt
      by_cases first : k < u1
      · exact fails1 k first
      · have := fails2 (k - u1) (by omega)
        change Fail (r1.bits.toNat + 8 * (k - u1)) at this
        rw [show r1.bits.toNat + 8 * (k - u1) = l.bits.toNat + 8 * k by omega] at this
        exact this
    by_cases isLeave2 : res2 = .error Ex.leave
    · subst isLeave2
      exact ⟨_, _, _, runPre.trans (len_run_sub_leave run1 sl run2), Or.inl ⟨rfl, Or.inl (leave2 rfl).1,
        leaveLoop r2 (u1 + u2) (by simp only [List.length_drop, loopRead]; omega) inv2h same2' keep2
          next2 count2' failsT⟩⟩
    have isOk2 : res2 = .ok () := kinds2.resolve_right isLeave2
    subst isOk2
    have fit2 := ok2 rfl
    have lastEq : r2.last = r1.here := by rw [shape2]
    have leafBits := leaf2.1
    have rootSmall : r1.here.bits.toNat ≤ 15 := link0.1
    have runS := len_run_sub_ok E0 0 run1 sl run2 lastEq backZero rootSmall (by omega)
    have small1 : r1.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; omega
    obtain ⟨inv3, stream3, count3⟩ := DROPBITS_inv inv2h r1.here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32]; omega) small1
    let r3 : IL :=
      { r2 with hold := r2.hold >>> r1.here.bits.toUInt32.toUInt64, bits := r2.bits - r1.here.bits.toUInt32 }
    have count3' : r3.bits.toNat = r2.bits.toNat - r1.here.bits.toNat := by
      rw [UInt8.toNat_toUInt32] at count3; exact count3
    have small2 : r3.here.bits.toUInt32.toNat < 64 := by
      rw [UInt8.toNat_toUInt32]; show r2.here.bits.toNat < 64; omega
    obtain ⟨inv4, stream4, count4⟩ := DROPBITS_inv inv3 r3.here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32, count3']; show r2.here.bits.toNat ≤ _; omega) small2
    let r4 : IL :=
      { r3 with hold := r3.hold >>> r3.here.bits.toUInt32.toUInt64, bits := r3.bits - r3.here.bits.toUInt32 }
    have held3 := held_drop stream3 (by rw [UInt8.toNat_toUInt32]; omega)
    have held4 := held_drop stream4 (by rw [UInt8.toNat_toUInt32, count3']; show r2.here.bits.toNat ≤ _; omega)
    have split : natBits r2.bits.toNat r2.hold.toNat =
        natBits (r1.here.bits.toNat + r2.here.bits.toNat) r2.hold.toNat ++
          natBits r4.bits.toNat r4.hold.toNat := by
      have e4 : natBits r4.bits.toNat r4.hold.toNat =
          (natBits r2.bits.toNat r2.hold.toNat).drop (r1.here.bits.toNat + r2.here.bits.toNat) := by
        change natBits r4.bits.toNat r4.hold.toNat = _ at held4
        rw [held4]
        change (natBits r3.bits.toNat r3.hold.toNat).drop r3.here.bits.toUInt32.toNat = _
        change natBits r3.bits.toNat r3.hold.toNat = _ at held3
        rw [held3, List.drop_drop, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32]
      rw [e4, ← natBits_take r2.bits.toNat r2.hold.toNat _ fit2, List.take_append_drop]
    have q2 := len_query inv safe (bits := r2.bits.toNat) (hold := r2.hold.toNat) inv2.hold_lt
    rw [idxAt r2 _ inv2 same2' (by omega), ← hereEq] at q2
    obtain ⟨_, _, query2⟩ := q2.2 sl
    have hereEq2 : r2.here = ca.getD (offset + r1.here.val.toNat +
        subLookupIndexNat r1.here r2.hold.toNat) default := sel2
    rw [← hereEq2] at query2
    have E1 : Env c (setI (setI h zs { s with back := 0 }) zs
          { ({ s with back := 0 } : InflateState) with back := Int32.ofNat (0 + r1.here.bits.toNat) }) r zs z
        { ({ s with back := 0 } : InflateState) with back := Int32.ofNat (0 + r1.here.bits.toNat) } :=
      ⟨strm, st, by simpa using hz, by simp⟩
    have runF := len_run_finish E1 r3 (0 + r1.here.bits.toNat) rfl
      (by show r2.here.bits.toNat ≤ 15; omega) (by omega)
    rw [setI_setI, setI_setI] at runF
    rw [setI_setI] at runS
    exact tail r2 r4 (u1 + u2) (r1.here.bits.toNat + r2.here.bits.toNat)
      (0 + r1.here.bits.toNat + r3.here.bits.toNat) r2.here
      (by simp only [List.length_drop, loopRead]; omega) inv2h same2' keep2 ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
      next2 count2' failsT query2 fit2 inv4 split
      (by show 0 + r1.here.bits.toNat + r2.here.bits.toNat ≤ 15; omega)
      (runPre.trans (runS.trans runF))
  · -- a root leaf
    obtain ⟨leaf0, query1⟩ := q1.1 sl
    have small : r1.here.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; have := leaf0.1; omega
    obtain ⟨invD, streamD, countD⟩ := DROPBITS_inv inv1h r1.here.bits.toUInt32
      (by rw [UInt8.toNat_toUInt32]; exact fit1) small
    have heldD := held_drop streamD (by rw [UInt8.toNat_toUInt32]; exact fit1)
    have split : natBits r1.bits.toNat r1.hold.toNat =
        natBits r1.here.bits.toNat r1.hold.toNat ++
          natBits (r1.bits - r1.here.bits.toUInt32).toNat
            (r1.hold >>> r1.here.bits.toUInt32.toUInt64).toNat := by
      rw [heldD, UInt8.toNat_toUInt32, ← natBits_take r1.bits.toNat r1.hold.toNat _ fit1,
        List.take_append_drop]
    have runF := (len_run_leaf run1 sl).trans
      (len_run_finish E0 r1 0 backZero (by have := leaf0.1; omega) (by omega))
    rw [setI_setI] at runF
    exact tail r1
      { r1 with hold := r1.hold >>> r1.here.bits.toUInt32.toUInt64, bits := r1.bits - r1.here.bits.toUInt32 }
      u1 r1.here.bits.toNat (0 + r1.here.bits.toNat) r1.here
      (by simp only [List.length_drop, loopRead]; omega) inv1h same1 keep1 ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl cur1
      count1 fails1 query1 fit1 invD split (by have := leaf0.1; omega) (runPre.trans runF)

#print axioms len_slow_step

end LenStep


theorem len__run {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState} (E : Env c h r zs z s) (l : IL) :
    runX (inflate_LEN_ c) l h = runX (inflate_LEN c) l (setI h zs { s with mode := LEN }) := by
  unfold inflate_LEN_
  rw [runX_bind, runX_setMode E]

/-- `case LEN_` on the slow branch keeps the format meaning: it sets the mode
`LEN` and runs `case LEN` (`len_slow_step`), with the same hypotheses. -/
theorem len__step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} {r : ZStreamRef} {z : ZStream}
    (loop : LoopMatches c f h l) (strm : c.strm = some r) (hz : r.get h = some z)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true)
    (lenMode : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.mode = LEN_)
    (tables : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → DataTablesSafe h s)
    (bounds : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wnext ≤ s.whave ∧ s.whave ≤ s.wsize)
    (sane : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s → s.sane ≠ 0)
    (wsizeBits : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.wsize ≠ 0 → s.wsize.toNat = 2 ^ s.wbits.toNat)
    (ring : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      s.whave < s.wsize → s.wnext = s.whave)
    (privateWindow : ∀ zs s, c.st = some (.tab zs) → h.istates zs = some s →
      ∀ w o d i, s.window = .ref w o → l.put = .ref d i → w ≠ d)
    (rawWidth : f.wrap = .raw → f.configured ≠ 0) :
    ∃ result l' h', runX (inflate_LEN_ c) l h = .ok ((result, l'), h') ∧
      ((result = .error Ex.leave ∧ (l'.have_ = 0 ∨ l.left = 0) ∧ LoopMatches c f h' l') ∨
       (result = .ok () ∧ loopRead l ≤ loopRead l' ∧
         (LoopMatches c f h' l' ∨
          ((∀ zs s, c.st = some (.tab zs) → h'.istates zs = some s → s.mode = BAD) ∧
            LoopDoomed f l')))) := by
  have loop0 := loop
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, config, haveLe, inLen, binv, leftLe,
    pendLe, putEq, outBytes, writable, sepIn, sepWin, sepOutIn, bitsEq, heldBits, parsed, stageM,
    wrapM, outputEq⟩ := loop
  have E : Env c h r zs z s := ⟨strm, st, hz, hs⟩
  have mode := lenMode zs s st hs
  obtain ⟨header, out, final, L, D, rfl⟩ := stage_of_len stageM (Or.inr mode)
  have pendBase := pendLe.2 _ _ rfl
  obtain ⟨⟨last, lenTable, distTable, _, p7⟩, window, check⟩ := stageM
  obtain ⟨bodyDict, bitsP, wrapHeader, consumedEq, deflate⟩ := parsed
  have heldEq : held = natBits l.bits.toNat l.hold.toNat := HeldBits.eq_natBits heldBits
  subst heldEq
  have loop1 := loop_move (s' := { s with mode := LEN }) (l' := l) (j := 0)
    (pos := ⟨out, final, .codes L D .none⟩) st retOk
    ⟨config.1, config.2.1, config.2.2.1, config.2.2.2.1, config.2.2.2.2.1, show LEN ≠ SYNC by decide⟩
    haveLe inLen leftLe pendBase putEq outBytes writable sepIn sepWin sepOutIn
    ⟨rfl, rfl, rfl, rfl, rfl⟩ (by omega) (inputAdvance_zero l.next).symm binv bitsEq
    (HeldBits.of_natBits (s := loopState { s with mode := LEN } l) binv.hold_lt) wrapHeader consumedEq
    deflate
    ⟨last, table_setI (s' := { s with mode := LEN }) hs rfl lenTable,
      table_setI (s' := { s with mode := LEN }) hs rfl distTable, Or.inr rfl, p7⟩
    (window_transfer (s := loopState s l) (s' := loopState { s with mode := LEN } l) rfl rfl rfl rfl
      (fun q => byte_view_get_setI h zs _ q) window) check wrapM outputEq
  have same : ∀ zs' s', c.st = some (.tab zs') →
      (setI h zs { s with mode := LEN }).istates zs' = some s' → s' = { s with mode := LEN } := by
    intro zs' s' st' hs'
    rw [st] at st'
    cases st'
    rw [setI_istates_same] at hs'
    cases hs'
    rfl
  obtain ⟨result, l', h', run, rest⟩ := len_slow_step loop1 strm (by rw [ZStreamRef.get_setI]; exact hz)
    slow
    (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact Or.inl rfl)
    (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact (tables zs s st hs).decode_update hs rfl)
    (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact bounds zs s st hs)
    (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact sane zs s st hs)
    (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact wsizeBits zs s st hs)
    (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact ring zs s st hs)
    (fun zs' s' st' hs' => by rw [same zs' s' st' hs']; exact privateWindow zs s st hs)
    rawWidth
  exact ⟨result, l', h', (len__run E l).trans run, rest⟩

#print axioms len__step

end Zlib.Inflate.Proofs.MeaningLength
