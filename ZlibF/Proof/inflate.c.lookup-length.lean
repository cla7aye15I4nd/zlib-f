import ZlibF.Proof.«inflate.c.lookup-subtable»
import ZlibF.Proof.«inflate.c.main.common»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inffast.Spec
set_option autoImplicit false

/-- The link test made by the slow literal/length decoder. -/
def SlowLenLink (entry : Code) : Prop := entry.op ≠ 0 ∧ entry.op &&& 240 = 0
instance (entry : Code) : Decidable (SlowLenLink entry) := inferInstanceAs (Decidable (entry.op ≠ 0 ∧ entry.op &&& 240 = 0))

theorem slowLenLink_fast {entry : Code} (slow : SlowLenLink entry) : LenLink entry := by
  obtain ⟨flag16, flag64⟩ := ZlibF.Math.InflateLookup.high_zero_flags entry.op slow.2
  exact ⟨slow.1, flag16, flag64⟩

theorem lenLink_slow {entry : Code} {ca : Array Code} {offset : Nat}
    (link : LenLink entry) (safe : LinkOK LenLeaf ca offset entry) : SlowLenLink entry :=
  ⟨link.1, ZlibF.Math.InflateLookup.small_high_zero entry.op safe.2.2.1⟩

/-- Only the selected entry, remembered root and input-bit registers change. -/
def SymbolRegShape (before after : IL) : Prop :=
  after = { before with next := after.next, have_ := after.have_, hold := after.hold, bits := after.bits, here := after.here, last := after.last }

theorem LookupRegShape.symbol {before after : IL} (shape : LookupRegShape before after) :
    SymbolRegShape before after := by
  unfold LookupRegShape at shape
  unfold SymbolRegShape
  rw [shape]

theorem SymbolRegShape.trans {a b c : IL} (first : SymbolRegShape a b) (second : SymbolRegShape b c) :
    SymbolRegShape a c := by
  unfold SymbolRegShape at *
  rw [second, first]

/-- The actual slow length-link block, including its checked signed counter update. -/
def lenSubLookup (c : Ctx) (root : Code) : X Unit := do
  modify fun l => { l with last := root }
  lookup2 c false
  let last := (← get).last
  DROPBITS last.bits.toUInt32
  let s ← ldInflateState c.st
  let bk ← chkI32 (s.back.toInt + last.bits.toNat)
  wrS c.st fun s => { s with back := bk }

/-- Actual second-level length lookup plus the root-bit consumption. Every
successful result is a proved leaf, with enough held bits to consume it.
Input exhaustion occurs before the state or bit buffer is committed. -/
theorem lenSubLookup_run_cursor {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (root : Code) (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (link : LinkOK LenLeaf ca offset root) (back : s.back = 0) (B : BitInv h l bs) :
    ∃ result regs used after,
      runX (lenSubLookup c root) l h = .ok ((result, regs), after) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.last = root ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () →
        after = setI h zs { s with back := Int32.ofNat root.bits.toNat } ∧
        LenLeaf root.bits.toNat regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop root.bits.toNat ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - root.bits.toNat) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) ∧ regs.next = inputAdvance l.next used := by
  let start := { l with last := root }
  have startInv : BitInv h start bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  obtain ⟨result, current, used, run, usedTwo, usedBound, currentInv, sameStream, shape, count,
    bitBound, _, leaf, totalBound, kinds, enough, empty, cursor⟩ :=
    lookup2_data_run_cursor false root hc hs pointer tableGet (l := start) rfl link
      (fun _ leaf => leaf.1) startInv
  have lastEq : current.last = root := by rw [shape]
  have symbolShape : SymbolRegShape l current :=
    SymbolRegShape.trans (b := start) (by rfl) shape.symbol
  -- Input exhaustion must be returned before the continuation is entered.
  cases result with
  | error e =>
    have equal : e = Ex.leave := by rcases kinds with impossible | equal; cases impossible; exact Except.error.inj equal
    subst e
    refine ⟨.error Ex.leave, current, used, h, ?_, usedTwo, usedBound, currentInv,
      symbolShape, lastEq, bitBound, Or.inr rfl, ?_, ?_, cursor⟩
    · unfold lenSubLookup
      rw [runX_bind, runX_modify]
      simp only []
      rw [runX_bind, run]
    · intro impossible
      cases impossible
    · intro _
      exact ⟨rfl, empty rfl, sameStream⟩
  | ok unit =>
    cases unit
    have source : runX (lenSubLookup c root) l h =
        runX (do
          let last := (← get).last
          DROPBITS last.bits.toUInt32
          let s ← ldInflateState c.st
          let bk ← chkI32 (s.back.toInt + last.bits.toNat)
          wrS c.st fun s => { s with back := bk }) current h := by
      unfold lenSubLookup
      rw [runX_bind, runX_modify]
      simp only []
      rw [runX_bind, run]
    have totalEnough := enough rfl
    have rootEnough : root.bits.toNat ≤ current.bits.toNat := by omega
    have rootSmall : root.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; have := link.1; omega
    obtain ⟨finalInv, finalStream, finalCount⟩ :=
      DROPBITS_inv currentInv root.bits.toUInt32 (by simpa using rootEnough) rootSmall
    let final := { current with hold := current.hold >>> root.bits.toUInt32.toUInt64, bits := current.bits - root.bits.toUInt32 }
    let after := setI h zs { s with back := Int32.ofNat root.bits.toNat }
    have checked : chkI32 (s.back.toInt + root.bits.toNat) h = .ok (Int32.ofNat root.bits.toNat, h) := by
      rw [back]
      simp only [Int32.toInt_zero, Int.zero_add]
      unfold chkI32
      have rootBound := link.1
      split
      · rfl
      · omega
    have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, hs]
    have write : wrS c.st (fun s => { s with back := Int32.ofNat root.bits.toNat }) h = .ok ((), after) := by
      rw [hc, wrI_eq, hs]
    refine ⟨.ok (), final, used, after, ?_, usedTwo, usedBound, (by
        refine ⟨finalInv.have_eq, ?_, finalInv.hold_lt⟩
        rcases finalInv.next with nil | ⟨ref, array, off, pointer, arrayGet, bound, contents⟩
        · exact Or.inl nil
        · refine Or.inr ⟨ref, array, off, pointer, ?_, bound, contents⟩
          cases ref <;> exact arrayGet),
      symbolShape.trans (by rfl), lastEq, ?_, Or.inl rfl, ?_, ?_, cursor⟩
    · rw [source]
      simp only [runX_bind, runX_get, lastEq, DROPBITS_run current h _ rootSmall,
        runX_lift_ok load, runX_lift_ok checked, runX_lift_ok write]
      simp only [final, lastEq]
    · change (current.bits - root.bits.toUInt32).toNat ≤ _
      rw [finalCount]
      change current.bits.toNat ≤ max l.bits.toNat 22 at bitBound
      omega
    · intro _
      refine ⟨rfl, leaf, ?_, ?_, ?_⟩
      · change current.here.bits.toNat ≤ (current.bits - root.bits.toUInt32).toNat
        rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; simpa using rootEnough), UInt8.toNat_toUInt32]
        omega
      · simpa only [UInt8.toNat_toUInt32, stream, start, final] using finalStream.trans (congrArg (List.drop root.bits.toUInt32.toNat) sameStream)
      · change (current.bits - root.bits.toUInt32).toNat = _
        rw [UInt32.toNat_sub_of_le _ _ (by apply UInt32.le_iff_toNat_le.mpr; simpa using rootEnough), UInt8.toNat_toUInt32]
        exact congrArg (fun n => n - root.bits.toNat) count
    · intro impossible
      cases impossible

/-- Projection retaining the original length-link lookup statement. -/
theorem lenSubLookup_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (root : Code) (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (link : LinkOK LenLeaf ca offset root) (back : s.back = 0) (B : BitInv h l bs) :
    ∃ result regs used after,
      runX (lenSubLookup c root) l h = .ok ((result, regs), after) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.last = root ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () →
        after = setI h zs { s with back := Int32.ofNat root.bits.toNat } ∧
        LenLeaf root.bits.toNat regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop root.bits.toNat ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - root.bits.toNat) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) := by
  obtain ⟨result, regs, used, after, run, two, usedBound, inv, shape, last, bound, kinds, done, leave, _⟩ :=
    lenSubLookup_run_cursor root hc hs pointer tableGet link back B
  exact ⟨result, regs, used, after, run, two, usedBound, inv, shape, last, bound, kinds, done, leave⟩

/-- The source point after the root lookup, including the actual slow-link test. -/
def lenRootTail (c : Ctx) (here : Code) : X Unit := do
  if here.op != 0 && (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c false
    let last := (← get).last
    DROPBITS last.bits.toUInt32
    let s ← ldInflateState c.st
    let bk ← chkI32 (s.back.toInt + last.bits.toNat)
    wrS c.st fun s => { s with back := bk }

def lenLookup (c : Ctx) : X Unit := do
  lookup1 c false
  let here := (← get).here
  lenRootTail c here

theorem lenRootTail_link (c : Ctx) (here : Code) (link : SlowLenLink here) :
    lenRootTail c here = lenSubLookup c here := by
  unfold lenRootTail lenSubLookup
  have nonzero := link.1
  have high := link.2
  simp [nonzero, high]

theorem lenRootTail_leaf (c : Ctx) (here : Code) (leaf : ¬ SlowLenLink here) :
    lenRootTail c here = pure () := by
  unfold lenRootTail
  simp only [bne_iff_ne, beq_iff_eq, Bool.and_eq_true]
  exact if_neg leaf

/-- Actual LEN suffix after root/link lookup and root-bit consumption. -/
def lenFinish (c : Ctx) : X Unit := do
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  let s ← ldInflateState c.st
  let bk ← chkI32 (s.back.toInt + here.bits.toNat)
  wrS c.st fun s => { s with back := bk, length := here.val.toUInt32 }
  if here.op.toNat == 0 then
    setMode c.st LIT
    return
  if (here.op &&& 32) != 0 then
    wrS c.st fun s => { s with back := -1, mode := TYPE }
    return
  if (here.op &&& 64) != 0 then
    badMode c "invalid literal/length code"
    return
  wrS c.st fun s => { s with extra := here.op.toUInt32 &&& 15, mode := LENEXT }
  inflate_LENEXT c

def lenSlow (c : Ctx) : X Unit := do
  -- state->back = 0;
  wrS c.st fun s => { s with back := 0 }
  lookup1 c false
  let here := (← get).here
  -- if (here.op && (here.op & 0xf0) == 0) {
  if here.op != 0 && (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c false
    let last := (← get).last
    DROPBITS last.bits.toUInt32
    let s ← ldInflateState c.st
    let bk ← chkI32 (s.back.toInt + last.bits.toNat)
    wrS c.st fun s => { s with back := bk }
  -- DROPBITS(here.bits); state->back += here.bits; state->length = (unsigned)here.val;
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  let s ← ldInflateState c.st
  let bk ← chkI32 (s.back.toInt + here.bits.toNat)
  wrS c.st fun s => { s with back := bk, length := here.val.toUInt32 }
  -- if ((int)(here.op) == 0) { state->mode = LIT; break; }
  if here.op.toNat == 0 then
    setMode c.st LIT
    return
  -- if (here.op & 32) { state->back = -1; state->mode = TYPE; break; }
  if (here.op &&& 32) != 0 then
    wrS c.st fun s => { s with back := -1, mode := TYPE }
    return
  -- if (here.op & 64) { ...BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid literal/length code"
    return
  -- state->extra = (unsigned)(here.op) & 15; state->mode = LENEXT; /* fallthrough */
  wrS c.st fun s => { s with extra := here.op.toUInt32 &&& 15, mode := LENEXT }
  inflate_LENEXT c


private theorem bindX_assoc {α β γ : Type} (x : X α) (f : α → X β) (g : β → X γ) :
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
    rcases pair with ⟨⟨result, regs⟩, heap⟩
    cases result <;> simp only [run]

/-- The cut contains the actual slow source statements in source order. -/
theorem inflate_LEN_slow_cut {c : Ctx} {l : IL} {h : Heap}
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    runX (inflate_LEN c) l h = runX (lenSlow c) l h := by
  unfold inflate_LEN
  rw [runX_bind, runX_get]
  simp only [slow, Bool.false_eq_true, ite_false]
  rfl

/-- Root and second-level lookup for the actual slow LEN source cut. Normal
returns supply a leaf with enough remaining bits; exhausted input preserves
the uncommitted state and bit stream. The only state write is the bounded
root-bit contribution to back. -/
theorem lenLookup_run_cursor {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat) (back : s.back = 0) (B : BitInv h l bs) :
    ∃ result regs used after,
      runX (lenLookup c) l h = .ok ((result, regs), after) ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → ∃ dropped, dropped ≤ 15 ∧
        after = setI h zs { s with back := Int32.ofNat dropped } ∧
        LenLeaf dropped regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop dropped ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - dropped) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) ∧ regs.next = inputAdvance l.next used := by
  obtain ⟨first, current, used, run, usedTwo, usedBound, inv, sameStream, shape, count,
    bitBound, _, entryBound, classification, kinds, enough, empty, cursor⟩ :=
    lookup1_len_run_cursor hc hs pointer tableGet safe B
  cases first with
  | error e =>
    have equal : e = Ex.leave := by
      rcases kinds with impossible | equal
      · cases impossible
      · exact Except.error.inj equal
    subst e
    refine ⟨.error Ex.leave, current, used, h, ?_, by omega, usedBound, inv, shape.symbol,
      bitBound, Or.inr rfl, ?_, fun _ => ⟨rfl, empty rfl, sameStream⟩, cursor⟩
    · unfold lenLookup
      rw [runX_bind, run]
    · intro impossible
      cases impossible
  | ok unit =>
    cases unit
    have prefixRun : runX (lenLookup c) l h = runX (lenRootTail c current.here) current h := by
      unfold lenLookup
      rw [runX_bind, run]
      simp only [runX_bind, runX_get]
    by_cases slow : SlowLenLink current.here
    · have link : LenLink current.here := slowLenLink_fast slow
      rw [if_pos link] at classification
      obtain ⟨result, final, used2, after, subRun, usedTwo2, usedBound2, finalInv, finalShape,
        _, finalBound, kinds2, done, leave, subCursor⟩ :=
        lenSubLookup_run_cursor current.here hc hs pointer tableGet classification back inv
      have totalBound : used + used2 ≤ bs.length := by
        simp only [List.length_drop] at usedBound2
        omega
      have finalInv' : BitInv after final (bs.drop (used + used2)) := by
        simpa only [List.drop_drop, Nat.add_comm] using finalInv
      have actual : runX (lenLookup c) l h = .ok ((result, final), after) := by
        rw [prefixRun, lenRootTail_link c current.here slow]
        exact subRun
      refine ⟨result, final, used + used2, after, actual, by omega, totalBound, finalInv',
        shape.symbol.trans finalShape, ?_, kinds2, ?_, ?_, by rw [subCursor, cursor, inputAdvance_add]⟩
      · exact Nat.le_trans finalBound (by omega)
      · intro success
        obtain ⟨heapEq, leaf, fits, bits, finalCount⟩ := done success
        refine ⟨current.here.bits.toNat, entryBound, heapEq, leaf, fits, ?_, ?_⟩
        · simpa only [List.drop_drop, Nat.add_comm] using bits.trans (congrArg (List.drop current.here.bits.toNat) sameStream)
        · simp only [count, Nat.mul_add] at finalCount
          simpa only [Nat.mul_add, Nat.add_assoc] using finalCount
      · intro exhausted
        obtain ⟨heapEq, zero, bits⟩ := leave exhausted
        refine ⟨heapEq, zero, ?_⟩
        simpa only [List.drop_drop, Nat.add_comm] using bits.trans sameStream
    · have notLink : ¬ LenLink current.here := by
        intro link
        have table := classification
        rw [if_pos link] at table
        exact slow (lenLink_slow link table)
      rw [if_neg notLink] at classification
      refine ⟨.ok (), current, used, h, ?_, by omega, usedBound, inv, shape.symbol,
        bitBound, Or.inl rfl, ?_, ?_, cursor⟩
      · rw [prefixRun, lenRootTail_leaf c current.here slow, runX_pure]
      · intro _
        refine ⟨0, by omega, ?_, classification, enough rfl, ?_, ?_⟩
        · have stateEq : { s with back := Int32.ofNat 0 } = s := by
            change { s with back := 0 } = s
            rw [← back]
          rw [stateEq]
          simp only [setI, upd_self _ _ _ hs]
        · simpa using sameStream
        · simpa using count
      · intro impossible
        cases impossible

/-- Projection retaining the original complete length lookup. -/
theorem lenLookup_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat) (back : s.back = 0) (B : BitInv h l bs) :
    ∃ result regs used after,
      runX (lenLookup c) l h = .ok ((result, regs), after) ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → ∃ dropped, dropped ≤ 15 ∧
        after = setI h zs { s with back := Int32.ofNat dropped } ∧
        LenLeaf dropped regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop dropped ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - dropped) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) := by
  obtain ⟨result, regs, used, after, run, four, usedBound, inv, shape, bound, kinds, done, leave, _⟩ :=
    lenLookup_run_cursor hc hs pointer tableGet safe back B
  exact ⟨result, regs, used, after, run, four, usedBound, inv, shape, bound, kinds, done, leave⟩

private theorem bindX_ite {α β : Type} (p : Prop) [Decidable p] (a b : X α) (f : α → X β) :
    ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
  split <;> rfl

private theorem bindX_pure {α β : Type} (a : α) (f : α → X β) :
    ((pure a : X α) >>= f) = f a := by
  apply ExceptT.ext
  apply StateT.ext
  intro l
  funext h
  change runX ((pure a : X α) >>= f) l h = runX (f a) l h
  rw [runX_bind, runX_pure]

theorem lenSlow_split (c : Ctx) : lenSlow c = (do
    wrS c.st fun s => { s with back := 0 }
    lenLookup c
    lenFinish c) := by
  unfold lenSlow lenLookup lenRootTail lenFinish
  simp only [bindX_assoc, bindX_ite, bindX_pure]

end Zlib.Inflate.Proofs
