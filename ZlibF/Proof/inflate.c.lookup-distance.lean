import ZlibF.Proof.«inflate.c.length-extra»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual slow distance-link block, including its checked signed counter update. -/
def distSubLookup (c : Ctx) (root : Code) : X Unit := do
  modify fun l => { l with last := root }
  lookup2 c true
  let last := (← get).last
  DROPBITS last.bits.toUInt32
  let s ← ldInflateState c.st
  let bk ← chkI32 (s.back.toInt + last.bits.toNat)
  wrS c.st fun s => { s with back := bk }

/-- Actual second-level distance lookup plus the root-bit consumption. Every
successful result is a proved leaf, with enough held bits to consume it.
Input exhaustion occurs before the state or bit buffer is committed. -/
theorem distSubLookup_run_cursor {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (root : Code) (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (link : LinkOK DistLeaf ca offset root) (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) (B : BitInv h l bs) :
    ∃ result regs used after,
      runX (distSubLookup c root) l h = .ok ((result, regs), after) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.last = root ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () →
        after = setI h zs { s with back := Int32.ofNat (before + root.bits.toNat) } ∧
        DistLeaf root.bits.toNat regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop root.bits.toNat ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - root.bits.toNat) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) ∧ regs.next = inputAdvance l.next used := by
  let start := { l with last := root }
  have startInv : BitInv h start bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  obtain ⟨result, current, used, run, usedTwo, usedBound, currentInv, sameStream, shape, count,
    bitBound, _, leaf, totalBound, kinds, enough, empty, cursor⟩ :=
    lookup2_data_run_cursor true root hc hs pointer tableGet (l := start) rfl link
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
    · unfold distSubLookup
      rw [runX_bind, runX_modify]
      simp only []
      rw [runX_bind, run]
    · intro impossible
      cases impossible
    · intro _
      exact ⟨rfl, empty rfl, sameStream⟩
  | ok unit =>
    cases unit
    have source : runX (distSubLookup c root) l h =
        runX (do
          let last := (← get).last
          DROPBITS last.bits.toUInt32
          let s ← ldInflateState c.st
          let bk ← chkI32 (s.back.toInt + last.bits.toNat)
          wrS c.st fun s => { s with back := bk }) current h := by
      unfold distSubLookup
      rw [runX_bind, runX_modify]
      simp only []
      rw [runX_bind, run]
    have totalEnough := enough rfl
    have rootEnough : root.bits.toNat ≤ current.bits.toNat := by omega
    have rootSmall : root.bits.toUInt32.toNat < 64 := by rw [UInt8.toNat_toUInt32]; have := link.1; omega
    obtain ⟨finalInv, finalStream, finalCount⟩ :=
      DROPBITS_inv currentInv root.bits.toUInt32 (by simpa using rootEnough) rootSmall
    let final := { current with hold := current.hold >>> root.bits.toUInt32.toUInt64, bits := current.bits - root.bits.toUInt32 }
    let after := setI h zs { s with back := Int32.ofNat (before + root.bits.toNat) }
    have checked : chkI32 (s.back.toInt + root.bits.toNat) h = .ok (Int32.ofNat (before + root.bits.toNat), h) := by
      rw [back]
      rw [show (Int32.ofNat before).toInt = (before : Int) from int32_ofInt_toInt before (by omega) (by omega)]
      unfold chkI32
      have rootBound := link.1
      split
      · rfl
      · omega
    have load : ldInflateState c.st h = .ok (s, h) := by rw [hc, ldI_eq, hs]
    have write : wrS c.st (fun s => { s with back := Int32.ofNat (before + root.bits.toNat) }) h = .ok ((), after) := by
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


/-- Projection retaining the original distance-link lookup statement. -/
theorem distSubLookup_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (root : Code) (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (link : LinkOK DistLeaf ca offset root) (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) (B : BitInv h l bs) :
    ∃ result regs used after,
      runX (distSubLookup c root) l h = .ok ((result, regs), after) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.last = root ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () →
        after = setI h zs { s with back := Int32.ofNat (before + root.bits.toNat) } ∧
        DistLeaf root.bits.toNat regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop root.bits.toNat ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - root.bits.toNat) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) := by
  obtain ⟨result, regs, used, after, run, two, usedBound, inv, shape, last, bound, kinds, done, leave, _⟩ :=
    distSubLookup_run_cursor root hc hs pointer tableGet link before back backBound B
  exact ⟨result, regs, used, after, run, two, usedBound, inv, shape, last, bound, kinds, done, leave⟩

/-- The distance decoder's actual root-link test. -/
def SlowDistLink (entry : Code) : Prop := entry.op &&& 240 = 0
instance (entry : Code) : Decidable (SlowDistLink entry) := inferInstanceAs (Decidable (entry.op &&& 240 = 0))

theorem slowDistLink_fast {entry : Code} (slow : SlowDistLink entry) : DistLink entry :=
  ZlibF.Math.InflateLookup.high_zero_flags entry.op slow

theorem distLink_slow {entry : Code} {ca : Array Code} {offset : Nat}
    (safe : LinkOK DistLeaf ca offset entry) : SlowDistLink entry :=
  ZlibF.Math.InflateLookup.small_high_zero entry.op safe.2.2.1

def distRootTail (c : Ctx) (here : Code) : X Unit := do
  if (here.op &&& 0xf0) == 0 then
    modify fun l => { l with last := here }
    lookup2 c true
    let last := (← get).last
    DROPBITS last.bits.toUInt32
    let s ← ldInflateState c.st
    let bk ← chkI32 (s.back.toInt + last.bits.toNat)
    wrS c.st fun s => { s with back := bk }

def distLookup (c : Ctx) : X Unit := do
  lookup1 c true
  let here := (← get).here
  distRootTail c here

theorem distRootTail_link (c : Ctx) (here : Code) (link : SlowDistLink here) :
    distRootTail c here = distSubLookup c here := by
  unfold distRootTail distSubLookup
  have high := link
  change here.op &&& 240 = 0 at high
  simp [high]

theorem distRootTail_leaf (c : Ctx) (here : Code) (leaf : ¬ SlowDistLink here) :
    distRootTail c here = pure () := by
  unfold distRootTail
  have high : here.op &&& 240 ≠ 0 := leaf
  simp [high]

/-- Root and second-level lookup for the actual DIST source cut. Normal
returns supply a leaf with enough remaining bits; exhausted input preserves
the uncommitted state and bit stream. The only state write is the bounded
root-bit contribution to back. -/
theorem distLookup_run_cursor {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : DistTableSafe ca offset s.distbits.toNat) (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) (B : BitInv h l bs) :
    ∃ result regs used after,
      runX (distLookup c) l h = .ok ((result, regs), after) ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → ∃ dropped, dropped ≤ 15 ∧
        after = setI h zs { s with back := Int32.ofNat (before + dropped) } ∧
        DistLeaf dropped regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop dropped ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - dropped) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) ∧ regs.next = inputAdvance l.next used := by
  obtain ⟨first, current, used, run, usedTwo, usedBound, inv, sameStream, shape, count,
    bitBound, _, entryBound, classification, kinds, enough, empty, cursor⟩ :=
    lookup1_dist_run_cursor hc hs pointer tableGet safe B
  cases first with
  | error e =>
    have equal : e = Ex.leave := by
      rcases kinds with impossible | equal
      · cases impossible
      · exact Except.error.inj equal
    subst e
    refine ⟨.error Ex.leave, current, used, h, ?_, by omega, usedBound, inv, shape.symbol,
      bitBound, Or.inr rfl, ?_, fun _ => ⟨rfl, empty rfl, sameStream⟩, cursor⟩
    · unfold distLookup
      rw [runX_bind, run]
    · intro impossible
      cases impossible
  | ok unit =>
    cases unit
    have prefixRun : runX (distLookup c) l h = runX (distRootTail c current.here) current h := by
      unfold distLookup
      rw [runX_bind, run]
      simp only [runX_bind, runX_get]
    by_cases slow : SlowDistLink current.here
    · have link : DistLink current.here := slowDistLink_fast slow
      rw [if_pos link] at classification
      obtain ⟨result, final, used2, after, subRun, usedTwo2, usedBound2, finalInv, finalShape,
        _, finalBound, kinds2, done, leave, subCursor⟩ :=
        distSubLookup_run_cursor current.here hc hs pointer tableGet classification before back backBound inv
      have totalBound : used + used2 ≤ bs.length := by
        simp only [List.length_drop] at usedBound2
        omega
      have finalInv' : BitInv after final (bs.drop (used + used2)) := by
        simpa only [List.drop_drop, Nat.add_comm] using finalInv
      have actual : runX (distLookup c) l h = .ok ((result, final), after) := by
        rw [prefixRun, distRootTail_link c current.here slow]
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
    · have notLink : ¬ DistLink current.here := by
        intro link
        have table := classification
        rw [if_pos link] at table
        exact slow (distLink_slow table)
      rw [if_neg notLink] at classification
      refine ⟨.ok (), current, used, h, ?_, by omega, usedBound, inv, shape.symbol,
        bitBound, Or.inl rfl, ?_, ?_, cursor⟩
      · rw [prefixRun, distRootTail_leaf c current.here slow, runX_pure]
      · intro _
        refine ⟨0, by omega, ?_, classification, enough rfl, ?_, ?_⟩
        · have stateEq : { s with back := Int32.ofNat (before + 0) } = s := by
            rw [Nat.add_zero, ← back]
          rw [stateEq]
          simp only [setI, upd_self _ _ _ hs]
        · simpa using sameStream
        · simpa using count
      · intro impossible
        cases impossible

/-- Projection retaining the original complete distance lookup. -/
theorem distLookup_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (safe : DistTableSafe ca offset s.distbits.toNat) (before : Nat) (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) (B : BitInv h l bs) :
    ∃ result regs used after,
      runX (distLookup c) l h = .ok ((result, regs), after) ∧
      used ≤ 4 ∧ used ≤ bs.length ∧ BitInv after regs (bs.drop used) ∧
      SymbolRegShape l regs ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → ∃ dropped, dropped ≤ 15 ∧
        after = setI h zs { s with back := Int32.ofNat (before + dropped) } ∧
        DistLeaf dropped regs.here ∧ regs.here.bits.toNat ≤ regs.bits.toNat ∧
        stream regs (bs.drop used) = (stream l bs).drop dropped ∧
        regs.bits.toNat = l.bits.toNat + 8 * used - dropped) ∧
      (result = .error Ex.leave → after = h ∧ regs.have_ = 0 ∧
        stream regs (bs.drop used) = stream l bs) := by
  obtain ⟨result, regs, used, after, run, four, usedBound, inv, shape, bound, kinds, done, leave, _⟩ :=
    distLookup_run_cursor hc hs pointer tableGet safe before back backBound B
  exact ⟨result, regs, used, after, run, four, usedBound, inv, shape, bound, kinds, done, leave⟩

/-- Actual DIST suffix after root/link lookup and root-bit consumption. -/
def distFinish (c : Ctx) : X Unit := do
  -- DROPBITS(here.bits); state->back += here.bits;
  let here := (← get).here
  DROPBITS here.bits.toUInt32
  let s ← ldInflateState c.st
  let bk ← chkI32 (s.back.toInt + here.bits.toNat)
  wrS c.st fun s => { s with back := bk }
  -- if (here.op & 64) { ...BAD; break; }
  if (here.op &&& 64) != 0 then
    badMode c "invalid distance code"
    return
  -- state->offset = (unsigned)here.val; state->extra = (unsigned)(here.op) & 15; state->mode = DISTEXT;
  wrS c.st fun s => { s with offset := here.val.toUInt32, extra := here.op.toUInt32 &&& 15 }
  setMode c.st DISTEXT
  inflate_DISTEXT c

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

/-- Exact decomposition of the actual DIST branch into lookup and leaf work. -/
theorem inflate_DIST_lookup_cut (c : Ctx) : inflate_DIST c = (do distLookup c; distFinish c) := by
  unfold inflate_DIST distLookup distRootTail distFinish
  simp only [bindX_assoc, bindX_ite, bindX_pure]

/-- Actual DIST lookup uses the same installed table as its caller. It
returns safely on exhausted input or reaches the actual finishing suffix
with a proved distance leaf and enough held bits. -/
theorem inflate_DIST_lookup_boundary_bounded {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) :
    (∃ regs used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_DIST c) l h = .ok ((.error Ex.leave, regs), h) ∧
      BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 22) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_DIST c) l h = runX (distFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ DistLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat (before + dropped) ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      after = setI h zs state ∧ state = { s with back := Int32.ofNat (before + dropped) } ∧ regs.next = inputAdvance l.next used ∧ regs.bits.toNat ≤ max l.bits.toNat 22) := by
  obtain ⟨ref, offset, array, pointer, tableGet, tableSafe⟩ := tables.distanceTable
  obtain ⟨result, regs, used, after, run, usedFour, usedBound, inv, shape, bitBound, kinds, done, leave, cursor⟩ :=
    distLookup_run_cursor hc good.live.hs pointer tableGet tableSafe before back backBound B
  cases result with
  | error e =>
    have equal : e = Ex.leave := by
      rcases kinds with impossible | equal
      · cases impossible
      · exact Except.error.inj equal
    subst e
    obtain ⟨heapEq, empty, bits⟩ := leave rfl
    subst after
    left
    refine ⟨regs, used, usedFour, usedBound, ?_, inv, empty, bits, shape, cursor, bitBound⟩
    rw [inflate_DIST_lookup_cut, runX_bind, run]
  | ok unit =>
    cases unit
    obtain ⟨dropped, dropBound, heapEq, leaf, enough, bits, count⟩ := done rfl
    subst after
    let state := { s with back := Int32.ofNat (before + dropped) }
    have finalGood : Good (setI h zs state) r zs z state := good.decode_update rfl good.live.mode
    have finalTables : DataTablesSafe (setI h zs state) state := tables.decode_update good.live.hs rfl
    right
    refine ⟨regs, setI h zs state, state, used, dropped, usedFour, usedBound, dropBound,
      ?_, finalGood, finalTables, inv, leaf, enough, rfl, bits, shape, rfl, count, rfl, rfl, cursor, bitBound⟩
    rw [inflate_DIST_lookup_cut, runX_bind, run]

/-- Projection retaining the previous boundary. -/
theorem inflate_DIST_lookup_boundary_cursor {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) :
    (∃ regs used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_DIST c) l h = .ok ((.error Ex.leave, regs), h) ∧
      BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_DIST c) l h = runX (distFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ DistLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat (before + dropped) ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      after = setI h zs state ∧ state = { s with back := Int32.ofNat (before + dropped) } ∧ regs.next = inputAdvance l.next used) := by
  rcases inflate_DIST_lookup_boundary_bounded before hc good tables B back backBound with wait | continued
  · obtain ⟨regs, used, four, usedBound, run, inv, empty, bits, shape, cursor, _⟩ := wait
    exact Or.inl ⟨regs, used, four, usedBound, run, inv, empty, bits, shape, cursor⟩
  · obtain ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, inv, leaf, enough, back, bits, shape, frame, count, heap, stateEq, cursor, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, inv, leaf, enough, back, bits, shape, frame, count, heap, stateEq, cursor⟩

/-- Projection retaining the original framed distance boundary. -/
theorem inflate_DIST_lookup_boundary_full {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) :
    (∃ regs used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_DIST c) l h = .ok ((.error Ex.leave, regs), h) ∧
      BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_DIST c) l h = runX (distFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ DistLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat (before + dropped) ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped ∧
      after = setI h zs state ∧ state = { s with back := Int32.ofNat (before + dropped) }) := by
  rcases inflate_DIST_lookup_boundary_cursor before hc good tables B back backBound with wait | continued
  · obtain ⟨regs, used, four, usedBound, run, inv, empty, bits, shape, _⟩ := wait
    exact Or.inl ⟨regs, used, four, usedBound, run, inv, empty, bits, shape⟩
  · obtain ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, inv, leaf, enough, back, bits, shape, frame, count, heap, stateEq, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, dropped, four, usedBound, dropBound, run,
      finalGood, finalTables, inv, leaf, enough, back, bits, shape, frame, count, heap, stateEq⟩
/-- Actual DIST lookup uses the same installed table as its caller. It
returns safely on exhausted input or reaches the actual finishing suffix
with a proved distance leaf and enough held bits. -/
theorem inflate_DIST_lookup_boundary {c : Ctx} {l : IL} {h : Heap}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState} {bs : List UInt8} (before : Nat)
    (hc : c.st = some (.tab zs)) (good : Good h r zs z s)
    (tables : DataTablesSafe h s) (B : BitInv h l bs)
    (back : s.back = Int32.ofNat before) (backBound : before ≤ 20) :
    (∃ regs used,
      used ≤ 4 ∧ used ≤ bs.length ∧
      runX (inflate_DIST c) l h = .ok ((.error Ex.leave, regs), h) ∧
      BitInv h regs (bs.drop used) ∧ regs.have_ = 0 ∧
      stream regs (bs.drop used) = stream l bs ∧ SymbolRegShape l regs) ∨
    (∃ regs after state used dropped,
      used ≤ 4 ∧ used ≤ bs.length ∧ dropped ≤ 15 ∧
      runX (inflate_DIST c) l h = runX (distFinish c) regs after ∧
      Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ DistLeaf dropped regs.here ∧
      regs.here.bits.toNat ≤ regs.bits.toNat ∧ state.back = Int32.ofNat (before + dropped) ∧
      stream regs (bs.drop used) = (stream l bs).drop dropped ∧
      SymbolRegShape l regs ∧ DecodeStateFrame s state ∧
      regs.bits.toNat = l.bits.toNat + 8 * used - dropped) := by
  rcases inflate_DIST_lookup_boundary_full before hc good tables B back backBound with wait | continued
  · exact Or.inl wait
  · obtain ⟨regs, after, state, used, dropped, usedFour, usedBound, droppedBound,
      run, finalGood, finalTables, inv, leaf, enough, backEq, bits, shape, frame, count, _, _⟩ := continued
    exact Or.inr ⟨regs, after, state, used, dropped, usedFour, usedBound, droppedBound,
      run, finalGood, finalTables, inv, leaf, enough, backEq, bits, shape, frame, count⟩

end Zlib.Inflate.Proofs
