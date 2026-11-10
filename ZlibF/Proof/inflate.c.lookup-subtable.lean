import ZlibF.Proof.«inflate.c.lookup-data»
import ZlibF.Math.InflateLookupBits

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inffast.Spec
set_option autoImplicit false

def dataSubLookupBody (c : Ctx) (dist : Bool) : X Bool := do
  let s ← ldInflateState c.st
  let tab := if dist then s.distcode else s.lencode
  let last := (← get).last
  let b ← BITS (last.bits.toUInt32 + last.op.toUInt32)
  let sh ← shr32 b last.bits.toUInt32
  let here ← Ptr.index tab ((last.val.toUInt32 + sh).toNat : Int)
  modify fun l => { l with here := here }
  if (last.bits.toUInt32 + here.bits.toUInt32) <= (← get).bits then return true
  PULLBYTE
  return false

theorem lookup2_data_eq (c : Ctx) (dist : Bool) :
    lookup2 c dist = xloopBrk (dataSubLookupBody c dist) := rfl

def subLookupIndex (last : Code) (l : IL) : Nat :=
  l.hold.toNat % 2 ^ (last.bits.toNat + last.op.toNat) / 2 ^ last.bits.toNat

def subLookupValue (ca : Array Code) (offset : Nat) (last : Code) (l : IL) : Code :=
  ca.getD (offset + last.val.toNat + subLookupIndex last l) default

theorem subLookupIndex_lt (last : Code) (l : IL) : subLookupIndex last l < 2 ^ last.op.toNat :=
  ZlibF.Math.InflateLookup.slice_lt _ _ _

/-- The actual second-level mask, shift and index resolve to a bounded cell.
The remembered root entry is the same last field used by the translation. -/
theorem dataSubLookupBody_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {P : Nat → Code → Prop}
    (dist : Bool) (l : IL) (last : Code)
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : (if dist then s.distcode else s.lencode) = .ref ref offset)
    (get : Space.get h ref = some ca) (remembered : l.last = last)
    (link : LinkOK P ca offset last) :
    let entry := subLookupValue ca offset last l
    runX (dataSubLookupBody c dist) l h =
      if last.bits.toUInt32 + entry.bits.toUInt32 ≤ l.bits then
        .ok ((.ok true, { l with here := entry }), h)
      else runX (do PULLBYTE; pure false : X Bool) { l with here := entry } h := by
  dsimp only
  let width := last.bits.toUInt32 + last.op.toUInt32
  have widthNat : width.toNat = last.bits.toNat + last.op.toNat := by
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32,
      Nat.mod_eq_of_lt (by have := link.1; have := link.2.2.1; omega)]
  have widthBound : width.toNat < 32 := by rw [widthNat]; have := link.1; have := link.2.2.1; omega
  have shiftBound : last.bits.toUInt32.toNat < 32 := by rw [UInt8.toNat_toUInt32]; have := link.1; omega
  let mask := l.hold.toUInt32 &&& ((1 : UInt32) <<< width - 1)
  let shifted := mask >>> last.bits.toUInt32
  have maskNat : mask.toNat = l.hold.toNat % 2 ^ width.toNat := BITS_toNat l width widthBound
  have shiftNat : shifted.toNat = subLookupIndex last l := by
    rw [UInt32.toNat_shiftRight, UInt8.toNat_toUInt32,
      Nat.mod_eq_of_lt (by have := link.1; omega), Nat.shiftRight_eq_div_pow]
    rw [maskNat, widthNat]
    rfl
  have suffixBound : shifted.toNat < 2 ^ last.op.toNat := by rw [shiftNat]; exact subLookupIndex_lt _ _
  have indexNat : (last.val.toUInt32 + shifted).toNat = last.val.toNat + subLookupIndex last l := by
    rw [UInt32.toNat_add, UInt16.toNat_toUInt32, shiftNat]
    apply Nat.mod_eq_of_lt
    have valBound := UInt16.toNat_lt last.val
    have powBound : 2 ^ last.op.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) link.2.2.1
    have indexBound := subLookupIndex_lt last l
    omega
  have inside : offset + (last.val.toUInt32 + shifted).toNat < ca.size := by
    rw [indexNat]
    have capacity := link.2.2.2.1
    have := subLookupIndex_lt last l
    omega
  have read := Ptr.index_ok (off := offset) (i := (last.val.toUInt32 + shifted).toNat) get inside
  have actual : ca[offset + (last.val.toUInt32 + shifted).toNat] = subLookupValue ca offset last l := by
    unfold subLookupValue
    rw [Array.getD_eq_getD_getElem?, Nat.add_assoc, ← indexNat,
      Array.getElem?_eq_getElem inside, Option.getD_some]
  have bitsRun := BITS_run l h width widthBound
  have shiftRun : shr32 mask last.bits.toUInt32 h = .ok (shifted, h) := by
    rw [shr32_run mask _ shiftBound]
    rfl
  dsimp only [mask, shifted, width] at read actual bitsRun shiftRun
  have load : ldInflateState (some (.tab zs)) h = .ok (s, h) := by simp [ldI_eq, hs]
  unfold dataSubLookupBody
  rw [hc]
  simp only [runX_bind, runX_lift_ok load, runX_get, remembered, bitsRun, runX_lift_ok shiftRun,
    pointer, runX_lift_ok read, actual, runX_modify]
  by_cases fit : last.bits.toUInt32 + (subLookupValue ca offset last l).bits.toUInt32 ≤ l.bits
  all_goals simp only [fit, ite_true, ite_false, runX_bind, runX_pure]

/-- The complete actual second-level lookup terminates. Every selected cell
is a leaf of the same installed table. Its total code width is at most 15,
so at most two bytes are pulled, including input-exhaustion outcomes. -/
theorem lookup2_data_run_cursor {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {P : Nat → Code → Prop}
    {l : IL} {bs : List UInt8} (dist : Bool) (last : Code)
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : (if dist then s.distcode else s.lencode) = .ref ref offset)
    (get : Space.get h ref = some ca) (remembered : l.last = last)
    (link : LinkOK P ca offset last)
    (leafBound : ∀ entry, P last.bits.toNat entry → entry.bits.toNat + last.bits.toNat ≤ 15)
    (B : BitInv h l bs) :
    ∃ result regs used,
      runX (lookup2 c dist) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = subLookupValue ca offset last regs ∧ P last.bits.toNat regs.here ∧
      last.bits.toNat + regs.here.bits.toNat ≤ 15 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → last.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0) ∧ regs.next = inputAdvance l.next used := by
  let need := fun entry : Code => last.bits.toUInt32 + entry.bits.toUInt32
  have leaf : ∀ current, P last.bits.toNat (subLookupValue ca offset last current) := by
    intro current
    exact link.2.2.2.2 _ (subLookupIndex_lt _ _)
  have needNat : ∀ current, (need (subLookupValue ca offset last current)).toNat =
      last.bits.toNat + (subLookupValue ca offset last current).bits.toNat := by
    intro current
    have bound := leafBound _ (leaf current)
    rw [UInt32.toNat_add, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  rw [lookup2_data_eq]
  obtain ⟨result, regs, used, run, usedTwo, usedBound, inv, sameStream, shape, count, bitBound,
    selected, totalBound, kinds, enough, empty, cursor⟩ :=
    lookupLoop_run_cursor (query := subLookupValue ca offset last) (need := need) (fun _ => rfl)
      (by intro current; rw [needNat]; have := leafBound _ (leaf current); omega)
      (by
        intro current frame
        have lastEq : current.last = last := by rw [frame, remembered]
        exact dataSubLookupBody_run dist current last hc hs pointer get lastEq link) B
  have finalLeaf : P last.bits.toNat regs.here := by rw [selected]; exact leaf regs
  have totalNat : (need regs.here).toNat = last.bits.toNat + regs.here.bits.toNat := by
    rw [selected, needNat]
  refine ⟨result, regs, used, run, usedTwo, usedBound, inv, sameStream, shape, count, bitBound,
    selected, finalLeaf, ?_, kinds, ?_, empty, cursor⟩
  · rw [← totalNat]
    exact totalBound
  · intro success
    rw [← totalNat]
    exact enough success

/-- Projection retaining the original second-level lookup statement. -/
theorem lookup2_data_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {P : Nat → Code → Prop}
    {l : IL} {bs : List UInt8} (dist : Bool) (last : Code)
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : (if dist then s.distcode else s.lencode) = .ref ref offset)
    (get : Space.get h ref = some ca) (remembered : l.last = last)
    (link : LinkOK P ca offset last)
    (leafBound : ∀ entry, P last.bits.toNat entry → entry.bits.toNat + last.bits.toNat ≤ 15)
    (B : BitInv h l bs) :
    ∃ result regs used,
      runX (lookup2 c dist) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = subLookupValue ca offset last regs ∧ P last.bits.toNat regs.here ∧
      last.bits.toNat + regs.here.bits.toNat ≤ 15 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → last.bits.toNat + regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0) := by
  obtain ⟨result, regs, used, run, two, usedBound, inv, bits, shape, count, bitBound,
    selected, finalLeaf, total, kinds, enough, empty, _⟩ :=
      lookup2_data_run_cursor dist last hc hs pointer get remembered link leafBound B
  exact ⟨result, regs, used, run, two, usedBound, inv, bits, shape, count, bitBound,
    selected, finalLeaf, total, kinds, enough, empty⟩

end Zlib.Inflate.Proofs
