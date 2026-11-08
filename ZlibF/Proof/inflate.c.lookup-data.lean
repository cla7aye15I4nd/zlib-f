import ZlibF.Proof.«inflate.c.lookup-loop»
import ZlibF.Spec.InflateTableInvariant

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inffast.Spec
set_option autoImplicit false

def dataLookupBody (c : Ctx) (dist : Bool) : X Bool := do
  let s ← ldInflateState c.st
  let tab := if dist then s.distcode else s.lencode
  let nb := if dist then s.distbits else s.lenbits
  let b ← BITS nb
  let here ← Ptr.index tab (b.toNat : Int)
  modify fun l => { l with here := here }
  if here.bits.toUInt32 <= (← get).bits then return true
  PULLBYTE
  return false

theorem lookup1_data_eq (c : Ctx) (dist : Bool) :
    lookup1 c dist = xloopBrk (dataLookupBody c dist) := rfl

/-- The root cells actually read by lookup1 are in bounds and have bounded widths. -/
def RootTableReadable (ca : Array Code) (offset root : Nat) : Prop :=
  root ≤ 15 ∧ offset + 2 ^ root ≤ ca.size ∧
    ∀ i, i < 2 ^ root → (ca.getD (offset + i) default).bits.toNat ≤ 15

theorem lenTableSafe_readable {ca : Array Code} {offset root : Nat}
    (safe : LenTableSafe ca offset root) : RootTableReadable ca offset root := by
  refine ⟨safe.1, safe.2.1, ?_⟩
  intro i bound
  have cell := safe.2.2 i bound
  split at cell
  · exact cell.1
  · simpa only [Nat.add_zero] using cell.1

theorem distTableSafe_readable {ca : Array Code} {offset root : Nat}
    (safe : DistTableSafe ca offset root) : RootTableReadable ca offset root := by
  refine ⟨safe.1, safe.2.1, ?_⟩
  intro i bound
  have cell := safe.2.2 i bound
  split at cell
  · exact cell.1
  · simpa only [Nat.add_zero] using cell.1

/-- One actual root-table read, including the exact refill guard. -/
theorem dataLookupBody_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} (dist : Bool) (l : IL)
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : (if dist then s.distcode else s.lencode) = .ref ref offset)
    (get : Space.get h ref = some ca)
    (safe : RootTableReadable ca offset (if dist then s.distbits else s.lenbits).toNat) :
    let entry := codeLookupValue ca offset (if dist then s.distbits else s.lenbits).toNat l
    runX (dataLookupBody c dist) l h =
      if entry.bits.toUInt32 ≤ l.bits then .ok ((.ok true, { l with here := entry }), h)
      else runX (do PULLBYTE; pure false : X Bool) { l with here := entry } h := by
  dsimp only
  let width := if dist then s.distbits else s.lenbits
  change RootTableReadable ca offset width.toNat at safe
  have root : width.toNat < 32 := by have := safe.1; omega
  let mask := l.hold.toUInt32 &&& ((1 : UInt32) <<< width - 1)
  have value : mask.toNat = l.hold.toNat % 2 ^ width.toNat := BITS_toNat l width root
  have inside : offset + mask.toNat < ca.size := by
    have := Nat.mod_lt l.hold.toNat (Nat.two_pow_pos width.toNat)
    have := safe.2.1
    omega
  have read := Ptr.index_ok (off := offset) (i := mask.toNat) get inside
  have actual : ca[offset + mask.toNat] = codeLookupValue ca offset width.toNat l := by
    unfold codeLookupValue
    rw [← value, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
  have bitsRun := BITS_run l h width root
  dsimp only [mask, width] at read actual bitsRun
  unfold dataLookupBody
  rw [hc]
  have load : ldInflateState (some (.tab zs)) h = .ok (s, h) := by simp [ldI_eq, hs]
  simp only [runX_bind, runX_lift_ok load, bitsRun,
    runX_modify, runX_get, pointer, runX_lift_ok read, actual]
  by_cases fit : (codeLookupValue ca offset width.toNat l).bits.toUInt32 ≤ l.bits
  all_goals
    dsimp only [width] at fit
    simp only [fit, ite_true, ite_false, runX_bind, runX_pure]

/-- The actual LEN/DIST root lookup terminates after at most two input bytes.
Refill is permitted only below fifteen held bits. Both normal and exhausted
input exits retain the same bit stream and exact selected root cell. -/
theorem lookup1_data_readable_run_cursor {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (dist : Bool) (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : (if dist then s.distcode else s.lencode) = .ref ref offset)
    (get : Space.get h ref = some ca)
    (safe : RootTableReadable ca offset (if dist then s.distbits else s.lenbits).toNat)
    (B : BitInv h l bs) :
    ∃ result regs used,
      runX (lookup1 c dist) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = codeLookupValue ca offset (if dist then s.distbits else s.lenbits).toNat regs ∧
      regs.here.bits.toNat ≤ 15 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0) ∧ regs.next = inputAdvance l.next used := by
  rw [lookup1_data_eq]
  apply lookupLoop_run_cursor (query := codeLookupValue ca offset (if dist then s.distbits else s.lenbits).toNat)
    (need := fun entry => entry.bits.toUInt32) (fun _ => rfl) ?_ ?_ B
  · intro current
    rw [UInt8.toNat_toUInt32]
    exact safe.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _))
  · intro current _
    exact dataLookupBody_run dist current hc hs pointer get safe

/-- Projection retaining the original lookup statement. -/
theorem lookup1_data_readable_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (dist : Bool) (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : (if dist then s.distcode else s.lencode) = .ref ref offset)
    (get : Space.get h ref = some ca)
    (safe : RootTableReadable ca offset (if dist then s.distbits else s.lenbits).toNat)
    (B : BitInv h l bs) :
    ∃ result regs used,
      runX (lookup1 c dist) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = codeLookupValue ca offset (if dist then s.distbits else s.lenbits).toNat regs ∧
      regs.here.bits.toNat ≤ 15 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0) := by
  obtain ⟨result, regs, used, run, two, usedBound, inv, bits, shape, count, bitBound,
    selected, entryBound, kinds, enough, empty, _⟩ := lookup1_data_readable_run_cursor dist hc hs pointer get safe B
  exact ⟨result, regs, used, run, two, usedBound, inv, bits, shape, count, bitBound,
    selected, entryBound, kinds, enough, empty⟩

/-- An actual root lookup retains the exact root entry and its constructor
classification. The caller does not supply an independent decoded symbol. -/
theorem lookup1_len_run_cursor {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat) (B : BitInv h l bs) :
    ∃ result regs used,
      runX (lookup1 c false) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = codeLookupValue ca offset s.lenbits.toNat regs ∧
      regs.here.bits.toNat ≤ 15 ∧
      (if LenLink regs.here then LinkOK LenLeaf ca offset regs.here else LenLeaf 0 regs.here) ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0) ∧ regs.next = inputAdvance l.next used := by
  obtain ⟨result, regs, used, run, usedTwo, usedBound, inv, sameStream, shape, count, bits,
    selected, entryBound, kinds, enough, empty, cursor⟩ :=
    lookup1_data_readable_run_cursor false hc hs pointer get (lenTableSafe_readable safe) B
  refine ⟨result, regs, used, run, usedTwo, usedBound, inv, sameStream, shape, count, bits,
    selected, entryBound, ?_, kinds, enough, empty, cursor⟩
  rw [selected]
  exact safe.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _))

/-- Projection retaining the original lookup statement. -/
theorem lookup1_len_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (safe : LenTableSafe ca offset s.lenbits.toNat) (B : BitInv h l bs) :
    ∃ result regs used,
      runX (lookup1 c false) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = codeLookupValue ca offset s.lenbits.toNat regs ∧
      regs.here.bits.toNat ≤ 15 ∧
      (if LenLink regs.here then LinkOK LenLeaf ca offset regs.here else LenLeaf 0 regs.here) ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0) := by
  obtain ⟨result, regs, used, run, two, usedBound, inv, bits, shape, count, bitBound,
    selected, entryBound, classification, kinds, enough, empty, _⟩ := lookup1_len_run_cursor hc hs pointer get safe B
  exact ⟨result, regs, used, run, two, usedBound, inv, bits, shape, count, bitBound,
    selected, entryBound, classification, kinds, enough, empty⟩

theorem lookup1_dist_run_cursor {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (get : Space.get h ref = some ca)
    (safe : DistTableSafe ca offset s.distbits.toNat) (B : BitInv h l bs) :
    ∃ result regs used,
      runX (lookup1 c true) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = codeLookupValue ca offset s.distbits.toNat regs ∧
      regs.here.bits.toNat ≤ 15 ∧
      (if DistLink regs.here then LinkOK DistLeaf ca offset regs.here else DistLeaf 0 regs.here) ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0) ∧ regs.next = inputAdvance l.next used := by
  obtain ⟨result, regs, used, run, usedTwo, usedBound, inv, sameStream, shape, count, bits,
    selected, entryBound, kinds, enough, empty, cursor⟩ :=
    lookup1_data_readable_run_cursor true hc hs pointer get (distTableSafe_readable safe) B
  refine ⟨result, regs, used, run, usedTwo, usedBound, inv, sameStream, shape, count, bits,
    selected, entryBound, ?_, kinds, enough, empty, cursor⟩
  rw [selected]
  exact safe.2.2 _ (Nat.mod_lt _ (Nat.two_pow_pos _))
/-- Projection retaining the original lookup statement. -/
theorem lookup1_dist_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.distcode = .ref ref offset) (get : Space.get h ref = some ca)
    (safe : DistTableSafe ca offset s.distbits.toNat) (B : BitInv h l bs) :
    ∃ result regs used,
      runX (lookup1 c true) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = codeLookupValue ca offset s.distbits.toNat regs ∧
      regs.here.bits.toNat ≤ 15 ∧
      (if DistLink regs.here then LinkOK DistLeaf ca offset regs.here else DistLeaf 0 regs.here) ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → regs.here.bits.toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0) := by
  obtain ⟨result, regs, used, run, two, usedBound, inv, bits, shape, count, bitBound,
    selected, entryBound, classification, kinds, enough, empty, _⟩ := lookup1_dist_run_cursor hc hs pointer get safe B
  exact ⟨result, regs, used, run, two, usedBound, inv, bits, shape, count, bitBound,
    selected, entryBound, classification, kinds, enough, empty⟩


end Zlib.Inflate.Proofs
