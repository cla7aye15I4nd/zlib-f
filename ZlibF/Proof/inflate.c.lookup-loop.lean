import ZlibF.Proof.«inflate.c.input-cursor»
import ZlibF.Proof.«inflate.c.xloop-rank»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate
set_option autoImplicit false

def codeLookupValue (ca : Array Code) (offset root : Nat) (l : IL) : Code :=
  ca.getD (offset + l.hold.toNat % 2 ^ root) default

/-- Root lookup changes input and bit registers and the selected entry only. -/
def LookupRegShape (before after : IL) : Prop :=
  after = { before with next := after.next, have_ := after.have_, hold := after.hold, bits := after.bits, here := after.here }

theorem LookupRegShape.refl (l : IL) : LookupRegShape l l := rfl

theorem LookupRegShape.trans {a b c : IL} (first : LookupRegShape a b) (second : LookupRegShape b c) :
    LookupRegShape a c := by
  unfold LookupRegShape at *
  rw [second, first]

/-- A checked table-lookup body either stops on sufficient bits or refills.
This loop rule retains exact input consumption, the selected entry and the
bit stream. Actual lookup bodies must establish the execution equality. -/
theorem lookupLoop_run_cursor {body : X Bool} {h : Heap} {l : IL} {bs : List UInt8}
    (query : IL → Code) (need : Code → UInt32)
    (stable : ∀ current, query { current with here := query current } = query current)
    (bound : ∀ current, (need (query current)).toNat ≤ 15)
    (bodyRun : ∀ current, LookupRegShape l current →
      runX body current h =
        if need (query current) ≤ current.bits then
          .ok ((.ok true, { current with here := query current }), h)
        else runX (do PULLBYTE; pure false : X Bool) { current with here := query current } h)
    (B : BitInv h l bs) :
    ∃ result regs used,
      runX (xloopBrk body) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = query regs ∧ (need regs.here).toNat ≤ 15 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → (need regs.here).toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0) ∧ regs.next = inputAdvance l.next used := by
  let P : IL → Heap → Prop := fun regs heap =>
    heap = h ∧ ∃ used, used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧ regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.next = inputAdvance l.next used
  let Q : Except Ex Unit → IL → Heap → Prop := fun result regs heap =>
    P regs heap ∧ regs.here = query regs ∧
      (need regs.here).toNat ≤ 15 ∧ (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → (need regs.here).toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0)
  have step : ∀ current heap, P current heap → ∃ test regs heap1,
      runX (pure true : X Bool) current heap = .ok ((test, regs), heap1) ∧
      (match test with
       | .error fault => Q (.error fault) regs heap1
       | .ok false => Q (.ok ()) regs heap1
       | .ok true => ∃ result final heap2,
           runX body regs heap1 = .ok ((result, final), heap2) ∧
           (match result with
            | .error fault => Q (.error fault) final heap2
            | .ok true => Q (.ok ()) final heap2
            | .ok false => P final heap2 ∧ 15 - final.bits.toNat < 15 - current.bits.toNat)) := by
    rintro current heap ⟨heapEq, used, usedBound, inv, sameStream, shape, count, bitBound, cursor⟩
    subst heap
    refine ⟨.ok true, current, h, rfl, ?_⟩
    let entry := query current
    let read := { current with here := entry }
    have entryBound : (need entry).toNat ≤ 15 := bound current
    have readInv : BitInv h read (bs.drop used) := ⟨inv.have_eq, inv.next, inv.hold_lt⟩
    have readShape : LookupRegShape l read := shape.trans (by rfl)
    have actual := bodyRun current shape
    change runX body current h =
      if need entry ≤ current.bits then .ok ((.ok true, read), h)
      else runX (do PULLBYTE; pure false : X Bool) read h at actual
    by_cases fits : need entry ≤ current.bits
    · rw [ite_eq_left fits] at actual
      refine ⟨.ok true, read, h, actual, ⟨rfl, used, usedBound, readInv, sameStream, readShape, count, bitBound, cursor⟩,
        (stable current).symm, entryBound, Or.inl rfl, ?_, ?_⟩
      · intro _
        have bound := UInt32.le_iff_toNat_le.mp fits
        exact bound
      · intro impossible
        cases impossible
    · rw [ite_eq_right fits] at actual
      have short : current.bits.toNat < (need entry).toNat := by
        have := (not_congr UInt32.le_iff_toNat_le).mp fits
        omega
      cases remaining : bs.drop used with
      | nil =>
        have empty : read.have_ = 0 := by
          apply UInt32.toNat_inj.mp
          have len := inv.have_eq
          rw [remaining] at len
          exact len
        rw [runX_bind, PULLBYTE_zero empty] at actual
        refine ⟨.error Ex.leave, read, h, actual,
          ⟨rfl, used, usedBound, readInv, sameStream, readShape, count, bitBound, cursor⟩,
          (stable current).symm, entryBound, Or.inr rfl, ?_, fun _ => empty⟩
        intro impossible
        cases impossible
      | cons byte rest =>
        have readCons : BitInv h read (byte :: rest) := by rwa [remaining] at readInv
        obtain ⟨next, pull, nextInv, nextStream, nextBits, nextCursor⟩ := PULLBYTE_succ_cursor readCons
          (by change current.bits.toNat ≤ 56; omega)
        let final := pulled read byte next
        have restEq : bs.drop (used + 1) = rest := by
          have eq : (bs.drop used).drop 1 = rest := by rw [remaining]; rfl
          simpa only [List.drop_drop, Nat.add_comm] using eq
        have usedNext : used + 1 ≤ bs.length := by
          have len := congrArg List.length remaining
          simp only [List.length_drop, List.length_cons] at len
          omega
        have finalInv : BitInv h final (bs.drop (used + 1)) := by rwa [restEq]
        have finalStream : stream final (bs.drop (used + 1)) = stream l bs := by
          rw [restEq, nextStream, ← remaining]
          exact sameStream
        have finalCount : final.bits.toNat = l.bits.toNat + 8 * (used + 1) := by
          rw [nextBits]
          change current.bits.toNat + 8 = _
          rw [count, Nat.mul_add]
          omega
        have finalBound : final.bits.toNat ≤ max l.bits.toNat 22 := by
          rw [nextBits]
          change current.bits.toNat + 8 ≤ _
          omega
        rw [runX_bind, pull] at actual
        simp only [runX_pure] at actual
        refine ⟨.ok false, final, h, actual,
          ⟨rfl, used + 1, usedNext, finalInv, finalStream, readShape.trans (by rfl), finalCount, finalBound, ?_⟩, ?_⟩
        · change next = inputAdvance l.next (used + 1)
          rw [nextCursor]
          change inputAdvance current.next 1 = _
          rw [cursor, inputAdvance_add]
        · rw [nextBits]
          change 15 - (current.bits.toNat + 8) < 15 - current.bits.toNat
          omega
  have initial : P l h := ⟨rfl, 0, by omega, by simpa using B, rfl, LookupRegShape.refl l, by simp, by omega, (inputAdvance_zero l.next).symm⟩
  have fuelBound : 17 < fuel := by decide
  obtain ⟨result, regs, after, run, post, selected, entryBits, kinds, enough, empty⟩ :=
    xwhileBrk_rank P (fun regs _ => 15 - regs.bits.toNat) Q step initial (by change 15 - l.bits.toNat + 2 < fuel; omega)
  obtain ⟨heapEq, used, usedBound, inv, sameStream, shape, count, bitBound, cursor⟩ := post
  subst after
  have atMostTwo : used ≤ 2 := by omega
  exact ⟨result, regs, used, run, atMostTwo, usedBound, inv, sameStream, shape, count, bitBound,
    selected, entryBits, kinds, enough, empty, cursor⟩

/-- Projection retaining the original checked lookup-loop contract. -/
theorem lookupLoop_run {body : X Bool} {h : Heap} {l : IL} {bs : List UInt8}
    (query : IL → Code) (need : Code → UInt32)
    (stable : ∀ current, query { current with here := query current } = query current)
    (bound : ∀ current, (need (query current)).toNat ≤ 15)
    (bodyRun : ∀ current, LookupRegShape l current →
      runX body current h =
        if need (query current) ≤ current.bits then
          .ok ((.ok true, { current with here := query current }), h)
        else runX (do PULLBYTE; pure false : X Bool) { current with here := query current } h)
    (B : BitInv h l bs) :
    ∃ result regs used,
      runX (xloopBrk body) l h = .ok ((result, regs), h) ∧
      used ≤ 2 ∧ used ≤ bs.length ∧ BitInv h regs (bs.drop used) ∧
      stream regs (bs.drop used) = stream l bs ∧ LookupRegShape l regs ∧
      regs.bits.toNat = l.bits.toNat + 8 * used ∧
      regs.bits.toNat ≤ max l.bits.toNat 22 ∧
      regs.here = query regs ∧ (need regs.here).toNat ≤ 15 ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → (need regs.here).toNat ≤ regs.bits.toNat) ∧
      (result = .error Ex.leave → regs.have_ = 0) := by
  obtain ⟨result, regs, used, run, two, usedBound, inv, bits, shape, count, bitBound,
    selected, width, kinds, enough, empty, _⟩ := lookupLoop_run_cursor query need stable bound bodyRun B
  exact ⟨result, regs, used, run, two, usedBound, inv, bits, shape, count, bitBound,
    selected, width, kinds, enough, empty⟩

end Zlib.Inflate.Proofs
