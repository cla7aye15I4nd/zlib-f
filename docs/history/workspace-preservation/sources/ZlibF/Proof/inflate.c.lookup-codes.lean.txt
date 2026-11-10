import ZlibF.Proof.«inflate.c.lookup-loop»
import ZlibF.Proof.«inflate.c.input-cursor»
import ZlibF.Proof.«inftrees.c.decoder-safe»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

def codesLookupBody (c : Ctx) : X Bool := do
  let s ← ldInflateState c.st
  let b ← BITS s.lenbits
  let here ← Ptr.index s.lencode (b.toNat : Int)
  modify fun l => { l with here := here }
  if here.bits.toUInt32 <= (← get).bits then return true
  PULLBYTE
  return false

theorem lookup1_codes_eq (c : Ctx) : lookup1 c false = xloopBrk (codesLookupBody c) := rfl

/-- The root lookup executes on the actual table and actual bit mask,
even when fewer than root bits are currently held. -/
theorem codesLookupBody_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} (l : IL)
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (safe : Zlib.Inftrees.Spec.CodeLengthTableSafe ca offset s.lenbits.toNat) :
    let entry := codeLookupValue ca offset s.lenbits.toNat l
    runX (codesLookupBody c) l h =
      if entry.bits.toUInt32 ≤ l.bits then .ok ((.ok true, { l with here := entry }), h)
      else runX (do PULLBYTE; pure false : X Bool) { l with here := entry } h := by
  dsimp only
  have root : s.lenbits.toNat < 32 := by have := safe.2.1; omega
  let mask := l.hold.toUInt32 &&& ((1 : UInt32) <<< s.lenbits - 1)
  have value : mask.toNat = l.hold.toNat % 2 ^ s.lenbits.toNat := BITS_toNat l s.lenbits root
  have inside : offset + mask.toNat < ca.size := by
    have := Nat.mod_lt l.hold.toNat (Nat.two_pow_pos s.lenbits.toNat)
    have := safe.2.2.1
    omega
  have read := Ptr.index_ok (off := offset) (i := mask.toNat) get inside
  have actual : ca[offset + mask.toNat] = codeLookupValue ca offset s.lenbits.toNat l := by
    unfold codeLookupValue
    rw [← value, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem inside, Option.getD_some]
  dsimp only [mask] at read actual
  unfold codesLookupBody
  rw [hc]
  have load : ldInflateState (some (.tab zs)) h = .ok (s, h) := by simp [ldI_eq, hs]
  simp only [runX_bind, runX_lift_ok load, BITS_run l h s.lenbits root,
    runX_modify, runX_get, pointer, runX_lift_ok read, actual]
  by_cases fit : (codeLookupValue ca offset s.lenbits.toNat l).bits.toUInt32 ≤ l.bits
  all_goals simp only [fit, ite_true, ite_false, runX_bind, runX_pure]

private theorem xloopBrk_stop {body : X Bool} {l l' : IL} {h : Heap}
    (run : runX body l h = .ok ((.ok true, l'), h)) :
    runX (xloopBrk body) l h = .ok ((.ok (), l'), h) := by
  have rule := xwhileBrk_run (cond := pure true) (body := body)
    (fun k current heap => k = 1 ∧ current = l ∧ heap = h)
    (fun result current heap => result = .ok () ∧ current = l' ∧ heap = h)
    (by
      intro k current heap inv
      obtain ⟨count, currentEq, heapEq⟩ := inv
      subst current heap
      exact ⟨l, h, rfl, .ok true, l', h, run, rfl, rfl, rfl⟩)
    (by intro current heap inv; have := inv.1; omega)
    (k := 1) ⟨rfl, rfl, rfl⟩ (by decide)
  obtain ⟨result, current, heap, actual, rfl, rfl, rfl⟩ := rule
  exact actual

private theorem xloopBrk_leave {body : X Bool} {l l' : IL} {h : Heap}
    (run : runX body l h = .ok ((.error Ex.leave, l'), h)) :
    runX (xloopBrk body) l h = .ok ((.error Ex.leave, l'), h) := by
  have rule := xwhileBrk_run (cond := pure true) (body := body)
    (fun k current heap => k = 1 ∧ current = l ∧ heap = h)
    (fun result current heap => result = .error Ex.leave ∧ current = l' ∧ heap = h)
    (by
      intro k current heap inv
      obtain ⟨count, currentEq, heapEq⟩ := inv
      subst current heap
      exact ⟨l, h, rfl, .error Ex.leave, l', h, run, rfl, rfl, rfl⟩)
    (by intro current heap inv; have := inv.1; omega)
    (k := 1) ⟨rfl, rfl, rfl⟩ (by decide)
  obtain ⟨result, current, heap, actual, rfl, rfl, rfl⟩ := rule
  exact actual

private theorem xloopBrk_pull_stop {body : X Bool} {l middle final : IL} {h : Heap}
    (first : runX body l h = .ok ((.ok false, middle), h))
    (second : runX body middle h = .ok ((.ok true, final), h)) :
    runX (xloopBrk body) l h = .ok ((.ok (), final), h) := by
  have rule := xwhileBrk_run (cond := pure true) (body := body)
    (fun k current heap => heap = h ∧ ((k = 2 ∧ current = l) ∨ (k = 1 ∧ current = middle)))
    (fun result current heap => result = .ok () ∧ current = final ∧ heap = h)
    (by
      intro k current heap inv
      obtain ⟨heapEq, two | one⟩ := inv
      · subst heap
        obtain ⟨count, currentEq⟩ := two
        subst current
        have zero : k = 1 := by omega
        subst k
        exact ⟨l, h, rfl, .ok false, middle, h, first, rfl, Or.inr ⟨rfl, rfl⟩⟩
      · subst heap
        obtain ⟨count, currentEq⟩ := one
        subst current
        exact ⟨middle, h, rfl, .ok true, final, h, second, rfl, rfl, rfl⟩)
    (by intro current heap inv; rcases inv.2 with inv | inv <;> have := inv.1 <;> omega)
    (k := 2) ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩ (by decide)
  obtain ⟨result, current, heap, actual, rfl, rfl, rfl⟩ := rule
  exact actual

private theorem codeLookupValue_bits {ca : Array Code} {offset root : Nat} (l : IL)
    (safe : Zlib.Inftrees.Spec.CodeLengthTableSafe ca offset root) :
    1 ≤ (codeLookupValue ca offset root l).bits.toNat ∧
      (codeLookupValue ca offset root l).bits.toNat ≤ root := by
  have entry := safe.2.2.2 (l.hold.toNat % 2 ^ root)
    (Nat.mod_lt _ (Nat.two_pow_pos _))
  exact ⟨entry.1, entry.2.1⟩

/-- `for (;;) { here = lencode[BITS(lenbits)]; ... PULLBYTE(); }` in CODELENS.
The constructed code-length table makes the actual lookup terminate after
at most one input byte is pulled. Input exhaustion leaves safely. The held
bit stream is unchanged and the selected entry has a positive bounded width. -/
theorem lookup1_codes_run_cursor {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (safe : Zlib.Inftrees.Spec.CodeLengthTableSafe ca offset s.lenbits.toNat)
    (B : BitInv h l bs) :
    ∃ result l' used,
      runX (lookup1 c false) l h = .ok ((result, l'), h) ∧
      used ≤ 1 ∧ used ≤ bs.length ∧ BitInv h l' (bs.drop used) ∧
      stream l' (bs.drop used) = stream l bs ∧
      l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits, here := l'.here } ∧
      l'.bits.toNat ≤ max l.bits.toNat 14 ∧
      1 ≤ l'.here.bits.toNat ∧ l'.here.bits.toNat ≤ s.lenbits.toNat ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → l'.here.bits.toNat ≤ l'.bits.toNat) ∧
      (result = .error Ex.leave → l'.have_ = 0) ∧
      l'.next = inputAdvance l.next used ∧ l'.bits.toNat = l.bits.toNat + 8 * used := by
  let entry := codeLookupValue ca offset s.lenbits.toNat l
  let read := { l with here := entry }
  have bits := codeLookupValue_bits l safe
  have readB : BitInv h read bs := ⟨B.have_eq, B.next, B.hold_lt⟩
  have entryBound : entry.bits.toNat ≤ s.lenbits.toNat := bits.2
  have body := codesLookupBody_run l hc hs pointer get safe
  change runX (codesLookupBody c) l h =
    if entry.bits.toUInt32 ≤ l.bits then .ok ((.ok true, read), h)
    else runX (do PULLBYTE; pure false : X Bool) read h at body
  rw [lookup1_codes_eq]
  by_cases fit : entry.bits.toUInt32 ≤ l.bits
  · rw [if_pos fit] at body
    have enough : entry.bits.toNat ≤ l.bits.toNat := by
      have := UInt32.le_iff_toNat_le.mp fit
      simpa only [UInt8.toNat_toUInt32] using this
    refine ⟨.ok (), read, 0, xloopBrk_stop body, by omega, by omega, ?_, rfl,
      rfl, by dsimp only [read]; omega, bits.1, bits.2, Or.inl rfl,
      fun _ => enough, ?_, (inputAdvance_zero l.next).symm, by simp only [Nat.mul_zero, Nat.add_zero]; rfl⟩
    · simpa only [List.drop_zero] using readB
    · intro impossible
      cases impossible
  · rw [if_neg fit] at body
    have short : l.bits.toNat < entry.bits.toNat := by
      have := (not_congr UInt32.le_iff_toNat_le).mp fit
      simp only [UInt8.toNat_toUInt32] at this
      omega
    have root : s.lenbits.toNat ≤ 7 := safe.2.1
    cases bs with
    | nil =>
      have empty : read.have_ = 0 := by
        apply UInt32.toNat_inj.mp
        change l.have_.toNat = 0
        simpa only [List.length_nil] using B.have_eq
      rw [runX_bind, PULLBYTE_zero empty] at body
      refine ⟨.error Ex.leave, read, 0, xloopBrk_leave body, by omega, by omega, ?_, rfl,
        rfl, by dsimp only [read]; omega, bits.1, bits.2, Or.inr rfl, ?_, fun _ => empty, (inputAdvance_zero l.next).symm, by simp only [Nat.mul_zero, Nat.add_zero]; rfl⟩
      · simpa only [List.drop_zero] using readB
      · intro impossible
        cases impossible
    | cons b bs =>
      obtain ⟨next, pull, B', sameStream, bitCount, cursor⟩ := PULLBYTE_succ_cursor readB
        (by change l.bits.toNat ≤ 56; omega)
      let middle := pulled read b next
      let finalEntry := codeLookupValue ca offset s.lenbits.toNat middle
      let final := { middle with here := finalEntry }
      have finalBits := codeLookupValue_bits middle safe
      have fits : finalEntry.bits.toUInt32 ≤ middle.bits := by
        apply UInt32.le_iff_toNat_le.mpr
        rw [UInt8.toNat_toUInt32]
        change finalEntry.bits.toNat ≤ (pulled read b next).bits.toNat
        rw [bitCount]
        have bound : finalEntry.bits.toNat ≤ s.lenbits.toNat := finalBits.2
        omega
      have second := codesLookupBody_run middle hc hs pointer get safe
      change runX (codesLookupBody c) middle h =
        if finalEntry.bits.toUInt32 ≤ middle.bits then .ok ((.ok true, final), h)
        else runX (do PULLBYTE; pure false : X Bool) final h at second
      rw [if_pos fits] at second
      rw [runX_bind, pull] at body
      simp only [runX_pure] at body
      have execution := xloopBrk_pull_stop body second
      have streamFinal : stream final bs = stream l (b :: bs) := sameStream
      have bound : final.bits.toNat ≤ max l.bits.toNat 14 := by
        change (pulled read b next).bits.toNat ≤ _
        rw [bitCount]
        change l.bits.toNat + 8 ≤ max l.bits.toNat 14
        have entryBound : entry.bits.toNat ≤ s.lenbits.toNat := bits.2
        omega
      refine ⟨.ok (), final, 1, execution, by omega, by simp, ?_, streamFinal, ?_, bound,
        finalBits.1, finalBits.2, Or.inl rfl, ?_, ?_, cursor, by simpa only [Nat.mul_one] using bitCount⟩
      · exact ⟨B'.have_eq, B'.next, B'.hold_lt⟩
      · rfl
      · intro _
        have enough := UInt32.le_iff_toNat_le.mp fits
        simpa only [UInt8.toNat_toUInt32] using enough
      · intro impossible
        cases impossible

/-- Projection retaining the original lookup interface. -/
theorem lookup1_codes_run {c : Ctx} {h : Heap} {zs : Nat} {s : InflateState}
    {ref : CodeRef} {offset : Nat} {ca : Array Code} {l : IL} {bs : List UInt8}
    (hc : c.st = some (.tab zs)) (hs : h.istates zs = some s)
    (pointer : s.lencode = .ref ref offset) (get : Space.get h ref = some ca)
    (safe : Zlib.Inftrees.Spec.CodeLengthTableSafe ca offset s.lenbits.toNat)
    (B : BitInv h l bs) :
    ∃ result l' used,
      runX (lookup1 c false) l h = .ok ((result, l'), h) ∧
      used ≤ 1 ∧ used ≤ bs.length ∧ BitInv h l' (bs.drop used) ∧
      stream l' (bs.drop used) = stream l bs ∧
      l' = { l with next := l'.next, have_ := l'.have_, hold := l'.hold, bits := l'.bits, here := l'.here } ∧
      l'.bits.toNat ≤ max l.bits.toNat 14 ∧
      1 ≤ l'.here.bits.toNat ∧ l'.here.bits.toNat ≤ s.lenbits.toNat ∧
      (result = .ok () ∨ result = .error Ex.leave) ∧
      (result = .ok () → l'.here.bits.toNat ≤ l'.bits.toNat) ∧
      (result = .error Ex.leave → l'.have_ = 0) := by
  obtain ⟨result, regs, used, run, one, bound, inv, stream, shape, bits, lower, upper,
    kinds, full, empty, _, _⟩ := lookup1_codes_run_cursor hc hs pointer get safe B
  exact ⟨result, regs, used, run, one, bound, inv, stream, shape, bits, lower, upper, kinds, full, empty⟩

end Zlib.Inflate.Proofs
