import ZlibF.Proof.«inflate.c.slow-short-code-wait»
import ZlibF.Proof.«inflate.c.slow-short-distance-wait»
import ZlibF.Proof.«inflate.c.slow-future-distance-phase»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
set_option autoImplicit false

/-- Actual LEN_ either waits with the source-installed LEN/back-zero
state or reaches LENEXT with syntax produced from the independent future.
There is no current-input code-width or whole-token premise. -/
theorem LEN_future_fragment_progress {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {ref : CodeRef} {offset extent : Nat} {ca : Array Code}
    {L D : List Nat} {p : CopySyntax L D} {l : IL} {bs : List UInt8} {future : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.lencode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv LENS ca offset s.lenbits.toNat extent L)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery LENS ca offset s.lenbits.toNat)
    (B : BitInv h l bs) (source : FutureSource l bs future p.input)
    (slow : ¬ (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    (∃ regs state,
      InputWait (inflate_LEN_ c) h (setI h zs state) l bs future p.input regs ∧
      Good (setI h zs state) r zs z state ∧ DataTablesSafe (setI h zs state) state ∧
      PendingSyntax p state p.input ∧ state = {s with mode := LEN, back := 0}) ∨
    (∃ regs used after state,
      runX (inflate_LEN_ c) l h = runX (inflate_LENEXT c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = LENEXT ∧ PendingSyntax p state p.r1 ∧
      FutureSource regs (bs.drop used) future p.r1 ∧
      SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ DecodeStateFrame s state ∧ after = setI h zs state) := by
  by_cases fits : L.getD p.symbol 0 ≤ (stream l bs).length
  · exact Or.inr (LEN_future_phase E good tables pointer tableGet meaning stable B source fits slow)
  · let state := {s with mode := LEN, back := (0 : Int32)}
    let heap := setI h zs state
    have current : Good heap r zs z state := good.decode_update rfl (by change HEAD ≤ LEN ∧ LEN ≤ SYNC; decide)
    have currentTables : DataTablesSafe heap state := tables.decode_update good.live.hs rfl
    have currentGet : Space.get heap ref = some ca := by
      rw [decode_code_views good.live.hs (after := state) rfl]; exact tableGet
    have safe : LenTableSafe ca offset s.lenbits.toNat := by
      obtain ⟨otherRef, otherOffset, otherArray, otherPointer, otherGet, safe⟩ := tables.lengthTable
      rw [pointer] at otherPointer
      cases otherPointer
      have same := Option.some.inj (tableGet.symm.trans otherGet)
      subst otherArray
      exact safe
    obtain ⟨regs, wait⟩ := lenLookup_short_future E.st current.live.hs pointer currentGet safe meaning stable
      (B.decode_update zs state) source p.lengthDecode (by simpa only [ValidSymbol, ite_true] using p.lengthUpper)
      (by omega)
    have actual : runX (inflate_LEN_ c) l h = .ok ((.error Ex.leave, regs), heap) := by
      unfold inflate_LEN_
      rw [runX_bind, runX_setMode E]
      change runX (inflate_LEN c) l (setI h zs {s with mode := LEN}) = _
      rw [inflate_LEN_slow_cut slow, lenSlow_split, runX_bind]
      have env0 : Env c (setI h zs {s with mode := LEN}) r zs z {s with mode := LEN} :=
        ⟨E.strm, E.st, by simpa using E.hz, by simp⟩
      rw [runX_wrS env0]
      change runX (do lenLookup c; lenFinish c) l (setI (setI h zs {s with mode := LEN}) zs state) = _
      rw [setI_setI, runX_bind, wait.actual]
    exact Or.inl ⟨regs, state, {wait with actual := actual}, current, currentTables, .len (Or.inl rfl), rfl⟩

/-- DIST has the same complete wait/progress classification on the
independent future. All stored length/was fields are produced earlier. -/
theorem DIST_future_fragment_progress {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {ref : CodeRef} {offset extent : Nat} {ca : Array Code}
    {L D : List Nat} {p : CopySyntax L D} {l : IL} {bs : List UInt8} {future : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat extent D)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat)
    (B : BitInv h l bs) (phase : PendingSyntax p s p.r2) (mode : s.mode = DIST)
    (source : FutureSource l bs future p.r2) (lengthWidth : L.getD p.symbol 0 ≤ 15) :
    (∃ regs, InputWait (inflate_DIST c) h h l bs future p.r2 regs) ∨
    (∃ regs used after state,
      runX (inflate_DIST c) l h = runX (inflate_DISTEXT c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = DISTEXT ∧ PendingSyntax p state p.r3 ∧
      FutureSource regs (bs.drop used) future p.r3 ∧
      SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ DecodeStateFrame s state ∧ after = setI h zs state) := by
  by_cases fits : D.getD p.distanceSymbol 0 ≤ (stream l bs).length
  · exact Or.inr (DIST_future_phase E good tables pointer tableGet meaning stable B phase mode source lengthWidth fits)
  · have safe : DistTableSafe ca offset s.distbits.toNat := by
      obtain ⟨otherRef, otherOffset, otherArray, otherPointer, otherGet, safe⟩ := tables.distanceTable
      rw [pointer] at otherPointer
      cases otherPointer
      have same := Option.some.inj (tableGet.symm.trans otherGet)
      subst otherArray
      exact safe
    obtain ⟨regs, wait⟩ := distLookup_short_future E.st good.live.hs pointer tableGet safe meaning stable B source
      p.distanceDecode (by simpa only [ValidSymbol, show DISTS ≠ LENS by decide, ite_false] using p.distanceUpper) (by omega)
    left
    refine ⟨regs, {wait with actual := ?_}⟩
    rw [inflate_DIST_lookup_cut, runX_bind, wait.actual]

#print axioms LEN_future_fragment_progress
#print axioms DIST_future_fragment_progress
end Zlib.Inflate.Proofs.SlowInputFragment
