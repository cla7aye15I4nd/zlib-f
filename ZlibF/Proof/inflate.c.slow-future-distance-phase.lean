import ZlibF.Proof.«inflate.c.slow-future-prefix»
import ZlibF.Proof.«inflate.c.slow-distance-pending-fields»
import ZlibF.Proof.«inflate.c.slow-copy-token»
import ZlibF.Proof.«inflate.c.slow-extra-fragment-progress»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs Zlib.Inffast.Spec
open Zlib.Inftrees Zlib.Inftrees.Spec.DecodeSemantics Zlib.Inftrees.Spec.DecodeSoundness
open SlowDistancePendingFields SlowCopyTokenPath
set_option autoImplicit false

/-- A DIST phase exposes the source-installed length, was and back. -/
theorem pending_dist_fields {L D : List Nat} {p : CopySyntax L D} {s : InflateState}
    {residual : List Bool} (mode : s.mode = DIST) (phase : PendingSyntax p s residual) :
    s.length.toNat = lengthBases.getD (p.symbol - 257) 0 + p.lengthValue ∧
    s.was = s.length ∧
    s.back = Int32.ofNat (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0) := by
  cases phase with
  | len selected => rcases selected with selected | selected <;> rw [selected] at mode <;> contradiction
  | lenext selected _ _ _ => rw [selected] at mode; contradiction
  | dist _ length was back => exact ⟨length, was, back⟩
  | distext selected _ _ _ _ _ => rw [selected] at mode; contradiction
  | matching selected _ _ _ _ => rw [selected] at mode; contradiction

/-- Only the distance code must fit the current input. The rest of this
valid copy token may still be entirely in the independent future. -/
theorem DIST_future_phase {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {ref : CodeRef} {offset extent : Nat} {ca : Array Code}
    {L D : List Nat} {p : CopySyntax L D} {l : IL} {bs : List UInt8} {future : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (pointer : s.distcode = .ref ref offset) (tableGet : Space.get h ref = some ca)
    (meaning : Zlib.Inftrees.Spec.DecodeTableInvariant.Inv DISTS ca offset s.distbits.toNat extent D)
    (stable : Zlib.Inftrees.Spec.DecodeTableStability.StableQuery DISTS ca offset s.distbits.toNat)
    (B : BitInv h l bs) (phase : PendingSyntax p s p.r2) (mode : s.mode = DIST)
    (source : FutureSource l bs future p.r2) (lengthWidth : L.getD p.symbol 0 ≤ 15)
    (fits : D.getD p.distanceSymbol 0 ≤ (stream l bs).length) :
    ∃ regs used after state,
      runX (inflate_DIST c) l h = runX (inflate_DISTEXT c) regs after ∧
      used ≤ bs.length ∧ Good after r zs z state ∧ DataTablesSafe after state ∧
      BitInv after regs (bs.drop used) ∧ state.mode = DISTEXT ∧ PendingSyntax p state p.r3 ∧
      FutureSource regs (bs.drop used) future p.r3 ∧
      SymbolRegShape l regs ∧ regs.next = inputAdvance l.next used ∧ DecodeStateFrame s state ∧ after = setI h zs state := by
  obtain ⟨base, was, back⟩ := pending_dist_fields mode phase
  have decoded : decodeSym D (stream l bs ++ future) = some (p.distanceSymbol, p.r3) := by
    rw [source]; exact p.distanceDecode
  obtain ⟨localDecode, suffix⟩ := decodeSym_restrict decoded fits
  have budget := length_symbol_budget (p.symbol - 257) (by have lo := p.lengthLower; have hi := p.lengthUpper; omega)
  obtain ⟨regs, used, after, state, run, _four, bound, finalGood, finalTables, bits, streamEq,
    finalMode, offset, extra, finalBack, frame, shape, cursor, heap, lengthEq, wasEq⟩ :=
    inflate_DIST_symbol_fields_with_pending (L.getD p.symbol 0 + lengthExtras.getD (p.symbol - 257) 0)
      E good tables pointer tableGet meaning stable B back (by omega) localDecode p.distanceUpper
  refine ⟨regs, used, after, state, run, bound, finalGood, finalTables, bits, finalMode,
    .distext finalMode (by rw [lengthEq]; exact base) (by rw [wasEq, lengthEq]; exact was)
      offset extra finalBack, ?_, shape, cursor, frame, heap⟩
  unfold FutureSource
  rw [← streamEq]
  exact suffix.symm

#print axioms pending_dist_fields
#print axioms DIST_future_phase
end Zlib.Inflate.Proofs.SlowInputFragment
