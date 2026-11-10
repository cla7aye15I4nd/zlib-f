import ZlibF.Proof.«inflate.c.slow-token-leaf-events»
import ZlibF.Proof.«inflate.c.slow-raw-public-leave»
namespace Zlib.Inflate.Proofs.SlowTokenPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowInputFragment
set_option autoImplicit false

/-- All previously proved copy phases depend only on retained scalar
fields, not held bits, physical window geometry or public counters. -/
theorem pending_fields {L D : List Nat} {p : CopySyntax L D} {s state : InflateState} {residual : List Bool}
    (phase : PendingSyntax p s residual) (fields : PendingFieldsFrame s state) : PendingSyntax p state residual := by
  obtain ⟨modeEq, lengthEq, wasEq, offsetEq, extraEq, backEq⟩ := fields
  cases phase with
  | len mode => exact .len (mode.elim (fun selected => Or.inl (modeEq.trans selected)) (fun selected => Or.inr (modeEq.trans selected)))
  | lenext mode length extra back =>
    exact .lenext (modeEq.trans mode) (by rw [lengthEq]; exact length)
      (by rw [extraEq]; exact extra) (backEq.trans back)
  | dist mode length was back =>
    exact .dist (modeEq.trans mode) (by rw [lengthEq]; exact length)
      (by rw [wasEq, lengthEq]; exact was) (backEq.trans back)
  | distext mode length was offset extra back =>
    exact .distext (modeEq.trans mode) (by rw [lengthEq]; exact length)
      (by rw [wasEq, lengthEq]; exact was) (by rw [offsetEq]; exact offset)
      (by rw [extraEq]; exact extra) (backEq.trans back)
  | matching mode was remaining offset back =>
    exact .matching (modeEq.trans mode) (by rw [wasEq]; exact was)
      (by rw [lengthEq, wasEq]; exact remaining) (by rw [offsetEq]; exact offset) (backEq.trans back)

/-- Real public return scalar frames preserve any token stage, including
LIT waiting for one byte of output, without a copy-only ghost. -/
theorem TokenPhase.fields {L D : List Nat} {token : TokenSyntax L D}
    {s state : InflateState} {residual : List Bool} (phase : TokenPhase token s residual)
    (fields : PendingFieldsFrame s state) : TokenPhase token state residual := by
  obtain ⟨modeEq, lengthEq, _wasEq, _offsetEq, _extraEq, backEq⟩ := fields
  cases phase with
  | code mode => exact .code (mode.elim (fun selected => Or.inl (modeEq.trans selected)) (fun selected => Or.inr (modeEq.trans selected)))
  | literal mode length back => exact .literal (modeEq.trans mode) (by rw [lengthEq]; exact length) (backEq.trans back)
  | copy phase => exact .copy (pending_fields phase ⟨modeEq, lengthEq, _wasEq, _offsetEq, _extraEq, backEq⟩)

/-- Any actual no-output code transition produces the full caller buffer
packet needed for the following LIT/TYPE dispatch or public return. -/
theorem CodePoint.buffers {h after : Heap} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {future residual : List Bool} {r : ZStreamRef} {zs : Nat} {z : ZStream} {used : Nat}
    (good : Good h r zs z s) (buffers : DispatchBuffers h r l bs)
    (point : CodePoint h s l bs future r zs z after state regs used residual) :
    DispatchBuffers after r regs (bs.drop used) := by
  have views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [point.heap, byte_view_get_setI]
  have ro : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [point.heap, byte_view_ro_setI]
  have range := callerRange_transport good point.good (by rw [point.frame]) views ro buffers.output.range
  have usedBound : used ≤ l.have_.toNat := by rw [buffers.bits.have_eq]; exact point.bound
  have count : regs.have_.toNat = l.have_.toNat - used := by rw [point.bits.have_eq, buffers.bits.have_eq, List.length_drop]
  have inputRange := callerRange_advance buffers.input usedBound
  have inputAfter := callerRange_transport good point.good (by rw [point.frame]) views ro inputRange
  refine ⟨?_, ?_, ?_, point.bits⟩
  · rw [point.cursor, count]
    exact inputAfter
  · rw [point.shape]
    exact ⟨range, buffers.output.nonnull, buffers.output.count, buffers.output.produced⟩
  · have put : regs.put = l.put := by rw [point.shape]
    have left : regs.left = l.left := by rw [point.shape]
    rw [point.cursor, count, put, left]
    exact inputAdvance_separate _ _ _ _ _ usedBound buffers.separate

#print axioms pending_fields
#print axioms TokenPhase.fields
#print axioms CodePoint.buffers
end Zlib.Inflate.Proofs.SlowTokenPath
