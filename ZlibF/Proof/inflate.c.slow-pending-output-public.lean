import ZlibF.Proof.«inflate.c.slow-output-public-source»
import ZlibF.Proof.«inflate.c.slow-fragment-logical-history»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowMatchCompletion
set_option autoImplicit false

/-- The produced pending-MATCH syntax and remaining length establish the
actual safety scalar clause. Public callers supply none of these fields. -/
theorem pending_match_safe {L D : List Nat} {p : CopySyntax L D} {s : InflateState}
    (mode : s.mode = MATCH) (phase : PendingSyntax p s p.rest)
    (positive : 0 < s.length.toNat) (sane : s.sane = 1) : DataPendingInvariant s := by
  obtain ⟨was, remaining, offset, _back⟩ := pending_matching_fields mode phase
  obtain ⟨_lo, lengthHi, distanceLo, _distanceHi⟩ := copy_syntax_scalar_bounds p
  refine ⟨sane, ?_, ?_, ?_, ?_⟩
  · intro selected; rw [mode] at selected; contradiction
  · intro selected; rw [mode] at selected; contradiction
  · intro selected; rw [mode] at selected; contradiction
  · intro _
    exact ⟨positive, remaining, by rw [was]; exact lengthHi, by rw [offset]; omega⟩

/-- Actual public leave handles pending output even with unread input.
It returns the same original token and all its remaining scalar fields,
or the genuine window-allocation MEM branch. -/
theorem pending_match_public_leave {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {bs : List UInt8} {future : List Bool}
    (E : Env c h r zs z s) (good : Good h r zs z s) (tables : DataTablesSafe h s)
    (buffers : DispatchBuffers h r l bs) (mode : s.mode = MATCH) (phase : PendingSyntax p s p.rest)
    (source : FutureSource l bs future p.rest) (positive : 0 < s.length.toNat) (sane : s.sane = 1)
    (allocator : z.zalloc = .fn "zcalloc") (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (bits : l.bits.toNat ≤ 39) :
    ∃ rc after stream state, inflate_leave c l h = .ok (rc, after) ∧
      Good after r zs stream state ∧ DataTableInvariant after state ∧ DataPendingInvariant state ∧
      ((PendingSyntax p state p.rest ∧ PendingFieldsFrame s state ∧
        (natBits state.bits.toNat state.hold.toNat ++ bytesBits bs) ++ future = p.rest ∧
        stream.next_in = l.next ∧ stream.avail_in = l.have_) ∨ (rc = Z_MEM_ERROR ∧ state.mode = MEM)) := by
  exact inflate_leave_pending_source E good allocator statics buffers (fun _ => tables)
    (pending_match_safe mode phase positive sane) bits phase source

/-- Logical progress survives the actual source's scalar frame. It keeps
the original output history and emitted-prefix equality across leave. -/
theorem logical_progress_pending_fields {L D : List Nat} {p : CopySyntax L D}
    {dict original current : List UInt8} {s state : InflateState}
    (progress : LogicalCopyProgress p dict original current s) (frame : PendingFieldsFrame s state) :
    LogicalCopyProgress p dict original current state := by
  unfold LogicalCopyProgress at *
  rw [frame.2.1]
  exact progress

/-- Actual Rebuffer preserves both the produced pending MATCH and its
logical emitted-prefix ghost while producing the next actual LOAD view. -/
theorem logical_pending_rebuffer {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z next : ZStream} {s : InflateState} {L D : List Nat} {p : CopySyntax L D}
    {dict original current : List UInt8} {chunk : List UInt8} {later : List Bool}
    (good : Good before r zs z s) (rebuffer : Rebuffer before after r) (tables : DataTableInvariant before s)
    (mode : s.mode = MATCH) (phase : PendingSyntax p s p.rest)
    (progress : LogicalCopyProgress p dict original current s)
    (held : s.hold.toNat < 2 ^ s.bits.toNat)
    (observed : Bytes after next.next_in next.avail_in.toNat chunk)
    (saved : natBits s.bits.toNat s.hold.toNat ++ (bytesBits chunk ++ later) = p.rest) :
    after.istates zs = some s ∧ DataTableInvariant after s ∧ PendingSyntax p s p.rest ∧
      LogicalCopyProgress p dict original current s ∧ BitInv after (dispatchRegs next s) chunk ∧
      FutureSource (dispatchRegs next s) chunk later p.rest := by
  obtain ⟨state, finalTables, _mode, finalPhase, B, source⟩ := pending_match_rebuffer good rebuffer tables mode phase held observed saved
  exact ⟨state, finalTables, finalPhase, progress, B, source⟩

#print axioms pending_match_safe
#print axioms pending_match_public_leave
#print axioms logical_progress_pending_fields
#print axioms logical_pending_rebuffer
end Zlib.Inflate.Proofs.SlowInputFragment
