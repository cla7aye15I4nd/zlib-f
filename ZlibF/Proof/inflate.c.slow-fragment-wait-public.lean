import ZlibF.Proof.«inflate.c.slow-fragment-parser»
import ZlibF.Proof.«inflate.c.slow-fragment-public-handoff»
namespace Zlib.Inflate.Proofs.SlowInputFragment
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs SlowExtraFragmentProgress SlowExtraSemanticPath
set_option autoImplicit false
set_option maxRecDepth 10000

/-- The source-produced parsing ghost supplies the public safety scalar
clause. No pending-length or original-length hypothesis is added. -/
theorem pending_parser_safe {L D : List Nat} {p : CopySyntax L D} {s : InflateState} {residual : List Bool}
    (phase : PendingSyntax p s residual) (waiting : ParserWaitingMode s) (sane : s.sane = 1)
    (lengthWidth : L.getD p.symbol 0 ≤ 15) (distanceWidth : D.getD p.distanceSymbol 0 ≤ 15) :
    DataPendingInvariant s := by
  obtain ⟨lo, le, budget⟩ := length_base_extra_budget (p.symbol - 257) (by have := p.lengthLower; have := p.lengthUpper; omega)
  have valueBound := readBits_value_bound p.lengthRead
  obtain ⟨dlo, de, dbudget⟩ := distance_base_extra_bounds p.distanceSymbol p.distanceUpper
  refine ⟨sane, ?_, ?_, ?_, ?_⟩
  · intro mode
    obtain ⟨base, extra, back⟩ := lenext_fields mode phase
    exact ⟨by rw [extra]; exact le, by rw [base]; exact lo,
      by rw [base, extra]; exact budget, ⟨_, lengthWidth, back⟩⟩
  · intro mode
    obtain ⟨length, was, back⟩ := pending_dist_fields mode phase
    exact ⟨⟨by rw [length]; omega, by rw [length]; omega, was⟩,
      ⟨_, by omega, back⟩⟩
  · intro mode
    obtain ⟨length, was, offset, extra, back⟩ := distext_fields mode phase
    exact ⟨⟨by rw [length]; omega, by rw [length]; omega, was⟩,
      by rw [extra]; exact de, by rw [offset]; exact dlo,
      by rw [offset, extra]; omega, ⟨_, by omega, back⟩⟩
  · intro mode
    rcases waiting with selected | selected | selected | selected <;> rw [selected] at mode <;> contradiction

/-- A parsing prefix emits no output and changes no byte view or window
ownership. It therefore produces the actual buffers needed by leave. -/
theorem ParsePoint.buffers {L D : List Nat} {p : CopySyntax L D}
    {h after : Heap} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {future residual : List Bool} {r : ZStreamRef} {zs : Nat} {z : ZStream} {used : Nat}
    (good : Good h r zs z s) (buffers : DispatchBuffers h r l bs)
    (point : ParsePoint p h s l bs future r zs z after state regs used residual) :
    DispatchBuffers after r regs (bs.drop used) := by
  have views : ∀ ref : BRef, (Space.get after ref : Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [point.heap, byte_view_get_setI]
  have ro : ∀ ref : BRef, Space.ro after ref = Space.ro h ref := by
    intro ref
    rw [point.heap, byte_view_ro_setI]
  have range := callerRange_transport good point.good (by rw [point.frame]) views ro buffers.output.range
  have usedBound : used ≤ l.have_.toNat := by rw [buffers.bits.have_eq]; exact point.bound
  have count : regs.have_.toNat = l.have_.toNat - used := by
    rw [point.bits.have_eq, buffers.bits.have_eq, List.length_drop]
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

/-- A parsed input-wait packet feeds the actual complete public leave.
The local held-bit bound is the independent safety ledger's existing
input; all semantic phase fields are produced by ParsePoint itself. -/
theorem ParsePoint.wait_public_leave {L D : List Nat} {p : CopySyntax L D}
    {c : Ctx} {h after : Heap} {s state : InflateState} {l regs : IL} {bs : List UInt8}
    {future residual : List Bool} {r : ZStreamRef} {zs : Nat} {z : ZStream} {used : Nat}
    (E : Env c h r zs z s) (good : Good h r zs z s)
    (allocator : z.zalloc = .fn "zcalloc") (statics : Zlib.Crc32.Proofs.StaticsOK h)
    (buffers : DispatchBuffers h r l bs) (sane : s.sane = 1)
    (point : ParsePoint p h s l bs future r zs z after state regs used residual)
    (waiting : ParserWaitingMode state) (empty : regs.have_ = 0) (bits : regs.bits.toNat ≤ 39)
    (lengthWidth : L.getD p.symbol 0 ≤ 15) (distanceWidth : D.getD p.distanceSymbol 0 ≤ 15) :
    ∃ rc final stream saved, inflate_leave c regs after = .ok (rc, final) ∧
      Good final r zs stream saved ∧ DataTableInvariant final saved ∧ DataPendingInvariant saved ∧
      ((PendingSyntax p saved residual ∧ natBits saved.bits.toNat saved.hold.toNat ++ future = residual ∧
        stream.next_in = regs.next ∧ stream.avail_in = 0) ∨ (rc = Z_MEM_ERROR ∧ saved.mode = MEM)) := by
  have currentBuffers := point.buffers good buffers
  have remaining : bs.drop used = [] := by
    apply List.length_eq_zero_iff.mp
    rw [← point.bits.have_eq, empty]
    rfl
  rw [remaining] at currentBuffers
  have currentSource : FutureSource regs [] future residual := by simpa only [remaining] using point.source
  have pending := pending_parser_safe point.phase waiting (by rw [point.frame]; exact sane) lengthWidth distanceWidth
  have env : Env c after r zs z state := ⟨E.strm, E.st, point.good.live.hz, point.good.live.hs⟩
  have currentStatics : Zlib.Crc32.Proofs.StaticsOK after := by
    rw [point.heap]
    exact statics
  exact inflate_leave_pending_input env point.good allocator currentStatics currentBuffers
    (fun _ => point.tables) pending bits point.phase currentSource

#print axioms pending_parser_safe
#print axioms ParsePoint.buffers
#print axioms ParsePoint.wait_public_leave
end Zlib.Inflate.Proofs.SlowInputFragment
