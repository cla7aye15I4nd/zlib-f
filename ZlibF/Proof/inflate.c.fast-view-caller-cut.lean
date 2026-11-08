import ZlibF.Proof.«inflate.c.fast-view-public-accounting»
import ZlibF.Proof.«inflate.c.fast-buffers»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual RESTORE prefix establishes the synchronized default callee
state from the dispatch invariant and its bit registers. -/
theorem DefaultStateJ.leave_restore
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39) :
    DefaultStateJ (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      r zs (leaveStream z l) (leaveState s l) ∧
    DispatchBuffers (setI (r.put h (leaveStream z l)) zs (leaveState s l)) r l bs := by
  obtain ⟨good, pending, held, sizes⟩ := leave_restore_invariant E invariant.good
    invariant.pending buffers.bits bits
  have tables := leave_restore_tables (r := r) (z := z) l invariant.good.live.hs invariant.tables
  have current : DefaultStateJ
      (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      r zs (leaveStream z l) (leaveState s l) := by
    refine ⟨⟨good, tables, pending, invariant.lengths, invariant.headerLengths,
      held, invariant.window, invariant.wrapper, invariant.header, invariant.modes,
      invariant.trailer, ?_, sizes.platform invariant.platform⟩,
      invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩
    simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals
  have views : ∀ ref : BRef,
      (Space.get (setI (r.put h (leaveStream z l)) zs (leaveState s l)) ref :
        Option (Array UInt8)) = Space.get h ref := by
    intro ref
    rw [byte_view_get_setI, byte_view_get_stream_put]
  have readonly : ∀ ref : BRef,
      Space.ro (setI (r.put h (leaveStream z l)) zs (leaveState s l)) ref =
        Space.ro h ref := by
    intro ref
    rw [byte_view_ro_setI, byte_view_ro_stream_put]
  exact ⟨current, buffers.byte_views invariant.good good rfl views readonly⟩

/-- The real fast LEN branch calls the proved general-view callee after
its actual RESTORE. This source cut admits disjoint slices in one object. -/
theorem inflate_LEN_fast_view_cut
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ after zNext sNext used made,
      runX (inflate_LEN c) l h = runX (inflateAfterFast c) l after ∧
      DefaultStateJ after r zs zNext sNext ∧
      StreamAccounting (leaveStream z l) zNext used made := by
  have bitBound : l.bits.toNat ≤ 39 := by
    have facts : (6 ≤ l.have_ ∧ 258 ≤ l.left) ∧ l.bits < 8 := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using fast
    have small : l.bits.toNat < 8 := by simpa using UInt32.lt_iff_toNat_lt.mp facts.2
    omega
  obtain ⟨restored, packet⟩ := invariant.leave_restore E buffers bitBound
  obtain ⟨after, zNext, sNext, used, made, call, current, accounting⟩ :=
    inflate_fast_default_view_public_core restored packet mode rfl rfl rfl rfl rfl rfl fast
  have execution : Zlib.Inffast.inflate_fast c.strm l.out_
      (setI (r.put h (leaveStream z l)) zs (leaveState s l)) = .ok ((), after) := by
    rw [E.strm]
    exact call
  refine ⟨after, zNext, sNext, used, made, ?_, current, accounting⟩
  unfold inflate_LEN
  rw [runX_bind, runX_get]
  simp only [fast, ↓reduceIte]
  rw [runX_bind, RESTORE_pending_run E]
  simp only []
  rw [runX_bind, runX_lift_ok execution]
  rfl

/-- The complete actual fast LEN branch returns for every general caller
byte view admitted by the initialized default dispatch relation. -/
theorem inflate_LEN_fast_view_run
    {c : Ctx} {l : IL} {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r l bs) (mode : DataTableMode s.mode)
    (fast : (l.have_ >= 6 && l.left >= 258 && l.bits < 8) = true) :
    ∃ regs after, runX (inflate_LEN c) l h = .ok ((.ok (), regs), after) := by
  obtain ⟨after, zNext, sNext, used, made, cut, current, accounting⟩ :=
    inflate_LEN_fast_view_cut E invariant buffers mode fast
  have environment : Env c after r zs zNext sNext :=
    ⟨E.strm, E.st, current.good.live.hz, current.good.live.hs⟩
  rw [cut, inflateAfterFast_run environment]
  exact ⟨_, _, rfl⟩

#print axioms DefaultStateJ.leave_restore
#print axioms inflate_LEN_fast_view_cut
#print axioms inflate_LEN_fast_view_run
end Zlib.Inflate.Proofs
