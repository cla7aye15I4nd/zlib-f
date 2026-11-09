import ZlibF.Proof.«inflate.c.local-data-invariant»
import ZlibF.Proof.«inflate.c.local-stored»
import ZlibF.Proof.«inflate.c.default-byte-view»
import ZlibF.Proof.«inflate.c.fast-view-caller-cut»
import ZlibF.Proof.«inflate.c.fast-writeback-default-state»

/-! Local decoder representation at the actual fast-call boundaries.
No uniqueness of the caller's older heap records is required. -/
namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inffast.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A size-preserving write to caller storage outside the decoder's window
retains every default decoder clause, including installed table contents and
the platform byte-object bound. -/
theorem LocalStateJ.byte_view_put {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : LocalStateJ h cutoff r zs z s)
    {dest : BRef} {old : Array UInt8} (get : Space.get h dest = some old)
    (write : Space.ro h dest = false)
    (separate : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (array : Array UInt8) (size : array.size = old.size) :
    LocalStateJ (Space.put h dest array) cutoff r zs z s := by
  have good := invariant.good.byte_view_put get write separate array
  have tables : DataTableInvariant (Space.put h dest array) s := by
    intro active
    exact (invariant.tables active).byte_view_put dest array
  have sizes := byte_view_sizes_put get write array size
  have globals : LibraryGlobals (Space.put h dest array) := by
    change (Space.put h dest array).static = _
    rw [byte_view_put_static]
    exact invariant.globals
  exact ⟨⟨good, tables, invariant.pending, invariant.lengths,
      invariant.headerLengths, invariant.held, invariant.window,
      invariant.wrapper, invariant.header, invariant.modes,
      invariant.trailer, globals, sizes.platform invariant.platform⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase, ⟨invariant.roots.stream, invariant.roots.state, invariant.roots.window⟩⟩

/-- The exact stream/state records written by the fast suffix retain
`Good` and establish a normalized, sub-byte bit buffer. -/
theorem fastWriteback_normalized_good {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : LocalGood h cutoff r zs z s)
    (l : Zlib.Inffast.L) (input output : BPtr) (ai ao : UInt32) :
    let bits := l.bits - ((l.bits >>> 3) <<< 3)
    let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
    let z' := { z with next_in := input, next_out := output, avail_in := ai, avail_out := ao }
    let s' := { s with hold, bits }
    LocalGood (setI (r.put h z') zs s') cutoff r zs z' s' ∧
      bits.toNat < 8 ∧ hold.toNat < 2 ^ bits.toNat := by
  dsimp only
  have bits := fastResidualBits_eq_mod l.bits
  have small : (l.bits - ((l.bits >>> 3) <<< 3)).toNat < 8 := by omega
  refine ⟨good.setZI rfl good.live.zalloc good.live.zfree rfl good.live.mode ?_,
    small, normalized_hold_lt _ _ (by omega)⟩
  have win := good.inv.win
  refine ⟨good.inv.wf, ⟨win.wbits, win.block, win.nullws, win.ws, win.hv, win.wn, win.eq⟩,
    good.inv.reqbits, ?_, good.inv.ptr⟩
  change (l.bits - ((l.bits >>> 3) <<< 3)).toNat ≤ 39
  omega

/-- Normalized fast writeback preserves every default invariant clause,
including table contents and construction/history fields. It changes only
the exposed stream bindings and the private held-bit registers. -/
theorem LocalStateJ.fast_writeback_normalized
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : LocalStateJ h cutoff r zs z s)
    (l : Zlib.Inffast.L) (input output : BPtr) (ai ao : UInt32) :
    let bits := l.bits - ((l.bits >>> 3) <<< 3)
    let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
    let zNext := { z with next_in := input, next_out := output, avail_in := ai, avail_out := ao }
    let sNext := { s with hold, bits }
    LocalStateJ (setI (r.put h zNext) zs sNext) cutoff r zs zNext sNext ∧
      bits.toNat < 8 ∧ hold.toNat < 2 ^ bits.toNat := by
  dsimp only
  let bits := l.bits - ((l.bits >>> 3) <<< 3)
  let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
  let zNext : ZStream := { z with
    next_in := input, next_out := output, avail_in := ai, avail_out := ao }
  let sNext : InflateState := { s with hold, bits }
  have normalized := fastWriteback_normalized_good invariant.good l input output ai ao
  have state : (r.put h zNext).istates zs = some s := by
    rw [ZStreamRef.put_istates]
    exact invariant.good.live.hs
  have tables : DataTableInvariant (setI (r.put h zNext) zs sNext) sNext := by
    intro active
    have old := invariant.tables active
    constructor
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.lengthTable
      refine ⟨ref, offset, array, pointer, ?_, safe⟩
      rw [code_views_set_bits state, code_views_put_stream]
      exact get
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.distanceTable
      refine ⟨ref, offset, array, pointer, ?_, safe⟩
      rw [code_views_set_bits state, code_views_put_stream]
      exact get
  have sizes : ByteViewSizes h (setI (r.put h zNext) zs sNext) :=
    (byte_view_sizes_stream_put h r zNext).trans (byte_view_sizes_setI _ zs sNext)
  refine ⟨⟨⟨normalized.1, tables,
    ⟨invariant.pending.sane, invariant.pending.lenext, invariant.pending.dist,
      invariant.pending.distext, invariant.pending.matching⟩,
    invariant.lengths, invariant.headerLengths, normalized.2.2,
    invariant.window, invariant.wrapper, invariant.header, invariant.modes,
    invariant.trailer, ?_, sizes.platform invariant.platform⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase, ⟨invariant.roots.stream, invariant.roots.state, invariant.roots.window⟩⟩,
    normalized.2.1, normalized.2.2⟩
  simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals

/-- RESTORE preserves representation and pending scalar clauses. The bit
count and held-bit premises come from the actual dispatch relation. -/
theorem leave_restore_invariant {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (good : LocalGood h cutoff r zs z s) (pending : DataPendingInvariant s)
    (B : BitInv h l bs) (bits : l.bits.toNat ≤ 39) :
    LocalGood (setI (r.put h (leaveStream z l)) zs (leaveState s l)) cutoff r zs (leaveStream z l) (leaveState s l) ∧
      DataPendingInvariant (leaveState s l) ∧
      (leaveState s l).hold.toNat < 2 ^ (leaveState s l).bits.toNat ∧
      ByteViewSizes h (setI (r.put h (leaveStream z l)) zs (leaveState s l)) := by
  have stateInv : StInv h zs (leaveState s l) :=
    good.inv.of_fields rfl rfl rfl rfl rfl rfl rfl rfl rfl bits rfl rfl rfl
  have finalGood := good.setZI (stream := leaveStream z l) (state := leaveState s l)
    rfl good.live.zalloc good.live.zfree rfl (by exact good.live.mode) stateInv
  exact ⟨finalGood, ⟨pending.sane, pending.lenext, pending.dist, pending.distext, pending.matching⟩, B.hold_lt,
    (byte_view_sizes_stream_put h r (leaveStream z l)).trans (byte_view_sizes_setI _ zs (leaveState s l))⟩

/-- The actual RESTORE prefix establishes the synchronized default callee
state from the dispatch invariant and its bit registers. -/
theorem LocalStateJ.leave_restore
    {c : Ctx} {l : IL} {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} {bs : List UInt8}
    (E : Env c h r zs z s) (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r l bs) (bits : l.bits.toNat ≤ 39) :
    LocalStateJ (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      cutoff r zs (leaveStream z l) (leaveState s l) ∧
    DispatchBuffers (setI (r.put h (leaveStream z l)) zs (leaveState s l)) r l bs := by
  obtain ⟨good, pending, held, sizes⟩ := leave_restore_invariant E invariant.good
    invariant.pending buffers.bits bits
  have tables := leave_restore_tables (r := r) (z := z) l invariant.good.live.hs invariant.tables
  have current : LocalStateJ
      (setI (r.put h (leaveStream z l)) zs (leaveState s l))
      cutoff r zs (leaveStream z l) (leaveState s l) := by
    refine ⟨⟨good, tables, pending, invariant.lengths, invariant.headerLengths,
      held, invariant.window, invariant.wrapper, invariant.header, invariant.modes,
      invariant.trailer, ?_, sizes.platform invariant.platform⟩,
      invariant.requestedBits, invariant.requestedWrap, invariant.phase, ⟨invariant.roots.stream, invariant.roots.state, invariant.roots.window⟩⟩
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
  have packet : DispatchBuffers (setI (r.put h (leaveStream z l)) zs (leaveState s l)) r l bs := by
    simpa only [List.drop_zero] using dispatch_advance_both_local buffers invariant.good good rfl
      sizes readonly (used := 0) (made := 0) (inputAdvance_zero l.next).symm (by omega)
      (inputAdvance_zero l.put).symm (by omega) rfl (by simpa using buffers.bits.byte_views views)
  exact ⟨current, packet⟩

/-- At TYPE, updating the diagnostic back counter preserves all default state
clauses and the actual table contents. -/
theorem LocalStateJ.type_set_back
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : LocalStateJ h cutoff r zs z s) (mode : s.mode = TYPE) (back : Int32) :
    LocalStateJ (setI h zs { s with back }) cutoff r zs z { s with back } := by
  have frame : DecodeStateFrame s { s with back } := rfl
  have good := invariant.good.decode_update frame invariant.good.live.mode
  have tables : DataTableInvariant (setI h zs { s with back }) { s with back } := by
    intro active
    exact (invariant.tables active).decode_update invariant.good.live.hs frame
  have pending : DataPendingInvariant { s with back } := by
    refine ⟨invariant.pending.sane, ?_, ?_, ?_, ?_⟩
    all_goals intro active; change s.mode = _ at active; rw [mode] at active; contradiction
  have sizes := byte_view_sizes_setI h zs { s with back }
  exact ⟨⟨good, tables, pending, invariant.lengths, invariant.headerLengths,
    invariant.held, invariant.window, invariant.wrapper, invariant.header, invariant.modes,
    invariant.trailer, invariant.globals, sizes.platform invariant.platform⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase, ⟨invariant.roots.stream, invariant.roots.state, invariant.roots.window⟩⟩


end Zlib.Inflate.Local
