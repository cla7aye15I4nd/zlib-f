import ZlibF.Proof.«inflate.c.fast-writeback-state»
import ZlibF.Proof.«inflate.c.leave-restore»
import ZlibF.Proof.«inflate.c.default-foundation»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Normalized fast writeback preserves every default invariant clause,
including table contents and construction/history fields. It changes only
the exposed stream bindings and the private held-bit registers. -/
theorem DefaultStateJ.fast_writeback_normalized
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (invariant : DefaultStateJ h r zs z s)
    (l : Zlib.Inffast.L) (input output : BPtr) (ai ao : UInt32) :
    let bits := l.bits - ((l.bits >>> 3) <<< 3)
    let hold := l.hold &&& (((1 : UInt32) <<< bits) - 1).toUInt64
    let zNext := { z with next_in := input, next_out := output, avail_in := ai, avail_out := ao }
    let sNext := { s with hold, bits }
    DefaultStateJ (setI (r.put h zNext) zs sNext) r zs zNext sNext ∧
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
    invariant.window, invariant.wrapper,
    HeaderMemory.records invariant.header invariant.good normalized.1 rfl rfl
      (fun _ => by simp only [setI, ZStreamRef.put_gzheaders]) sizes
      (fun ref => by rw [byte_view_ro_setI, byte_view_ro_stream_put]), invariant.modes,
    invariant.trailer, ?_, sizes.platform invariant.platform⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩,
    normalized.2.1, normalized.2.2⟩
  simpa only [LibraryGlobals, setI, ZStreamRef.put_static] using invariant.globals

#print axioms DefaultStateJ.fast_writeback_normalized
end Zlib.Inflate.Proofs
