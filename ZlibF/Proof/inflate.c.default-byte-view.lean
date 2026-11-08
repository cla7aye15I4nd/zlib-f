import ZlibF.Proof.«inflate.c.default-state»
import ZlibF.Proof.«inflate.c.match-invariant»
import ZlibF.Proof.«inflate.c.output-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A size-preserving write to caller storage outside the decoder's window
retains every default decoder clause, including installed table contents and
the platform byte-object bound. -/
theorem DefaultStateJ.byte_view_put {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    {dest : BRef} {old : Array UInt8} (get : Space.get h dest = some old)
    (write : Space.ro h dest = false)
    (separate : ∀ w, s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (array : Array UInt8) (size : array.size = old.size) :
    DefaultStateJ (Space.put h dest array) r zs z s := by
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
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

end Zlib.Inflate.Proofs
