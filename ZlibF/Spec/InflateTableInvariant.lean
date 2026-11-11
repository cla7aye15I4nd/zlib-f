import ZlibF.Proof.«inflate.c.base»
import ZlibF.Proof.«inffast.c.tableok»

/-!
# The guarded table-safety clause of the decoder invariant

Initialization does not construct data tables. Table facts are required only
while decoding a data block. This clause states safety, not canonical-code
meaning or the complete persistent stream invariant.
-/

namespace Zlib.Inflate.Spec
open C

/-- The actual state pointers resolve to the tables needed by the decoder.
Offsets, widths and arrays are those in the same heap, not independent
tables chosen by an enclosing proof. -/
structure DataTablesSafe (h : Heap) (s : InflateState) : Prop where
  lengthTable : ∃ ref offset ca,
    s.lencode = .ref ref offset ∧ Space.get h ref = some ca ∧
      Zlib.Inffast.Spec.LenTableSafe ca offset s.lenbits.toNat
  distanceTable : ∃ ref offset ca,
    s.distcode = .ref ref offset ∧ Space.get h ref = some ca ∧
      Zlib.Inffast.Spec.DistTableSafe ca offset s.distbits.toNat
  lengthLeaves : ∀ ref offset ca, s.lencode = .ref ref offset → Space.get h ref = some ca →
    Zlib.Inffast.Spec.LenLeavesPositive ca offset s.lenbits.toNat

/-- A frame keeps `lengthLeaves` when the length pointer, its width and the code array it points to are
unchanged. -/
theorem DataTablesSafe.lengthLeaves_frame {h h' : Heap} {s s' : InflateState} (tables : DataTablesSafe h s)
    (lens : s'.lencode = s.lencode) (bits : s'.lenbits = s.lenbits)
    (codes : ∀ (ref : CodeRef) (offset : Nat), s.lencode = .ref ref offset →
      (Space.get h' ref : Option (Array Code)) = Space.get h ref) :
    ∀ ref offset ca, s'.lencode = .ref ref offset → Space.get h' ref = some ca →
      Zlib.Inffast.Spec.LenLeavesPositive ca offset s'.lenbits.toNat := by
  intro ref offset ca pointer get
  rw [lens] at pointer
  rw [codes ref offset pointer] at get
  rw [bits]
  exact tables.lengthLeaves ref offset ca pointer get

/-- These modes retain the current block's data tables, including a
partially emitted literal or match which will resume decoding afterward. -/
def DataTableMode (mode : UInt32) : Prop :=
  mode = LEN_ ∨ mode = LEN ∨ mode = LENEXT ∨ mode = DIST ∨
    mode = DISTEXT ∨ mode = MATCH ∨ mode = LIT

/-- One guarded clause of the proposed persistent safety invariant.
Code-length-table construction needs its own, separate mode clause. -/
def DataTableInvariant (h : Heap) (s : InflateState) : Prop :=
  DataTableMode s.mode → DataTablesSafe h s

end Zlib.Inflate.Spec
