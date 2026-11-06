import ZlibF.Spec.InflateDecodeTableSemantics
import ZlibF.Spec.InflateTableExtent

/-!
# Transporting table meaning across a later constructor

LENS and DISTS share one code array. A semantic result about the first
constructor's array cannot be applied to the second constructor's array
without a frame argument. The returned extent bounds both table reads.
This obligation transports the query itself, including failed queries.
It does not assume or establish a constructor's frame.
-/

namespace Zlib.Inftrees.Spec.DecodeTableFrame
open C Zlib.Inftrees.Spec.DecodeSemantics

/-- Preserving every cell of the first table's returned extent preserves
every two-level query, for inputs of any length. The actual second builder
must supply the cell equality. A capacity bound alone cannot replace it. -/
def Goal.decode_table_read_preserved : Prop :=
  ∀ (type : UInt32) (before after : Array Code) (offset root used : Nat),
    (type = LENS ∨ type = DISTS) →
    TableReadExtent type before offset root used →
    (∀ i, offset ≤ i → i < offset + used → after[i]? = before[i]?) →
    ∀ inp : List Bool,
      tableRead type after offset root inp = tableRead type before offset root inp

end Zlib.Inftrees.Spec.DecodeTableFrame
