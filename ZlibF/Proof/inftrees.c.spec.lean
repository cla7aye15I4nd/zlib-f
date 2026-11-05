import ZlibF.Zlib.«inftrees.c»
import ZlibF.Spec.Format.Huffman

/-!
# inftrees.c: what the theorems about `inflate_table` say

`capOf` is the room the caller gives the table (`inftrees.h`: `ENOUGH_LENS`, `ENOUGH_DISTS`; 128 entries for
`CODES`, where the code-length code has at most 7 bits). `Result` is what every exit of `inflate_table` does to
the heap and to the returned values.
-/

namespace Zlib.Inftrees.Spec
open C

/-- The number of `code` entries the caller provides at `*table`: 128 for `CODES` (`1 << 7`), `ENOUGH_LENS` (852) for
`LENS`, `ENOUGH_DISTS` (592) for `DISTS`. -/
def capOf (type : UInt32) : Nat := if type = CODES then 128 else if type = LENS then 852 else 592

/-- The heap and the result after a call, safety part. The call changed only the `unsigned short` array `work` (inside
`[ow, ow + n)`) and the `code` array of the table (inside `[oc, oc + cap)`), through `wa'` and `ca'`; the arrays kept
their sizes. The result is `0` with the table pointer advanced by at most `cap` entries inside the same array, or `1`
(table too large) or `-1` (bad code lengths) with the table pointer and `*bits` as they were passed. -/
def Result (h : Heap) (rw : WRef) (rc : CodeRef) (ow oc cap n : Nat) (wa : Array UInt16) (ca : Array Code)
    (table : CodePtr) (bits : UInt32) (r : Int32 × CodePtr × UInt32) (h' : Heap) : Prop :=
  ∃ wa' ca', h' = Space.put (Space.put h rw wa') rc ca' ∧ wa'.size = wa.size ∧ ca'.size = ca.size ∧
    (∀ x, (x < ow ∨ ow + n ≤ x) → wa'[x]? = wa[x]?) ∧ (∀ x, (x < oc ∨ oc + cap ≤ x) → ca'[x]? = ca[x]?) ∧
    ((r.1 = 0 ∧ ∃ u, u ≤ cap ∧ r.2.1 = .ref rc (oc + u)) ∨ ((r.1 = 1 ∨ r.1 = -1) ∧ r.2.1 = table ∧ r.2.2 = bits))

/-- The first `n` code lengths of `lens` (the array `la` read from offset `ol`), as the specification sees them. -/
def lensList (la : Array UInt16) (ol n : Nat) : List Nat := (List.range n).map (fun k => (la.getD (ol + k) 0).toNat)

/-- The kind of code that `inflate_table` builds for each table type: `CODES` is the code-length code, `LENS` the
literal/length code, `DISTS` the distance code. -/
def kindOf (type : UInt32) : ZlibF.Spec.CodeKind :=
  if type = CODES then .codeLength else if type = LENS then .litLen else .dist

end Zlib.Inftrees.Spec
