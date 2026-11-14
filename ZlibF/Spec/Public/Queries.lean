import ZlibF.Spec.Public.Calls

/-!
# Complete contracts for pure bounds and public identification queries

These goals name actual translated entries. They have no extra stream invariant or callee
contract hypothesis. Heap equality supplies frame and ownership preservation for the queries.
The numeric bound contract states the returned formula, not compressed-output adequacy.
-/

namespace ZlibF.Spec.Public
open C

/-- A result points to the stated NUL-terminated read-only static string. -/
def StaticString (h : Heap) (p : BPtr) (text : String) : Prop :=
  ∃ i, p = .ref (.str i) 0 ∧
    Space.get h (BRef.str i) = some (text.toUTF8.data.push 0) ∧
    Space.ro h (BRef.str i) = true

/-- Public error text; every integer outside the documented return-code range gives empty text. -/
def errorText : Int → String
  | 2 => "need dictionary"
  | 1 => "stream end"
  | -1 => "file error"
  | -2 => "stream error"
  | -3 => "data error"
  | -4 => "insufficient memory"
  | -5 => "buffer error"
  | -6 => "incompatible version"
  | _ => ""

end ZlibF.Spec.Public
