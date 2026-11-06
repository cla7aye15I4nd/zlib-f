import ZlibF.Spec.Format.Deflate
import ZlibF.Proof.«inffast.c.copy»

/-!
# Array copying and the independent LZ77 history operation

The array functions describe bytewise writes. The format's copyBack reads
from the growing dictionary-plus-output history. These obligations relate
the two without a heap or an assumption about a translated callee.
-/

namespace ZlibF.Math.LZ77Copy
open C ZlibF.Spec

/-- The count output bytes immediately before the current write offset. -/
def writtenBytes (bytes : Array UInt8) (offset count : Nat) : List UInt8 :=
  (bytes.toList.drop (offset - count)).take count

/-- A potentially overlapping output copy implements copyBack. The source
can read bytes written earlier in this same copy. No length-258 bound is
needed for this heap-free equality. -/
def Goal.output_copy_refines_lz77 : Prop :=
  ∀ (dict : List UInt8) (bytes : Array UInt8) (offset count dist n : Nat),
    count ≤ offset → 0 < dist → dist ≤ count → offset + n ≤ bytes.size →
    writtenBytes (Zlib.Inffast.Proofs.cpyN n (offset - dist) offset bytes)
      (offset + n) (count + n) =
      copyBack dict dist n (writtenBytes bytes offset count)

/-- A saved-window chunk implements copyBack until the source reaches the
current call's output. The pointwise premise is a relation between array
data and history; the actual circular-window proof must establish it. -/
def Goal.window_copy_refines_lz77 : Prop :=
  ∀ (dict : List UInt8) (bytes window : Array UInt8)
    (offset count sourceOffset dist n : Nat),
    count ≤ offset → count < dist → dist ≤ dict.length + count →
    n ≤ dist - count → offset + n ≤ bytes.size → sourceOffset + n ≤ window.size →
    (∀ i, i < n → window.getD (sourceOffset + i) 0 =
      dict.getD (dict.length + count - dist + i) 0) →
    writtenBytes (Zlib.Inffast.Proofs.blitN window n sourceOffset offset bytes)
      (offset + n) (count + n) =
      copyBack dict dist n (writtenBytes bytes offset count)

end ZlibF.Math.LZ77Copy
