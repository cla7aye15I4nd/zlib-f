import ZlibF.Proof.«deflate.c.universal-call-assemble»
import ZlibF.Proof.«deflate.c.universal-sequence-safety»

/-!
# deflate.c: the header facts after a `deflate` call, and the sequence facts

Batch C (`SequenceFacts.deflateHeader`). Owner 2's `deflate_call_header` gives `HeaderInv` after any
`deflate` call from `DInv`, `HeaderInv` and `CallFacts`; with it every field of `SequenceFacts` is a
theorem under the two open hypotheses of the call, `TinyOverlay` (`memLevel` 1 and 2) and
`FinishProgress` (the `Z_FINISH` progress clause).
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec
set_option autoImplicit false

/-- **`SequenceFacts.deflateHeader`** from `deflate_call_header`. -/
theorem deflate_header_of (tiny : Block.TinyOverlay) (fp : FinishProgress) : DeflateHeaderFact :=
  fun inv header calls buffers act run inv2 => deflate_call_header tiny fp inv header calls buffers act run inv2

/-- **Every field of `SequenceFacts`**, under the two open hypotheses of the call. -/
theorem sequence_facts_of (tiny : Block.TinyOverlay) (fp : FinishProgress) : SequenceFacts :=
  ⟨deflate_call_of tiny fp, deflate_header_of tiny fp, deflate_calls_of tiny fp⟩

end Zlib.Deflate.Universal.Call
