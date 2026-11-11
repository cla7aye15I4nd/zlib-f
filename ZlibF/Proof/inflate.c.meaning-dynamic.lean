import ZlibF.Proof.«inflate.c.meaning»
import ZlibF.Proof.Format.Deflate

/-!
# inflate.c: dynamic block header positions

Facts about the header bits held by `.dynamicHeader` positions that the
`TABLE`, `LENLENS` and `CODELENS` steps share: reading more bits keeps the
fields already read, and a causal partial parse that has all its lengths is a
complete `DynamicHeader`.
-/

namespace Zlib.Inflate.Proofs.MeaningDynamic
open C Zlib.Inflate Zlib.Inflate.Proofs ZlibF.Spec
set_option autoImplicit false

/-- The three count fields of a header are kept when more bits are read. -/
theorem counts_append {header more r1 r2 r3 : List Bool} {hlit hdist hclen : Nat}
    (read1 : readBits 5 header = some (hlit, r1)) (read2 : readBits 5 r1 = some (hdist, r2))
    (read3 : readBits 4 r2 = some (hclen, r3)) :
    readBits 5 (header ++ more) = some (hlit, r1 ++ more) ∧
    readBits 5 (r1 ++ more) = some (hdist, r2 ++ more) ∧
    readBits 4 (r2 ++ more) = some (hclen, r3 ++ more) :=
  ⟨Proofs.readBits_append 5 header hlit r1 more read1,
    Proofs.readBits_append 5 r1 hdist r2 more read2,
    Proofs.readBits_append 4 r2 hclen r3 more read3⟩

/-- A partial parse of the code lengths that has read all of them, with the
format checks on the result, completes the header. -/
theorem dynamic_header_of_trace {header r1 r2 r3 r4 : List Bool} {hlit hdist hclen : Nat}
    {cl lens : List Nat}
    (read1 : readBits 5 header = some (hlit, r1)) (read2 : readBits 5 r1 = some (hdist, r2))
    (read3 : readBits 4 r2 = some (hclen, r3)) (counts : DynamicCountsOK hlit hdist)
    (lenLens : readCodeLenLens (hclen + 4) r3 = some (cl, r4))
    (clOK : Acceptable .codeLength cl)
    (trace : ZlibF.Math.CodeLengthPrefix.Trace cl (hlit + 257 + (hdist + 1)) [] r4 lens)
    (all : lens.length = hlit + 257 + (hdist + 1))
    (eob : HasEndOfBlock (lens.take (hlit + 257)))
    (litOK : Acceptable .litLen (lens.take (hlit + 257)))
    (distOK : Acceptable .dist (lens.drop (hlit + 257))) :
    DynamicHeader header (lens.take (hlit + 257)) (lens.drop (hlit + 257)) := by
  have done : CodeLens cl (hlit + 257 + (hdist + 1)) lens [] [] lens := CodeLens.done all
  have whole := trace [] [] lens done
  rw [List.append_nil] at whole
  exact ⟨hlit, hdist, hclen, r1, r2, r3, r4, cl, lens, read1, read2, read3, counts, lenLens,
    clOK, whole, eob, litOK, distOK, rfl, rfl⟩

end Zlib.Inflate.Proofs.MeaningDynamic
