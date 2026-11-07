import ZlibF.Proof.«crc32.c»
import ZlibF.Spec.Public.Checksums

/-! Complete numeric results for the public CRC combination entries. -/

namespace Zlib.Crc32.Proofs
open C Zlib.Crc32

/-- `uLong crc32_combine_gen64(z_off64_t len2)` returns zero for a negative
length; otherwise it returns the independent bitwise polynomial operator. -/
theorem crc32_combine_gen64_public (h : Heap) (hs : StaticsOK h) (len2 : Int64) :
    C.run (crc32_combine_gen64 len2) h = .ok
      ((if len2.toInt < 0 then 0 else
        ((List.range (8 * len2.toInt.toNat)).foldl
          (fun c _ => ZlibF.Spec.crcBit c) (0x80000000 : UInt32)).toUInt64), h) := by
  by_cases hn : len2.toInt < 0
  · simpa [hn, C.run, OkOn] using gen64_neg h len2 hn
  · simpa [hn] using crc32_combine_gen64_correct h hs len2 (by omega)

/-- `uLong crc32_combine_gen(z_off_t len2)` has the same LP64 result. -/
theorem crc32_combine_gen_public (h : Heap) (hs : StaticsOK h) (len2 : Int64) :
    C.run (crc32_combine_gen len2) h = .ok
      ((if len2.toInt < 0 then 0 else
        ((List.range (8 * len2.toInt.toNat)).foldl
          (fun c _ => ZlibF.Spec.crcBit c) (0x80000000 : UInt32)).toUInt64), h) :=
  by
    by_cases hz : len2 = 0
    · subst len2
      rfl
    · exact crc32_combine_gen64_public h hs len2

/-- `uLong crc32_combine64(uLong crc1, uLong crc2, z_off64_t len2)` is total
for all checksum arguments and signed lengths, preserving the heap. -/
theorem crc32_combine64_public (h : Heap) (hs : StaticsOK h)
    (first second : UInt64) (len2 : Int64) :
    C.run (crc32_combine64 first second len2) h = .ok
      ((if len2.toInt < 0 then 0 else
        (((List.range (8 * len2.toInt.toNat)).foldl
          (fun c _ => ZlibF.Spec.crcBit c) first.toUInt32) ^^^ second.toUInt32).toUInt64), h) := by
  have hr := combine64_ok h hs first second len2
  simpa only [C.run, OkOn, pw_foldl] using hr

/-- `uLong crc32_combine(uLong crc1, uLong crc2, z_off_t len2)` has the same LP64 result. -/
theorem crc32_combine_public (h : Heap) (hs : StaticsOK h)
    (first second : UInt64) (len2 : Int64) :
    C.run (crc32_combine first second len2) h = .ok
      ((if len2.toInt < 0 then 0 else
        (((List.range (8 * len2.toInt.toNat)).foldl
          (fun c _ => ZlibF.Spec.crcBit c) first.toUInt32) ^^^ second.toUInt32).toUInt64), h) :=
  crc32_combine64_public h hs first second len2

/-- `uLong crc32_combine_op(uLong crc1, uLong crc2, uLong op)` returns the
independent polynomial result when the operator is generated from any signed length. -/
theorem crc32_combine_op_public (h : Heap) (hs : StaticsOK h)
    (first second : UInt64) (len2 : Int64) :
    C.run (crc32_combine_op first second
      (if len2.toInt < 0 then 0 else
        ((List.range (8 * len2.toInt.toNat)).foldl
          (fun c _ => ZlibF.Spec.crcBit c) (0x80000000 : UInt32)).toUInt64)) h = .ok
      ((if len2.toInt < 0 then 0 else
        (((List.range (8 * len2.toInt.toNat)).foldl
          (fun c _ => ZlibF.Spec.crcBit c) first.toUInt32) ^^^ second.toUInt32).toUInt64), h) := by
  have hg := crc32_combine_gen64_public h hs len2
  have hc := crc32_combine64_public h hs first second len2
  unfold C.run at hg hc ⊢
  unfold crc32_combine64 at hc
  simp only [bind_app, hg] at hc
  exact hc

end Zlib.Crc32.Proofs

namespace ZlibF.Spec.Public.CrcCombineProof

/-- `uLong crc32_combine_gen(z_off_t len2)`; complete operator-generation contract.
The exact public contract, including rejected negative lengths and the unchanged heap. -/
theorem gen : Goal.crc32_combine_gen := by
  intro h length hg
  exact Zlib.Crc32.Proofs.crc32_combine_gen_public h hg length

/-- `uLong crc32_combine_gen64(z_off64_t len2)`; complete operator-generation contract.
The exact public contract, including rejected negative lengths and the unchanged heap. -/
theorem gen64 : Goal.crc32_combine_gen64 := by
  intro h length hg
  exact Zlib.Crc32.Proofs.crc32_combine_gen64_public h hg length

/-- `uLong crc32_combine_op(uLong crc1, uLong crc2, uLong op)`
The exact operator result, including the zero-operator sentinel and the unchanged heap. -/
theorem op : Goal.crc32_combine_op := by
  intro h first second length hg
  exact Zlib.Crc32.Proofs.crc32_combine_op_public h hg first second length

/-- `uLong crc32_combine(uLong crc1, uLong crc2, z_off_t len2)`; full combine contract.
The exact public contract, including rejected negative lengths and the unchanged heap. -/
theorem combine : Goal.crc32_combine := by
  intro h first second length hg
  exact Zlib.Crc32.Proofs.crc32_combine_public h hg first second length

/-- `uLong crc32_combine64(uLong crc1, uLong crc2, z_off64_t len2)`; full combine contract.
The exact public contract, including rejected negative lengths and the unchanged heap. -/
theorem combine64 : Goal.crc32_combine64 := by
  intro h first second length hg
  exact Zlib.Crc32.Proofs.crc32_combine64_public h hg first second length

#print axioms gen
#print axioms gen64
#print axioms op
#print axioms combine
#print axioms combine64
end ZlibF.Spec.Public.CrcCombineProof
