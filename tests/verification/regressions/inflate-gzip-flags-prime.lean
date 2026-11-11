import ZlibF.Proof.«inflate.c.invariant»

open C Zlib.Inflate Zlib.Inflate.Proofs
set_option autoImplicit false

/-! After `inflateInit2(&strm, 31)`, the gzip magic bytes and two `inflatePrime(&strm, 16, v)`
calls, `FLAGS` stores `(int)hold` with 32 held bits. The real C, built with AddressSanitizer and
UndefinedBehaviorSanitizer, continues with `flags == 65544` (`hold = 0x00010008`) and with a
negative `flags` (`hold = 0x80000008`), and ends the stream with `Z_STREAM_END`
(`tests/regression/inflate-gzip-flags-prime`). `InflatePhase.flags` first stated that `flags` is
-1 or a 16-bit word, so `InflateInv` did not hold on that history. -/
namespace GzipFlagsPrimeRegression

/-- The earlier `flags` clause fails on the value the C stores. -/
theorem earlier_flags_fails (s : InflateState) (flags : s.flags = Int32.ofInt 65544) :
    ¬ (s.flags = -1 ∨ (0 ≤ s.flags.toInt ∧ s.flags.toInt < 65536)) := by
  rw [flags]
  decide

/-- So does it on the negative value. -/
theorem earlier_flags_fails_negative (s : InflateState) (flags : s.flags = Int32.ofInt (-2147483640)) :
    ¬ (s.flags = -1 ∨ (0 ≤ s.flags.toInt ∧ s.flags.toInt < 65536)) := by
  rw [flags]
  decide

end GzipFlagsPrimeRegression

#print axioms GzipFlagsPrimeRegression.earlier_flags_fails
#print axioms GzipFlagsPrimeRegression.earlier_flags_fails_negative
