import ZlibF.Spec.Public.Memory
import ZlibF.Spec.PlatformMemory
import ZlibF.Proof.«inflate.c.base»
import ZlibF.Proof.«deflate.c.base»

namespace ZlibF.Spec.Public
open C ZlibF.Spec

def compressRejected (dest : BPtr) (capacity : Option UInt64) (source : BPtr) (n : UInt64) : Prop :=
  capacity = none ∨ (source = .null ∧ n ≠ 0) ∨
    ∃ c, capacity = some c ∧ dest = .null ∧ c ≠ 0

def CompressArguments (h : Heap) (dest : BPtr) (capacity : Option UInt64)
    (source : BPtr) (n : UInt64) (xs : List UInt8) : Prop :=
  compressRejected dest capacity source n ∨
  ∃ c, capacity = some c ∧ Bytes h source n.toNat xs ∧ Writable h dest c.toNat ∧
    Separate source n.toNat dest c.toNat

/-- **Safety of a compressor entry** (the safety half of `CompressorContract`, for the
safety-only scope of `docs/progress.md`): the call returns without a fault, writes only the
destination within its capacity (`Store`, with exactly the same objects otherwise), releases
every temporary allocation, reports an allocation failure only after one happened, and refuses
the rejected arguments without a write. The data relation `Api.Compress2Z` of
`CompressorContract` is not part of it. -/
def CompressorSafety
    (program : BPtr → Option UInt64 → BPtr → UInt64 → M (Int32 × Option UInt64))
    (nullableLength : Bool) : Prop :=
  ∀ h dest capacity source n xs,
    Fresh h → Zlib.Deflate.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    (nullableLength = false → capacity ≠ none) →
    CompressArguments h dest capacity source n xs →
    ∃ rc stored after out expected,
      C.run (program dest capacity source n) h = .ok ((rc, stored), after) ∧
      Store h dest out expected ∧ SameObjectsUpToTableShape expected after ∧
      out.length ≤ (capacity.getD 0).toNat ∧
      (rc = Z_MEM_ERROR → AllocationFailed h after) ∧
      (compressRejected dest capacity source n →
        rc = Z_STREAM_ERROR ∧ stored = capacity ∧ out = [] ∧ after = h)

/-- Scalar cells are separate from data buffers and from each other. This is the explicit
scalar-alias representation limit recorded in `docs/deviations.md`. -/
def UtilitySeparation (dest : BPtr) (capacity : Nat) (source : BPtr) (n : Nat)
    (destLen sourceLen : BPtr) : Prop :=
  Separate dest capacity source n ∧ Separate destLen 8 dest capacity ∧
  Separate destLen 8 source n ∧ Separate sourceLen 8 dest capacity ∧
  Separate sourceLen 8 source n ∧ Separate destLen 8 sourceLen 8

/-! ## Safety of decompression on buffers

The safety goals: for every input the functional goals admit, the call runs
without undefined behaviour and terminates (`C.run … = .ok`), refuses the
argument errors without a change, writes only the output buffer (at most its
capacity) and the length cells, frees every allocation on every return path
(`SameObjectsUpToTableShape` with the stored heap), returns one of the documented
codes, and reports `Z_MEM_ERROR` only after an allocation failed. They say
nothing about the bytes written (the format is in `Goal.uncompress*`).
Statement test: `tests/goals/uncompress-safety` (evidence, not proof). -/

/-- Safety of counted decompression (`uncompress2_z`, `uncompress2`). The premises are
those of `UncompressCounted`. -/
def UncompressCountedSafe
    (program : BPtr → BPtr → BPtr → BPtr → M Int32) (nullableLengths : Bool) : Prop :=
  ∀ h dest destLen source sourceLen capacity n src,
    Fresh h → Zlib.Inflate.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    (destLen ≠ .null → LengthCell h destLen capacity) →
    (sourceLen ≠ .null → LengthCell h sourceLen n) →
    (nullableLengths = false → destLen ≠ .null ∧ sourceLen ≠ .null) →
    (source ≠ .null → Bytes h source n.toNat src) →
    (dest ≠ .null → Writable h dest capacity.toNat) →
    UtilitySeparation dest capacity.toNat source n.toNat destLen sourceLen →
    ∃ rc after, C.run (program dest destLen source sourceLen) h = .ok (rc, after) ∧
      (sourceLen = .null ∨ destLen = .null ∨ (source = .null ∧ n ≠ 0) ∨
        (dest = .null ∧ capacity ≠ 0) → rc = Z_STREAM_ERROR ∧ SameObjectsUpToTableShape h after) ∧
      (sourceLen ≠ .null → destLen ≠ .null →
        (source = .null → n = 0) → (dest = .null → capacity = 0) →
        ∃ out got consumed h₁ h₂ expected,
          Store h dest out h₁ ∧ Store h₁ sourceLen (lengthBytes consumed) h₂ ∧
          Store h₂ destLen (lengthBytes got) expected ∧ SameObjectsUpToTableShape expected after ∧
          out.length ≤ capacity.toNat ∧ consumed.toNat ≤ n.toNat ∧
          (rc = Z_OK ∨ rc = Z_BUF_ERROR ∨ rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR) ∧
          (got.toNat = out.length ∨ (rc = Z_MEM_ERROR ∧ out = [] ∧ got = capacity ∧ consumed = n)) ∧
          (rc = Z_MEM_ERROR → AllocationFailed h after))

/-- Safety of the single-length wrappers (`uncompress_z`, `uncompress`). The premises are those
of `UncompressSingle`. -/
def UncompressSingleSafe (program : BPtr → BPtr → BPtr → UInt64 → M Int32)
    (nullableLength : Bool) : Prop :=
  ∀ h dest destLen source capacity n src,
    Fresh h → Zlib.Inflate.Spec.Uniq h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    (destLen ≠ .null → LengthCell h destLen capacity) →
    (nullableLength = false → destLen ≠ .null) →
    (source ≠ .null → Bytes h source n.toNat src) →
    (dest ≠ .null → Writable h dest capacity.toNat) →
    Separate source n.toNat dest capacity.toNat →
    Separate destLen 8 dest capacity.toNat → Separate destLen 8 source n.toNat →
    ∃ rc after, C.run (program dest destLen source n) h = .ok (rc, after) ∧
      (destLen = .null ∨ (source = .null ∧ n ≠ 0) ∨ (dest = .null ∧ capacity ≠ 0) →
        rc = Z_STREAM_ERROR ∧ SameObjectsUpToTableShape h after) ∧
      (destLen ≠ .null → (source = .null → n = 0) → (dest = .null → capacity = 0) →
        ∃ out got h₁ expected,
          Store h dest out h₁ ∧ Store h₁ destLen (lengthBytes got) expected ∧
          SameObjectsUpToTableShape expected after ∧ out.length ≤ capacity.toNat ∧
          (rc = Z_OK ∨ rc = Z_BUF_ERROR ∨ rc = Z_DATA_ERROR ∨ rc = Z_MEM_ERROR) ∧
          (got.toNat = out.length ∨ (rc = Z_MEM_ERROR ∧ out = [] ∧ got = capacity)) ∧
          (rc = Z_MEM_ERROR → AllocationFailed h after))

end ZlibF.Spec.Public
