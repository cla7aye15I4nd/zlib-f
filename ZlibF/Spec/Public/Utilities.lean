import ZlibF.Spec.Public.Memory
import ZlibF.Spec.Api.Compress
import ZlibF.Spec.PlatformMemory

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

/-- The four compressor entries share the data relation. Their scalar-pointer domains and
returned scalar types remain separate. No compressor or allocator theorem is assumed.
The accepted LP64 environment bounds each represented byte object by PTRDIFF_MAX;
it does not bound the total stream length. -/
def CompressorContract
    (program : BPtr → Option UInt64 → BPtr → UInt64 → M (Int32 × Option UInt64))
    (level : Int32) (nullableLength : Bool) : Prop :=
  ∀ h dest capacity source n xs,
    Fresh h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    (nullableLength = false → capacity ≠ none) →
    CompressArguments h dest capacity source n xs →
    ∃ rc stored after out expected,
      C.run (program dest capacity source n) h = .ok ((rc, stored), after) ∧
      Store h dest out expected ∧ SameObjects expected after ∧
      (rc = Z_MEM_ERROR → AllocationFailed h after) ∧
      (compressRejected dest capacity source n →
        rc = Z_STREAM_ERROR ∧ stored = capacity ∧ out = [] ∧ after = h) ∧
      (¬ compressRejected dest capacity source n →
        Api.Compress2Z
          { source := xs, capacity := (capacity.getD 0).toNat, level := level.toInt
            sourceNull := source == .null, destNull := dest == .null, lengthNull := false }
          { rc := rc.toInt, produced := out, storedLength := stored.map UInt64.toNat })

/-- `int compress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen, int level)`.
Includes null-cell rejection, unchanged capacity on argument rejection, exact stored length,
valid compressed data, buffer exhaustion, allocation failure, frame and complete cleanup. -/
def Goal.compress2_z : Prop :=
  ∀ level, CompressorContract (fun d c s n => Zlib.Compress.compress2_z d c s n level) level true

/-- `int compress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen, int level)`.
The wrapper reads the length cell before `_z` checks; its length cell must be nonnull. -/
def Goal.compress2 : Prop :=
  ∀ level, CompressorContract (fun d c s n => do
    let (rc, size) ← Zlib.Compress.compress2 d c s n level
    pure (rc, some size)) level false

/-- `int compress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen)`.
The nullable-length `_z` contract at the default compression level. -/
def Goal.compress_z : Prop :=
  CompressorContract Zlib.Compress.compress_z Z_DEFAULT_COMPRESSION true

/-- `int compress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen)`.
The nonnull-length wrapper contract at the default compression level. -/
def Goal.compress : Prop :=
  CompressorContract (fun d c s n => do
    let (rc, size) ← Zlib.Compress.compress d c s n
    pure (rc, some size)) Z_DEFAULT_COMPRESSION false

/-- Observable decompression on buffers. Memory failure can follow output. Buffer exhaustion
does not assert that unused trailing source bytes can extend a valid compressed stream. -/
def Uncompressed (src : List UInt8) (capacity : Nat) (rc : Int32)
    (out : List UInt8) (used : Nat) : Prop :=
  Api.Uncompress2 true src capacity rc.toInt out used

/-- Scalar cells are separate from data buffers and from each other. This is the explicit
scalar-alias representation limit recorded in `docs/deviations.md`. -/
def UtilitySeparation (dest : BPtr) (capacity : Nat) (source : BPtr) (n : Nat)
    (destLen sourceLen : BPtr) : Prop :=
  Separate dest capacity source n ∧ Separate destLen 8 dest capacity ∧
  Separate destLen 8 source n ∧ Separate sourceLen 8 dest capacity ∧
  Separate sourceLen 8 source n ∧ Separate destLen 8 sourceLen 8

/-- Counted decompression retains both length cells on early argument and init failures.
Later memory failure stores the actual output and consumption lengths.
The accepted LP64 byte-object premise includes caller, static and embedded storage. -/
def UncompressCounted
    (program : BPtr → BPtr → BPtr → BPtr → M Int32) (nullableLengths : Bool) : Prop :=
  ∀ h dest destLen source sourceLen capacity n src,
    Fresh h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    (destLen ≠ .null → LengthCell h destLen capacity) →
    (sourceLen ≠ .null → LengthCell h sourceLen n) →
    (nullableLengths = false → destLen ≠ .null ∧ sourceLen ≠ .null) →
    (source ≠ .null → Bytes h source n.toNat src) →
    (dest ≠ .null → Writable h dest capacity.toNat) →
    UtilitySeparation dest capacity.toNat source n.toNat destLen sourceLen →
    ∃ rc after, C.run (program dest destLen source sourceLen) h = .ok (rc, after) ∧
      (sourceLen = .null ∨ destLen = .null ∨ (source = .null ∧ n ≠ 0) ∨
        (dest = .null ∧ capacity ≠ 0) → rc = Z_STREAM_ERROR ∧ SameObjects h after) ∧
      (sourceLen ≠ .null → destLen ≠ .null →
        (source = .null → n = 0) → (dest = .null → capacity = 0) →
        ∃ out used got consumed h₁ h₂ expected,
          Store h dest out h₁ ∧ Store h₁ sourceLen (lengthBytes consumed) h₂ ∧
          Store h₂ destLen (lengthBytes got) expected ∧ SameObjects expected after ∧
          Uncompressed (if source = .null then [] else src) capacity.toNat rc out used ∧
          ((got.toNat = out.length ∧ consumed.toNat = used) ∨
            (rc = Z_MEM_ERROR ∧ out = [] ∧ got = capacity ∧ consumed = n)) ∧
          (rc = Z_MEM_ERROR → AllocationFailed h after))

/-- `int uncompress2_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t *sourceLen)`.
Includes both nullable scalar checks, trailing input, partial output on memory failure and cleanup. -/
def Goal.uncompress2_z : Prop := UncompressCounted Zlib.Uncompr.uncompress2_z true

/-- `int uncompress2(Bytef *dest, uLongf *destLen, const Bytef *source, uLong *sourceLen)`.
Both scalar cells are read by the wrapper before the checked `_z` entry. -/
def Goal.uncompress2 : Prop := UncompressCounted Zlib.Uncompr.uncompress2 false

/-- The single-length wrappers use the same accepted LP64 per-byte-object
scope as counted decompression. Total stream length is not bounded here. -/
def UncompressSingle (program : BPtr → BPtr → BPtr → UInt64 → M Int32)
    (nullableLength : Bool) : Prop :=
  ∀ h dest destLen source capacity n src,
    Fresh h → LibraryGlobals h → ZlibF.PlatformMemory.ByteObjectsFit h →
    (destLen ≠ .null → LengthCell h destLen capacity) →
    (nullableLength = false → destLen ≠ .null) →
    (source ≠ .null → Bytes h source n.toNat src) →
    (dest ≠ .null → Writable h dest capacity.toNat) →
    Separate source n.toNat dest capacity.toNat →
    Separate destLen 8 dest capacity.toNat → Separate destLen 8 source n.toNat →
    ∃ rc after, C.run (program dest destLen source n) h = .ok (rc, after) ∧
      (destLen = .null ∨ (source = .null ∧ n ≠ 0) ∨ (dest = .null ∧ capacity ≠ 0) →
        rc = Z_STREAM_ERROR ∧ SameObjects h after) ∧
      (destLen ≠ .null → (source = .null → n = 0) → (dest = .null → capacity = 0) →
        ∃ out used got h₁ expected,
          Store h dest out h₁ ∧ Store h₁ destLen (lengthBytes got) expected ∧
          SameObjects expected after ∧
          Uncompressed (if source = .null then [] else src) capacity.toNat rc out used ∧
          (got.toNat = out.length ∨ (rc = Z_MEM_ERROR ∧ out = [] ∧ got = capacity)) ∧
          (rc = Z_MEM_ERROR → AllocationFailed h after))

/-- `int uncompress_z(Bytef *dest, z_size_t *destLen, const Bytef *source, z_size_t sourceLen)`.
Only the output length is visible. A null output-length cell is a checked argument error. -/
def Goal.uncompress_z : Prop := UncompressSingle Zlib.Uncompr.uncompress_z true

/-- `int uncompress(Bytef *dest, uLongf *destLen, const Bytef *source, uLong sourceLen)`.
The output-length cell must be readable before the wrapper calls `_z`. -/
def Goal.uncompress : Prop := UncompressSingle Zlib.Uncompr.uncompress false

end ZlibF.Spec.Public
