import ZlibF.Spec.Public.Calls
import ZlibF.Spec.Api.Compress

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

/-- `uLong compressBound(uLong sourceLen)`.
Every LP64 input returns the saturated public bound formula. No heap is accessed. -/
def Goal.compressBound : Prop :=
  ∀ n : UInt64, (Zlib.Compress.compressBound n).toNat = Api.compressBound n.toNat

/-- `z_size_t compressBound_z(z_size_t sourceLen)`.
Every LP64 input returns the saturated public bound formula. No heap is accessed. -/
def Goal.compressBound_z : Prop :=
  ∀ n : UInt64, (Zlib.Compress.compressBound_z n).toNat = Api.compressBound n.toNat

/-- `const char *zlibVersion(void)`.
Every heap returns the pinned header's version string, as static read-only storage.
The call terminates without a fault, allocates nothing and changes no heap observation. -/
def Goal.zlibVersion : Prop :=
  ∀ h : Heap, ∃ p,
    C.run Zlib.Zutil.zlibVersion h = .ok (p, h) ∧ StaticString h p ZLIB_VERSION

/-- `uLong zlibCompileFlags(void)`.
The default LP64 build reports sizes 4, 8, 8 and 8 in its four two-bit size fields,
with the default feature flags. Every heap is unchanged and execution does not fault. -/
def Goal.zlibCompileFlags : Prop :=
  ∀ h : Heap, C.run Zlib.Zutil.zlibCompileFlags h = .ok ((1 + 2 * 4 + 2 * 16 + 2 * 64), h)

/-- `const char *zError(int err)`.
Every signed argument returns the public error text as static read-only storage.
Every heap is unchanged; no allocation, leak or runtime fault is permitted. -/
def Goal.zError : Prop :=
  ∀ (h : Heap) (err : Int32), ∃ p,
    C.run (Zlib.Zutil.zError err) h = .ok (p, h) ∧ StaticString h p (errorText err.toInt)

end ZlibF.Spec.Public
