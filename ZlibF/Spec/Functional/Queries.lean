import ZlibF.Spec.Public.Queries
import ZlibF.Spec.Functional.Api.Compress

/-!
# Queries: functional goals and the definitions only they use

Split from `ZlibF/Spec/Public/Queries.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C

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
