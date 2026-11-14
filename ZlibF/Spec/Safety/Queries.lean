import ZlibF.Spec.Public.Queries

/-!
# Library queries: safety goals

Step 2 of `docs/design/safety-functional-split.md`. On every heap the call returns without a fault
and leaves the heap exactly as it was. The value is the subject of the functional goal.
`compressBound` and `compressBound_z` have no separate safety goal: their translations are pure
functions with no heap and no fault, so such a goal would hold by definition; their full
contracts `Goal.compressBound` and `Goal.compressBound_z` stand for both.
-/

namespace ZlibF.Spec.Public
open C

/-- `const char *zlibVersion(void)`.
**Safety of `zlibVersion`**: on every heap the call returns and the heap is unchanged. -/
def Goal.zlibVersion_safety : Prop :=
  ∀ h : Heap, ∃ p, C.run Zlib.Zutil.zlibVersion h = .ok (p, h)

/-- `uLong zlibCompileFlags(void)`.
**Safety of `zlibCompileFlags`**: on every heap the call returns and the heap is unchanged. -/
def Goal.zlibCompileFlags_safety : Prop :=
  ∀ h : Heap, ∃ v, C.run Zlib.Zutil.zlibCompileFlags h = .ok (v, h)

end ZlibF.Spec.Public
