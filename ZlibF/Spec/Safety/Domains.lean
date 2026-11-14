import ZlibF.Spec.Public.Domains

/-!
# Domains: safety goals

Split from `ZlibF/Spec/Public/Domains.lean` without a change of statement or name
(`docs/design/safety-functional-split.md`). The namespace stays `ZlibF.Spec.Public`.
-/

namespace ZlibF.Spec.Public
open C Zlib.GzFs

/-- Every accepted signed window parameter has a non-failing init on every permitted heap.
The fixed witness additionally rules out an empty caller domain. -/
def Goal.inflate_initialisation_domain : Prop :=
  (∀ h r version wb wrap bits,
    InitDomain h r version → Api.inflWbits wb.toInt = some (wrap, bits) →
    h.allocOk h.nalloc = true →
    ∃ after, C.run (Zlib.Inflate.inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r wrap bits ∧ StreamReachable .inflate after r) ∧
  InitDomain witnessHeap (.tab 0) (.ref (.blk 1) 0) ∧
  (∀ wb wrap bits, Api.inflWbits wb.toInt = some (wrap, bits) →
    ∃ after, C.run (Zlib.Inflate.inflateInit2_ (some (.tab 0)) wb (.ref (.blk 1) 0) 112)
      witnessHeap = .ok (Z_OK, after) ∧ InflateInitial witnessHeap after (.tab 0) wrap bits)

/-- Full level, method, window, memory-level and strategy coverage, including normalisation.
No assumption that the post-init invariant already holds is permitted. -/
def Goal.deflate_initialisation_domain : Prop :=
  (∀ h r version level method wb mem strategy p,
    InitDomain h r version →
    Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p →
    (∀ j, j < 5 → h.allocOk (h.nalloc + j) = true) →
    ∃ after, C.run (Zlib.Deflate.deflateInit2_ (some r) level method wb mem strategy version 112) h =
      .ok (Z_OK, after) ∧ DeflateInitial h after r p ∧ StreamReachable .deflate after r) ∧
  InitDomain witnessHeap (.tab 0) (.ref (.blk 1) 0) ∧
  (∀ level method wb mem strategy p,
    Api.deflInit? level.toInt method.toInt wb.toInt mem.toInt strategy.toInt = some p →
    ∃ after, C.run (Zlib.Deflate.deflateInit2_ (some (.tab 0)) level method wb mem strategy
      (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, after) ∧
      DeflateInitial witnessHeap after (.tab 0) p)

end ZlibF.Spec.Public
