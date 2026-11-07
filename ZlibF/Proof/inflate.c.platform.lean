import ZlibF.Proof.PlatformMemory
import ZlibF.Proof.«public-inflate-init»

/-!
# inflate.c: successful initialization preserves the platform size scope

The new clause is derived from the actual initialization writes. It is not
an additional postcondition assumed for the translated initializer.
-/

namespace ZlibF.Spec.Public.Proofs.InflateInit
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec
open ZlibF.PlatformMemory
set_option autoImplicit false

/-- Initializing the decoder changes no represented byte-view sizes. -/
theorem initOkHeap_fits {h : Heap} (fit : ByteObjectsFit h)
    (r : ZStreamRef) (z : ZStream) (wrap wb : Int32) :
    ByteObjectsFit (initOkHeap h r z wrap wb) := by
  unfold initOkHeap
  dsimp only
  rw [reset2Heap_null _ _ _ rfl]
  have allocated : ByteObjectsFit (allocIstHeap (r.put h (initStream2 z h.nextBlk)) (initState r)) :=
    (fit.put_stream r _).of_storage_eq rfl rfl rfl
  exact (allocated.put_stream r _).with_istates _

/-- `int inflateInit2_(z_streamp strm, int windowBits, const char *version, int stream_size)`.
For every accepted window parameter and successful state allocation, actual
initialization establishes the existing initial-state relation and a reachable
stream, and preserves the explicit LP64 byte-object platform premise.
Caller storage must already satisfy that premise. This success theorem does
not discharge the separate invalid-parameter cleanup target. -/
theorem inflate_domain_general_platform
    (h : Heap) (r : ZStreamRef) (version : BPtr) (wb : Int32) (wrap : Api.Wrap) (bits : Nat)
    (domain : InitDomain h r version) (fit : ByteObjectsFit h)
    (params : Api.inflWbits wb.toInt = some (wrap, bits))
    (allocation : h.allocOk h.nalloc = true) :
    ∃ after, C.run (inflateInit2_ (some r) wb version 112) h = .ok (Z_OK, after) ∧
      InflateInitial h after r wrap bits ∧ StreamReachable .inflate after r ∧
      ByteObjectsFit after := by
  obtain ⟨after, run, initial, reachable⟩ :=
    inflate_domain_general h r version wb wrap bits domain params allocation
  obtain ⟨fresh, uniq, globals, value, z, get, allocators, rest⟩ := domain
  obtain ⟨nonnull, read⟩ := version_value_read value
  have parameters := params_equiv wb
  rw [params] at parameters
  change reset2Params wb = some (publicWrap wrap, Int32.ofInt bits) at parameters
  have actual := inflateInit2_success get fresh allocation allocators.1 allocators.2
    nonnull read parameters
  have same : after = initOkHeap h r z (publicWrap wrap) (Int32.ofInt bits) := by
    have equality := run.symm.trans actual
    cases equality
    rfl
  refine ⟨after, run, initial, reachable, ?_⟩
  rw [same]
  exact initOkHeap_fits fit r z _ _

end ZlibF.Spec.Public.Proofs.InflateInit
