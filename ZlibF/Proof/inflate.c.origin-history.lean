import ZlibF.Proof.«inflate.c.origin-history-calls»
import ZlibF.Proof.«inflate.c.copy-both-origin»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Selected default actual histories, now including recovery and copied
destinations as well as every ordinary stream operation. Init and reset2
select fifteen bits. Every transition records the original public arguments
and actual translated execution, never the desired invariant. -/
inductive DefaultOriginHistory : Heap → ZStreamRef → Prop where
  | init {h after r version} : InitDomain h r version →
      ZlibF.PlatformMemory.ByteObjectsFit h → h.allocOk h.nalloc = true →
      C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) → DefaultOriginHistory after r
  | rebuffer {h after r} : DefaultOriginHistory h r → Rebuffer h after r →
      ZlibF.PlatformMemory.ByteObjectsFit after → DefaultOriginHistory after r
  | step {h after r call value} : DefaultOriginHistory h r → DefaultHistoryCall r call →
      StreamArguments h r call → call.execute default h = .ok ((value, default), after) →
      DefaultOriginHistory after r
  | sync {h after r rc} : DefaultOriginHistory h r → StreamArguments h r (.inflateSync (some r)) →
      C.run (inflateSync (some r)) h = .ok (rc, after) → DefaultOriginHistory after r
  | copy {h after source dest z} : DefaultOriginHistory h source → source ≠ dest →
      dest.get h = some z → C.run (inflateCopy (some dest) (some source)) h = .ok (Z_OK, after) →
      DefaultOriginHistory after dest

/-- Actual default initialization gives a concrete member of this history
domain. It makes no assertion that compressed input was decoded. -/
theorem default_origin_history_initial_witness :
    ∃ after, DefaultOriginHistory after (.tab 0) := by
  obtain ⟨after, _z, _s, run, _⟩ := default_origin_state_witness
  exact ⟨after, .init ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain
    inflate_default_witness_platform rfl run⟩

#print axioms default_origin_history_initial_witness
end Zlib.Inflate.Proofs
