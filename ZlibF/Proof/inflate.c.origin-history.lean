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

/-- Induction establishes both origins, J and the allocator from actual
initialization and every selected transition. The same history embeds in
the unchanged original public reachability relation. -/
theorem DefaultOriginHistory.sound {h : Heap} {r : ZStreamRef} (history : DefaultOriginHistory h r) :
    (∃ zs z s, DefaultOriginState h r zs z s ∧ DefAlloc z) ∧ StreamReachable .inflate h r := by
  induction history with
  | @init before after r version domain platform allocation actual =>
    obtain ⟨computed, z, s, run, current, allocator, reachable⟩ :=
      inflate_default_origin_initial before r version domain platform allocation
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨⟨before.nextBlk, z, s, current, allocator⟩, reachable⟩
  | @rebuffer before after r prior edit platform ih =>
    obtain ⟨⟨zs, z, s, current, allocator⟩, reachable⟩ := ih
    obtain ⟨stream, next⟩ := rebuffer_default_origin current edit platform
    obtain ⟨otherZ, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : otherZ = stream := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst otherZ
    refine ⟨⟨zs, stream, s, next, ?_⟩, StreamReachable.rebuffer reachable edit platform⟩
    rw [fields]
    exact allocator
  | @step before after r call value prior selected arguments actual ih =>
    obtain ⟨⟨zs, z, s, current, allocator⟩, reachable⟩ := ih
    obtain ⟨stream, state, next, nextAllocator⟩ := selected.preserve_origin current allocator arguments actual
    exact ⟨⟨zs, stream, state, next, nextAllocator⟩,
      StreamReachable.step reachable current.platform selected.public_operation arguments actual⟩
  | @sync before after r rc prior arguments actual ih =>
    obtain ⟨⟨zs, z, s, current, allocator⟩, reachable⟩ := ih
    obtain ⟨stream, state, next, nextAllocator⟩ := inflateSync_default_origin_of_run current allocator actual
    exact ⟨⟨zs, stream, state, next, nextAllocator⟩,
      StreamReachable.step reachable current.platform (call := .inflateSync (some r)) ⟨rfl, rfl⟩ arguments
        (heapCall_of_actual_run actual default)⟩
  | @copy before after source dest oldDest prior different destGet actual ih =>
    obtain ⟨⟨zs, z, s, current, allocator⟩, reachable⟩ := ih
    obtain ⟨copied, destination, _original⟩ :=
      inflateCopy_actual_success_both_origin current allocator destGet different actual
    exact ⟨⟨before.nextBlk, { z with state := some (.inflate before.nextBlk) }, copied,
      destination, allocator⟩, StreamReachable.inflateCopy reachable different destGet actual⟩

/-- Actual default initialization gives a concrete member of this history
domain. It makes no assertion that compressed input was decoded. -/
theorem default_origin_history_initial_witness :
    ∃ after, DefaultOriginHistory after (.tab 0) := by
  obtain ⟨after, _z, _s, run, _⟩ := default_origin_state_witness
  exact ⟨after, .init ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain
    inflate_default_witness_platform rfl run⟩

#print axioms DefaultOriginHistory.sound
#print axioms default_origin_history_initial_witness
end Zlib.Inflate.Proofs
