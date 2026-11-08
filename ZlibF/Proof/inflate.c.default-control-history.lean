import ZlibF.Proof.«inflate.c.default-public-memory-contract»
import ZlibF.Proof.«inflate.c.reset-default-state»
import ZlibF.Proof.«inflate.c.prime-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual default initialization, processing and selected control calls.
Every edge records the translated execution, never its desired contract.
Rebuffered caller objects satisfy the explicit platform scope. Reset2 is
selected at fifteen bits. Copy, sync and dictionary transitions must still
be added before this covers the entire public history relation. -/
inductive DefaultControlHistory : Heap → ZStreamRef → Prop where
  | init {h after r version} :
      InitDomain h r version → ZlibF.PlatformMemory.ByteObjectsFit h →
      h.allocOk h.nalloc = true →
      C.run (inflateInit_ (some r) version 112) h = .ok (Z_OK, after) → DefaultControlHistory after r
  | rebuffer {h after r} : DefaultControlHistory h r → Rebuffer h after r →
      ZlibF.PlatformMemory.ByteObjectsFit after → DefaultControlHistory after r
  | inflate {h after r rc flush} : DefaultControlHistory h r → StreamBuffers h r →
      C.run (Zlib.Inflate.inflate (some r) flush) h = .ok (rc, after) → DefaultControlHistory after r
  | resetKeep {h after r rc} : DefaultControlHistory h r →
      C.run (inflateResetKeep (some r)) h = .ok (rc, after) → DefaultControlHistory after r
  | reset {h after r rc} : DefaultControlHistory h r →
      C.run (inflateReset (some r)) h = .ok (rc, after) → DefaultControlHistory after r
  | reset2 {h after r rc} : DefaultControlHistory h r →
      C.run (inflateReset2 (some r) 15) h = .ok (rc, after) → DefaultControlHistory after r
  | prime {h after r rc bits value} : DefaultControlHistory h r →
      C.run (inflatePrime (some r) bits value) h = .ok (rc, after) → DefaultControlHistory after r
  | validate {h after r rc check} : DefaultControlHistory h r →
      C.run (inflateValidate (some r) check) h = .ok (rc, after) → DefaultControlHistory after r
  | getHeader {h after r rc head} : DefaultControlHistory h r →
      HeaderMemory h r head true → head ≠ none →
      C.run (inflateGetHeader (some r) head) h = .ok (rc, after) → DefaultControlHistory after r
  | undermine {h after r rc subvert} : DefaultControlHistory h r →
      C.run (inflateUndermine (some r) subvert) h = .ok (rc, after) → DefaultControlHistory after r

/-- Establish the strong state relation by induction over actual calls.
No constructor assumes J or a callee contract. -/
theorem DefaultControlHistory.invariant {h : Heap} {r : ZStreamRef} (history : DefaultControlHistory h r) :
    ∃ zs z s, DefaultStateJ h r zs z s ∧ DefAlloc z := by
  induction history with
  | @init before after r version domain platform allocation actual =>
    obtain ⟨computed, z, s, run, initial, current, _⟩ :=
      inflate_default_state_initial before r version domain platform allocation
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    obtain ⟨otherZ, _otherS, good, alloc, free, _⟩ := initial
    have sameZ : otherZ = z := Option.some.inj (good.live.hz.symm.trans current.good.live.hz)
    subst otherZ
    exact ⟨before.nextBlk, z, s, current, alloc, free⟩
  | @rebuffer before after r prior edit platform ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    obtain ⟨stream, next⟩ := rebuffer_default_state current edit platform
    obtain ⟨otherZ, fields, good⟩ := rebuffer_inflate_good current.good edit
    have sameZ : otherZ = stream := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst otherZ
    refine ⟨zs, stream, s, next, ?_⟩
    rw [fields]
    exact allocator
  | @inflate before after r rc flush prior buffers actual ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    obtain ⟨code, computed, stream, state, _used, _output, run, next, nextAllocator, _⟩ :=
      inflate_default_view_public_memory_contract current allocator buffers flush
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨zs, stream, state, next, nextAllocator⟩
  | @resetKeep before after r rc prior actual ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    obtain ⟨computed, run, _, next, _⟩ := inflateResetKeep_default_state current
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨zs, _, _, next, allocator⟩
  | @reset before after r rc prior actual ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    obtain ⟨computed, run, next, _⟩ := inflateReset_default_state current allocator.2
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨zs, _, _, next, allocator⟩
  | @reset2 before after r rc prior actual ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    obtain ⟨computed, run, next, _⟩ := inflateReset2_15_default_state current allocator.2
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨zs, _, _, next, allocator⟩
  | @prime before after r rc bits value prior actual ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    obtain ⟨code, computed, state, run, next, _⟩ := inflatePrime_default_state current bits value
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨zs, z, state, next, allocator⟩
  | @validate before after r rc check prior actual ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    obtain ⟨computed, state, run, _, _, next⟩ := inflateValidate_default_state current check
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨zs, z, state, next, allocator⟩
  | @getHeader before after r rc head prior _memory _nonnull actual ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    have run := (inflateGetHeader_default_J current.toDefaultDecodeJ head).1
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨zs, z, s, current, allocator⟩
  | @undermine before after r rc subvert prior actual ih =>
    obtain ⟨zs, z, s, current, allocator⟩ := ih
    have run := (inflateUndermine_default_J current.toDefaultDecodeJ subvert).1
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨zs, z, s, current, allocator⟩

#print axioms DefaultControlHistory.invariant
end Zlib.Inflate.Proofs
