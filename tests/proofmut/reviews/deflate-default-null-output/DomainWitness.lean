import ZlibF.Proof.«deflate.c.engine.generic-default-request-trace»
import ZlibF.Proof.«deflate.c.engine.finish-protocol»
import ZlibF.Spec.Public.DeflateCore

namespace NullGuardBehaviorReview
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs Zlib.Deflate.Engine.Proofs
open ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.DeflateInit
set_option autoImplicit false

/-- Domain non-emptiness only. Existing actual initialization establishes the
invariant; no caller invariant or successful data-call premise is supplied. -/
theorem default_null_output_domain_nonempty :
    ∃ after z d,
      InitDomain ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap (.tab 0) (.ref (.blk 1) 0) ∧
      C.run (deflateInit_ (some (.tab 0)) Z_DEFAULT_COMPRESSION (.ref (.blk 1) 0) 112)
        ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap = .ok (Z_OK, after) ∧
      GenericDefaultRequestTrace (.tab 0) after ∧ DeflateCore.Calls (.tab 0) after ∧
      StreamReachable .deflate after (.tab 0) ∧ EngineStart after (.tab 0) 2 z d ∧
      StreamBuffers after (.tab 0) ∧ ActiveHeader after (.tab 0) ∧ DeflateCore.Output z.next_out ∧
      z.next_in = .null ∧ z.avail_in = 0 ∧ z.next_out = .null ∧ z.avail_out = 0 := by
  let before := ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap
  have getZ : (ZStreamRef.tab 0).get before = some (default : ZStream) := by
    simp [ZStreamRef.get, before, ZlibF.Spec.Public.Proofs.DeflateInit.witnessHeap]
  have domain : InitDomain before (.tab 0) (.ref (.blk 1) 0) :=
    ⟨witness_fresh, witness_uniq, rfl, witness_version, default, getZ,
      ⟨Or.inl rfl, Or.inl rfl⟩, rfl⟩
  obtain ⟨after, z, d, run, start, initial, reachable, nextIn, availIn, nextOut, availOut⟩ :=
    default_initialization_engine_bindings (h := before) (r := .tab 0) (z := default)
      (version := .ref (.blk 1) 0) (level := Z_DEFAULT_COMPRESSION) (p := settings 6)
      witness_fresh witness_uniq rfl getZ ⟨Or.inl rfl, Or.inl rfl⟩ witness_version
      (by decide +kernel) (by intro j hj; rfl)
  have ni : z.next_in = .null := nextIn
  have ai : z.avail_in = 0 := availIn
  have no : z.next_out = .null := nextOut
  have ao : z.avail_out = 0 := availOut
  have buffers : StreamBuffers after (.tab 0) :=
    ⟨z, start.good.live.hz, Or.inl ni, Or.inl no, Or.inl (by rw [ai]; rfl)⟩
  have header := default_finish_active_header start.good (initial_no_header start initial)
  exact ⟨after, z, d, domain, run, .init domain run, .init domain run, reachable,
    start, buffers, header, Or.inl no, ni, ai, no, ao⟩

#print axioms default_null_output_domain_nonempty
#print default_null_output_domain_nonempty
end NullGuardBehaviorReview
