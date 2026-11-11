import ZlibF.Proof.«inflate.c.default-history-calls»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual default histories with all selected control, dictionary and
query calls interleaved arbitrarily. This is a proper public-history subset:
reset2 selects fifteen bits, and sync recovery and copy remain excluded.
Every edge records real execution and the original public arguments. -/
inductive DefaultExtendedHistory : Heap → ZStreamRef → Prop where
  | initial {h r} : DefaultControlHistory h r → DefaultExtendedHistory h r
  | rebuffer {h after r} : DefaultExtendedHistory h r → Rebuffer h after r →
      ZlibF.PlatformMemory.ByteObjectsFit after → DefaultExtendedHistory after r
  | step {h after r call value} : DefaultExtendedHistory h r → DefaultHistoryCall r call →
      StreamArguments h r call → call.execute default h = .ok ((value, default), after) →
      DefaultExtendedHistory after r

/-- History induction establishes J and the allocator from actual calls,
and embeds the same history in the original public reachability relation. -/
theorem DefaultExtendedHistory.sound {h : Heap} {r : ZStreamRef}
    (history : DefaultExtendedHistory h r) :
    (∃ zs z s, DefaultStateJ h r zs z s ∧ DefAlloc z) ∧ StreamReachable .inflate h r := by
  induction history with
  | initial prior => exact ⟨prior.invariant, prior.reachable⟩
  | @rebuffer before after r prior edit platform ih =>
    obtain ⟨⟨zs, z, s, current, allocator⟩, reachable⟩ := ih
    obtain ⟨stream, next⟩ := rebuffer_default_state current edit platform
    obtain ⟨otherZ, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : otherZ = stream := Option.some.inj (good.live.hz.symm.trans next.good.live.hz)
    subst otherZ
    refine ⟨⟨zs, stream, s, next, ?_⟩, StreamReachable.rebuffer reachable edit (fun _ => platform)⟩
    rw [fields]
    exact allocator
  | @step before after r call value prior selected arguments actual ih =>
    obtain ⟨⟨zs, z, s, current, allocator⟩, reachable⟩ := ih
    obtain ⟨stream, state, next, nextAllocator⟩ := selected.preserve current allocator arguments actual
    exact ⟨⟨zs, stream, state, next, nextAllocator⟩,
      StreamReachable.step reachable (fun _ => current.platform) selected.public_operation arguments actual⟩

/-- The selected dictionary/query history relation has a concrete actual
initialization, legal rebuffer and public inflate execution. This retains
the malformed-header witness and makes no successful decoding claim. -/
theorem default_extended_history_witness :
    ∃ incoming after rc,
      DefaultExtendedHistory incoming (.tab 0) ∧ DefaultExtendedHistory after (.tab 0) ∧
      C.run (Zlib.Inflate.inflate (some (.tab 0)) Z_FINISH) incoming = .ok (rc, after) := by
  obtain ⟨incoming, after, _stream, _returned, _state, _used, _output, rc, before, final, run, _⟩ :=
    default_control_memory_history_witness
  exact ⟨incoming, after, rc, .initial before, .initial final, run⟩

#print axioms DefaultExtendedHistory.sound
#print axioms default_extended_history_witness
end Zlib.Inflate.Proofs
