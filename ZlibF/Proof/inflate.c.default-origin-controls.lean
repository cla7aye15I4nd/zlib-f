import ZlibF.Proof.«inflate.c.default-origin-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Bit-buffer writes do not change either history origin. -/
theorem DefaultOriginState.prime_set_bits {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s)
    (hold : UInt64) (bits : UInt32)
    (good : Good (setI h zs { s with hold, bits }) r zs z { s with hold, bits })
    (held : hold.toNat < 2 ^ bits.toNat) :
    DefaultOriginState (setI h zs { s with hold, bits }) r zs z { s with hold, bits } :=
  before.of_fields (before.toDefaultStateJ.prime_set_bits hold bits good held) rfl rfl rfl

/-- Every signed actual prime request retains both source origins.
Rejected counts, clearing and accepted insertions use the real source runs. -/
theorem inflatePrime_default_origin {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s)
    (bits value : Int32) :
    ∃ rc after state, C.run (inflatePrime (some r) bits value) h = .ok (rc, after) ∧
      DefaultOriginState after r zs z state ∧ (rc = Z_OK ∨ rc = Z_STREAM_ERROR) := by
  obtain ⟨zero, clear, reject, insert⟩ := inflatePrime_spec before.good bits value
  by_cases equal : bits = 0
  · exact ⟨Z_OK, h, s, zero equal, before, Or.inl rfl⟩
  by_cases negative : bits < 0
  · obtain ⟨run, good⟩ := clear negative
    exact ⟨Z_OK, _, _, run, before.prime_set_bits 0 0 good (by decide), Or.inl rfl⟩
  have positive : 0 < bits := by
    rw [Int32.lt_iff_toInt_lt] at negative ⊢
    simp only [Int32.toInt_zero] at negative ⊢
    have notZero : bits.toInt ≠ 0 := by
      intro zero
      exact equal (Int32.toInt_inj.mp zero)
    omega
  by_cases wide : 16 < bits.toInt
  · exact ⟨Z_STREAM_ERROR, h, s, reject positive (Or.inl wide), before, Or.inr rfl⟩
  by_cases full : 32 < s.bits.toNat + bits.toInt.toNat
  · exact ⟨Z_STREAM_ERROR, h, s, reject positive (Or.inr full), before, Or.inr rfl⟩
  obtain ⟨run, good⟩ := insert positive (by omega) (by omega)
  have held := primeState_held s bits value before.held positive (by omega) (by omega)
  exact ⟨Z_OK, _, _, run, before.prime_set_bits _ _ good held, Or.inl rfl⟩

/-- Validation changes wrapper policy but retains the header flag and both
table pointers, including during error and synchronization modes. -/
theorem inflateValidate_default_origin {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s) (check : Int32) :
    ∃ after state, C.run (inflateValidate (some r) check) h = .ok (Z_OK, after) ∧
      DefaultOriginState after r zs z state := by
  obtain ⟨after, state, run, _heap, stateEq, current⟩ :=
    inflateValidate_default_state before.toDefaultStateJ check
  refine ⟨after, state, run, current, ?_, ?_⟩
  · rw [stateEq]
    exact before.flagsOrigin.transfer rfl (wrapper_validate (check := check) before.wrapper).2.2
  · rw [stateEq]
    exact before.tableOrigin

/-- The selected build's undermine refusal retains the complete origin state. -/
theorem inflateUndermine_default_origin {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s) (subvert : Int32) :
    C.run (inflateUndermine (some r) subvert) h = .ok (Z_DATA_ERROR, h) ∧
      DefaultOriginState h r zs z s :=
  ⟨(inflateUndermine_default_J before.toDefaultDecodeJ subvert).1, before⟩

/-- General public dictionary extraction retains the decoder record and
therefore both source origins while writing the caller's actual bytes. -/
theorem inflateGetDictionary_default_origin {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (before : DefaultOriginState h r zs z s)
    (dest : BPtr) (dl : Option UInt32) (range : CallerRange h r dest s.whave.toNat true) :
    ∃ after, C.run (inflateGetDictionary (some r) dest dl) h =
      .ok ((Z_OK, dl.map (fun _ => s.whave)), after) ∧ DefaultOriginState after r zs z s := by
  obtain ⟨after, run, current⟩ := inflateGetDictionary_default_state before.toDefaultStateJ dest dl range
  exact ⟨after, run, ⟨current, before.flagsOrigin, before.tableOrigin⟩⟩

#print axioms inflatePrime_default_origin
#print axioms inflateValidate_default_origin
#print axioms inflateUndermine_default_origin
#print axioms inflateGetDictionary_default_origin
end Zlib.Inflate.Proofs
