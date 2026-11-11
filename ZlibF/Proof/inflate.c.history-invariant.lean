import ZlibF.Proof.«inflate.c.invariant»
import ZlibF.Proof.«inflate.c.default-history-calls»

/-!
# inflate.c: caller edits and stream operations preserve the general invariant

Each lemma covers one actual return of a public operation from any state
with `InflateInv`, in every configuration.
-/

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A caller rebuffer keeps the decoder state and its owned memory. -/
theorem rebuffer_invariant {h after : Heap} {r : ZStreamRef} {i : Nat} {z : ZStream}
    {s : InflateState} (current : InflateInv h r i z s) (edit : Rebuffer h after r) :
    ∃ z', InflateInv after r i z' s := by
  obtain ⟨stream, fields, good⟩ := rebuffer_inflate_good current.good edit
  have tables := (rebuffer_dataTableInvariant current.good edit current.tables).2
  refine ⟨stream, ⟨good, ?_, tables, current.pending, current.lengths, current.headerLengths,
    current.held, current.config, current.modes, current.phase, current.origin, edit.2.2.1⟩⟩
  rw [fields]
  exact current.alloc

/-- Preservation by one actual return of a stream operation. -/
def InflatePreserves (r : ZStreamRef) (call : Call) : Prop :=
  ∀ (h after : Heap) (i : Nat) (z : ZStream) (s : InflateState) (value : call.Result),
    InflateInv h r i z s → StreamArguments h r call →
    call.execute default h = .ok ((value, default), after) →
    ∃ z' s', InflateInv after r i z' s'

theorem inflateSyncPoint_preserves (r : ZStreamRef) :
    InflatePreserves r (.inflateSyncPoint (some r)) := by
  intro h after i z s value current _ actual
  have run := inflateSyncPoint_spec current.good.live
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

theorem inflateMark_preserves (r : ZStreamRef) : InflatePreserves r (.inflateMark (some r)) := by
  intro h after i z s value current _ actual
  obtain ⟨mark, run, _⟩ := inflateMark_spec current.good.live
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

theorem inflateCodesUsed_preserves (r : ZStreamRef) :
    InflatePreserves r (.inflateCodesUsed (some r)) := by
  intro h after i z s value current _ actual
  obtain ⟨offset, _, _, run⟩ := inflateCodesUsed_spec current.good
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

/-- The default build refuses undermining and keeps `sane = 1`. -/
theorem inflateUndermine_preserves (r : ZStreamRef) (subvert : Int32) :
    InflatePreserves r (.inflateUndermine (some r) subvert) := by
  intro h after i z s value current _ actual
  obtain ⟨written, run, heap, _⟩ := inflateUndermine_safe current.good subvert
  have state : { s with sane := 1 } = s := by rw [← current.pending.sane]
  have unchanged : written = h := by rw [heap, state, tcSetI_same current.good.live.hs]
  subst unchanged
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  exact ⟨z, s, current⟩

#print axioms rebuffer_invariant
#print axioms inflateSyncPoint_preserves
#print axioms inflateMark_preserves
#print axioms inflateCodesUsed_preserves
#print axioms inflateUndermine_preserves

/-- Prime changes only the private bit buffer. A checked new held value
transports every other clause. -/
theorem InflateInv.prime_set_bits
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (current : InflateInv h r zs z s) (hold : UInt64) (bits : UInt32)
    (good : Good (setI h zs { s with hold, bits }) r zs z { s with hold, bits })
    (held : hold.toNat < 2 ^ bits.toNat) :
    InflateInv (setI h zs { s with hold, bits }) r zs z { s with hold, bits } := by
  obtain ⟨tables, lengths⟩ := table_clauses_set_bits current.good.live.hs
    hold bits current.tables current.lengths
  refine ⟨good, current.alloc, tables, ?_, lengths, ?_, held,
    ⟨current.config.wrap, current.config.reqwrap, current.config.window, current.config.reqbits,
      current.config.header⟩, current.modes,
    ⟨current.phase.started, current.phase.flags, current.phase.gzipFlags⟩, current.origin, ?_⟩
  · refine ⟨current.pending.sane, ?_, ?_, ?_, ?_⟩
    · simpa [LengthExtraSafe, BackBound] using current.pending.lenext
    · simpa [DistanceSafe, PendingLengthSafe, BackBound] using current.pending.dist
    · simpa [DistanceExtraSafe, PendingLengthSafe, BackBound] using current.pending.distext
    · simpa [MatchSafe] using current.pending.matching
  · simpa [LengthHeaderInvariant] using current.headerLengths
  · simpa only [LibraryGlobals, setI] using current.globals

/-- Every signed prime request: refusals leave the heap unchanged, accepted
requests keep the checked bit-buffer bound. -/
theorem inflatePrime_preserves (r : ZStreamRef) (bits value : Int32) :
    InflatePreserves r (.inflatePrime (some r) bits value) := by
  intro h after i z s result current _ actual
  have finish : ∀ {rc : Int32} {written : Heap} {state : InflateState},
      C.run (inflatePrime (some r) bits value) h = .ok (rc, written) →
      InflateInv written r i z state → ∃ z' s', InflateInv after r i z' s' := by
    intro rc written state run next
    have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
    cases same
    exact ⟨z, state, next⟩
  obtain ⟨zero, clear, reject, insert⟩ := inflatePrime_spec current.good bits value
  by_cases equal : bits = 0
  · exact finish (zero equal) current
  by_cases negative : bits < 0
  · obtain ⟨run, good⟩ := clear negative
    have held : (0 : UInt64).toNat < 2 ^ (0 : UInt32).toNat := by decide
    exact finish run (current.prime_set_bits 0 0 good held)
  have positive : 0 < bits := by
    rw [Int32.lt_iff_toInt_lt] at negative ⊢
    simp only [Int32.toInt_zero] at negative ⊢
    have notZero : bits.toInt ≠ 0 := by
      intro eq
      apply equal
      exact Int32.toInt_inj.mp eq
    omega
  by_cases wide : 16 < bits.toInt
  · exact finish (reject positive (Or.inl wide)) current
  by_cases full : 32 < s.bits.toNat + bits.toInt.toNat
  · exact finish (reject positive (Or.inr full)) current
  obtain ⟨run, good⟩ := insert positive (by omega) (by omega)
  have held := primeState_held s bits value current.held positive (by omega) (by omega)
  exact finish run (current.prime_set_bits _ _ good held)

/-- Toggling bit 2 keeps a reachable wrapper value. -/
theorem validateWrap_value {w check : Int32} (value : WrapValue w) :
    WrapValue (if check != 0 && w != 0 then w ||| 4 else w &&& ~~~4) := by
  unfold WrapValue at value ⊢
  rcases value with v | v | v | v | v | v | v <;> subst v <;> cases (check != 0) <;> decide

/-- Toggling bit 2 keeps bit 1. -/
theorem validateWrap_gzip {w check : Int32} (gzip : GzipAllowed w) :
    GzipAllowed (if check != 0 && w != 0 then w ||| 4 else w &&& ~~~4) := by
  unfold GzipAllowed at gzip ⊢
  rcases gzip with v | v | v | v <;> subst v <;> cases (check != 0) <;> decide

theorem inflateValidate_preserves (r : ZStreamRef) (check : Int32) :
    InflatePreserves r (.inflateValidate (some r) check) := by
  intro h after i z s result current _ actual
  obtain ⟨written, run, heap, good, _⟩ := inflateValidate_safe current.good check
  subst written
  have same := Except.ok.inj ((heapCall_of_actual_run run default).symm.trans actual)
  cases same
  let state := validateState check s
  have tables : DataTableInvariant (setI h i state) state := by
    intro active
    have original := current.tables active
    constructor
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.lengthTable
      exact ⟨ref, off, array, ptr, by rw [validate_code_views current.good.live.hs]; exact get, safe⟩
    · obtain ⟨ref, off, array, ptr, get, safe⟩ := original.distanceTable
      exact ⟨ref, off, array, ptr, by rw [validate_code_views current.good.live.hs]; exact get, safe⟩
  refine ⟨z, state, ⟨good, current.alloc, tables,
    ⟨current.pending.sane, current.pending.lenext, current.pending.dist,
      current.pending.distext, current.pending.matching⟩,
    current.lengths, current.headerLengths, current.held, ?_, current.modes, ?_,
    current.origin, current.globals⟩⟩
  · exact ⟨validateWrap_value current.config.wrap, validateWrap_value current.config.reqwrap,
      current.config.window, current.config.reqbits,
      fun attached => validateWrap_gzip (current.config.header attached)⟩
  · refine ⟨?_, current.phase.flags,
      fun unread zero => validateWrap_gzip (current.phase.gzipFlags unread zero)⟩
    rcases current.phase.started with head | bad | mem | sync | raw | started
    · exact Or.inl head
    · exact Or.inr (Or.inl bad)
    · exact Or.inr (Or.inr (Or.inl mem))
    · exact Or.inr (Or.inr (Or.inr (Or.inl sync)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (validateState_raw_wrap raw check)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr started))))

#print axioms inflatePrime_preserves
#print axioms inflateValidate_preserves

end Zlib.Inflate.Proofs
