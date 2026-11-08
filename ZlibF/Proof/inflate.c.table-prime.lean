import ZlibF.Proof.«inflate.c.codelens-invariant»
import ZlibF.Proof.«inflate.c.misc2»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Updating the private bit buffer retains every actual code-array view. -/
theorem code_views_set_bits {h : Heap} {zs : Nat} {s : InflateState}
    (state : h.istates zs = some s) (hold : UInt64) (bits : UInt32) (ref : CodeRef) :
    (Space.get (setI h zs { s with hold, bits }) ref : Option (Array Code)) = Space.get h ref := by
  cases ref with
  | istate_codes i =>
    by_cases same : i = zs
    · subst i
      simp [Space.get, state]
    · simp [Space.get, setI, upd_ne _ _ _ _ same]
  | st_lenfix => rfl
  | st_distfix => rfl

/-- Both guarded table clauses survive an actual private bit-buffer update.
No table contract is assumed for a callee. -/
theorem table_clauses_set_bits {h : Heap} {zs : Nat} {s : InflateState}
    (state : h.istates zs = some s) (hold : UInt64) (bits : UInt32)
    (data : DataTableInvariant h s) (codes : CodeLengthInvariant zs s) :
    DataTableInvariant (setI h zs { s with hold, bits }) { s with hold, bits } ∧
      CodeLengthInvariant zs { s with hold, bits } := by
  refine ⟨?_, codes⟩
  intro active
  have tables := data active
  constructor
  · obtain ⟨ref, offset, array, pointer, get, safe⟩ := tables.lengthTable
    exact ⟨ref, offset, array, pointer, by rw [code_views_set_bits state]; exact get, safe⟩
  · obtain ⟨ref, offset, array, pointer, get, safe⟩ := tables.distanceTable
    exact ⟨ref, offset, array, pointer, by rw [code_views_set_bits state]; exact get, safe⟩

/-- `int inflatePrime(z_streamp strm, int bits, int value)`.
Every signed argument pair preserves both current table clauses on the
actual returned heap. Bit clearing, refusal and insertion are all included.
This discharges one transition's table obligation, not the full history invariant. -/
theorem inflatePrime_table_clauses {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s)
    (data : DataTableInvariant h s) (codes : CodeLengthInvariant zs s) (bits value : Int32) :
    ∃ rc after state,
      C.run (inflatePrime (some r) bits value) h = .ok (rc, after) ∧
      Good after r zs z state ∧ DataTableInvariant after state ∧
      CodeLengthInvariant zs state ∧ (rc = Z_OK ∨ rc = Z_STREAM_ERROR) := by
  obtain ⟨zero, clear, reject, insert⟩ := inflatePrime_spec good bits value
  by_cases equal : bits = 0
  · exact ⟨Z_OK, h, s, zero equal, good, data, codes, Or.inl rfl⟩
  by_cases negative : bits < 0
  · obtain ⟨run, nextGood⟩ := clear negative
    obtain ⟨nextData, nextCodes⟩ := table_clauses_set_bits good.live.hs 0 0 data codes
    exact ⟨Z_OK, _, _, run, nextGood, nextData, nextCodes, Or.inl rfl⟩
  have positive : 0 < bits := by
    rw [Int32.lt_iff_toInt_lt] at negative ⊢
    change ¬ bits.toInt < 0 at negative
    change 0 < bits.toInt
    have notZero : bits.toInt ≠ 0 := by
      intro eq
      apply equal
      exact Int32.toInt_inj.mp eq
    omega
  by_cases wide : 16 < bits.toInt
  · exact ⟨Z_STREAM_ERROR, h, s, reject positive (Or.inl wide), good, data, codes, Or.inr rfl⟩
  by_cases full : 32 < s.bits.toNat + bits.toInt.toNat
  · exact ⟨Z_STREAM_ERROR, h, s, reject positive (Or.inr full), good, data, codes, Or.inr rfl⟩
  obtain ⟨run, nextGood⟩ := insert positive (by omega) (by omega)
  obtain ⟨nextData, nextCodes⟩ := table_clauses_set_bits good.live.hs
    (s.hold + (primeBits bits value <<< s.bits.toUInt64)) (s.bits + i2u bits) data codes
  exact ⟨Z_OK, _, _, run, nextGood, nextData, nextCodes, Or.inl rfl⟩

end Zlib.Inflate.Proofs
