import ZlibF.Proof.«inflate.c.window-public-call-history»
import ZlibF.Proof.«inflate.c.window-dictionary-history»

namespace Zlib.Inflate.Proofs.WindowHistory
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

theorem dictionary_exists_bounded {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (good : Good h r zs z s) :
    ∃ history : List UInt8, history.length ≤ 2 ^ s.wbits.toNat ∧ InflateDictionary h s history := by
  rcases good.inv.win.block with null | ⟨w, a, window, get, _ro, size⟩
  · exact ⟨[], by simp, null_dictionary_empty good null⟩
  · refine ⟨ringList a s.wsize.toNat s.wnext.toNat s.whave.toNat, ?_,
      (inflateDictionary_eq_ring good window get size).mpr rfl⟩
    have haveBound := good.inv.win.hv
    have sizeBound := good.inv.win.ws
    simp only [ringList, List.length_map, List.length_range]
    omega

/-- The guarded ghost survives every actual setter, including calls made
in inactive states. Only a real successful setter appends physical bytes. -/
theorem dictionary_history_guarded
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {source : BPtr} {len : UInt32} {history incoming : List UInt8}
    (invariant : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (range : CallerRange h r source len.toNat false) (input : Bytes h source len.toNat incoming)
    (stored : s.mode < CHECK → InflateDictionary h s
      (history.drop (history.length - 2 ^ s.wbits.toNat))) :
    ∃ rc after state, C.run (inflateSetDictionary (some r) source len) h = .ok (rc, after) ∧
      DefaultStateJ after r zs z state ∧
      (state.mode < CHECK → InflateDictionary after state
        ((if rc = Z_OK then history ++ incoming else history).drop
          ((if rc = Z_OK then history ++ incoming else history).length - 2 ^ state.wbits.toNat))) := by
  by_cases active : s.mode < CHECK
  · obtain ⟨rc, after, state, run, current, outcome⟩ :=
      inflateSetDictionary_window_history invariant allocator range input (stored active)
    refine ⟨rc, after, state, run, current, ?_⟩
    intro nextActive
    rcases outcome with ⟨ok, _mode, dictionary⟩ | ⟨refused, heap, stateEq⟩ | ⟨mem, mode⟩
    · simpa only [ok, ite_true] using dictionary
    · have notOK : rc ≠ Z_OK := by
        rcases refused with error | error <;> rw [error] <;> decide
      simpa only [if_neg notOK, heap, stateEq] using stored active
    · rw [mode] at nextActive
      exact False.elim ((by decide : ¬ MEM < CHECK) nextActive)
  · obtain ⟨represented, bound, dictionary⟩ := dictionary_exists_bounded invariant.good
    have old : InflateDictionary h s
        (represented.drop (represented.length - 2 ^ s.wbits.toNat)) := by
      simpa only [Nat.sub_eq_zero_of_le bound, List.drop_zero] using dictionary
    obtain ⟨rc, after, state, run, current, outcome⟩ :=
      inflateSetDictionary_window_history invariant allocator range input old
    refine ⟨rc, after, state, run, current, ?_⟩
    intro nextActive
    rcases outcome with ⟨_ok, mode, _dictionary⟩ | ⟨_refused, _heap, stateEq⟩ | ⟨_mem, mode⟩
    · rw [mode] at nextActive
      exact False.elim (active nextActive)
    · rw [stateEq] at nextActive
      exact False.elim (active nextActive)
    · rw [mode] at nextActive
      exact False.elim ((by decide : ¬ MEM < CHECK) nextActive)

/-- Source-only default data traces in the explicit platform scope. The
extra index is physical saved-window history: successful setters append
it even when the original public DataLog replaces its logical dictionary.
No constructor assumes an invariant, callee contract or output meaning. -/
inductive DataHistory (r : ZStreamRef) : Heap → DataLog → List UInt8 → Prop where
  | init {h after version} : InitDomain h r version →
      ZlibF.PlatformMemory.ByteObjectsFit h → h.allocOk h.nalloc = true →
      C.run (inflateInit2_ (some r) 15 version 112) h = .ok (Z_OK, after) →
      DataHistory r after {} []
  | caller {h after log history} : DataHistory r h log history → Rebuffer h after r →
      ZlibF.PlatformMemory.ByteObjectsFit after → DataHistory r after log history
  | step {h after log history flush rc input output used} : DataHistory r h log history →
      ZlibF.PlatformMemory.ByteObjectsFit h → DataStep .inflate h after r flush rc input output used →
      DataHistory r after {log with
        input := log.input ++ input.take used, output := log.output ++ output,
        result := rc, finished := log.finished || rc == Z_STREAM_END} (history ++ output)
  | dictionary {h after log history p n bytes rc} : DataHistory r h log history →
      ZlibF.PlatformMemory.ByteObjectsFit h → StreamArguments h r (.inflateSetDictionary (some r) p n) → Bytes h p n.toNat bytes →
      C.run (inflateSetDictionary (some r) p n) h = .ok (rc, after) →
      DataHistory r after {log with dictionary := if rc = Z_OK then bytes else log.dictionary}
        (if rc = Z_OK then history ++ bytes else history)

/-- Erasing the physical ghost gives the existing public data trace. -/
theorem DataHistory.original_trace {r : ZStreamRef} {h : Heap} {log : DataLog} {history : List UInt8}
    (trace : DataHistory r h log history) : InflateDataTrace 15 r h log := by
  induction trace with
  | init domain _platform _allocation run => exact .init domain run
  | caller _prior edit platform ih => exact .caller ih edit platform
  | step _prior platform actual ih => exact .step ih platform actual
  | dictionary _prior platform args input run ih =>
    simpa only [show ¬ ((15 : Int32).toInt < 0) from by decide, ite_false,
      decide_false, Bool.and_false, Bool.false_and, Bool.not_false, Bool.and_true] using
      (InflateDataTrace.dictionary ih platform args input run)

/-- Initialization and every actual edge establish the physical saved
history, rather than asking the caller to provide it at payload entry. -/
theorem DataHistory.invariant {r : ZStreamRef} {h : Heap} {log : DataLog} {history : List UInt8}
    (trace : DataHistory r h log history) :
    ∃ zs z s, DefaultStateJ h r zs z s ∧ DefAlloc z ∧
      (s.mode < CHECK → InflateDictionary h s (history.drop (history.length - 2 ^ s.wbits.toNat))) := by
  induction trace with
  | @init before after version domain platform allocation actual =>
    obtain ⟨computed, z, s, run, current, allocator, _null, dictionary, _reachable⟩ :=
      default_init_window_history before r version domain platform allocation
    have source : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, computed) := by
      simpa only [inflateInit_, DEF_WBITS] using run
    have same := Except.ok.inj (source.symm.trans actual)
    cases same
    exact ⟨before.nextBlk, z, s, current, allocator, fun _ => by simpa using dictionary⟩
  | @caller before after log history _prior edit platform ih =>
    obtain ⟨zs, z, s, current, allocator, dictionary⟩ := ih
    obtain ⟨stream, final, finalAllocator, retained⟩ :=
      rebuffer_default_history current allocator edit platform dictionary
    exact ⟨zs, stream, s, final, finalAllocator, retained⟩
  | @step before after log history flush rc input output used _prior _fit actual ih =>
    obtain ⟨zs, z, s, current, allocator, dictionary⟩ := ih
    obtain ⟨stream, state, final, finalAllocator, retained⟩ := dataStep_history current allocator actual dictionary
    exact ⟨zs, stream, state, final, finalAllocator, retained⟩
  | @dictionary before after log history p n bytes rc _prior _fit args input actual ih =>
    obtain ⟨zs, z, s, current, allocator, dictionary⟩ := ih
    obtain ⟨code, heap, state, run, final, retained⟩ := dictionary_history_guarded current allocator args input dictionary
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    exact ⟨zs, z, state, final, allocator, retained⟩

/-- From actual init and public calls, every active payload entry obtains
the concrete physical saved ring used by fast match semantics. -/
theorem DataHistory.saved {r : ZStreamRef} {h : Heap} {log : DataLog} {history : List UInt8}
    (trace : DataHistory r h log history) :
    ∃ zs z s, DefaultStateJ h r zs z s ∧ DefAlloc z ∧
      (s.mode < CHECK →
        (s.window = .null ∧ s.whave = 0 ∧ history.drop (history.length - 2 ^ s.wbits.toNat) = []) ∨
        ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧ h.ro w = false ∧
          a.size = 2 ^ s.wbits.toNat ∧
          Zlib.Inffast.Spec.MatchHistory.saved a s.wsize.toNat s.wnext.toNat s.whave.toNat 0 =
            history.drop (history.length - 2 ^ s.wbits.toNat)) := by
  obtain ⟨zs, z, s, current, allocator, dictionary⟩ := trace.invariant
  exact ⟨zs, z, s, current, allocator,
    fun active => dictionary_saved_or_lazy current.good (dictionary active)⟩

#print axioms dictionary_exists_bounded
#print axioms dictionary_history_guarded
#print axioms DataHistory.original_trace
#print axioms DataHistory.invariant
#print axioms DataHistory.saved
end Zlib.Inflate.Proofs.WindowHistory
