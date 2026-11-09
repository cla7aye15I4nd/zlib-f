import ZlibF.Proof.«inflate.c.logical-window-history»
import ZlibF.Proof.«inflate.c.havedict-public»
import ZlibF.Proof.«public-inflate-protocol»

namespace Zlib.Inflate.Proofs.ProtocolWindow
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.WindowHistory
set_option autoImplicit false

/-- The accepted object-size environment is observed at initialization
and each caller edit. No constructor assumes a decoder invariant. -/
inductive PlatformScope {r : ZStreamRef} : {h : Heap} → {log : DataLog} → {pending : Bool} →
    InflateProtocolTrace 15 r h log pending → Prop where
  | init {before after : Heap} {version : BPtr} {domain : InitDomain before r version}
      {actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, after)} :
      ZlibF.PlatformMemory.ByteObjectsFit before → PlatformScope (.init domain actual)
  | caller {before after : Heap} {log : DataLog} {pending : Bool}
      {prior : InflateProtocolTrace 15 r before log pending} {edit : Rebuffer before after r} :
      PlatformScope prior → ZlibF.PlatformMemory.ByteObjectsFit after → PlatformScope (.caller prior edit)
  | step {before after : Heap} {log : DataLog} {pending : Bool} {flush rc : Int32}
      {input output : List UInt8} {used : Nat} {prior : InflateProtocolTrace 15 r before log pending}
      {actual : DataStep .inflate before after r flush rc input output used} :
      PlatformScope prior → PlatformScope (.step prior actual)
  | dictionary {before after : Heap} {log : DataLog} {pending : Bool}
      {source : BPtr} {n : UInt32} {bytes : List UInt8} {rc : Int32}
      {prior : InflateProtocolTrace 15 r before log pending}
      {arguments : StreamArguments before r (.inflateSetDictionary (some r) source n)}
      {input : Bytes before source n.toNat bytes}
      {actual : C.run (inflateSetDictionary (some r) source n) before = .ok (rc, after)}
      {allowed : (15 : Int32).toInt < 0 ∨ rc ≠ Z_OK ∨ pending = true} :
      PlatformScope prior → PlatformScope (.dictionary prior arguments input actual allowed)

/-- A successful actual init itself excludes allocation failure. This is
not an extra caller obligation of the platform-scoped protocol trace. -/
theorem successful_init_allocation
    {before initialized : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain before r version)
    (actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, initialized)) :
    before.allocOk before.nalloc = true := by
  apply Classical.byContradiction
  intro failed
  obtain ⟨fresh, _uniq, _globals, validVersion, z, get, allocators, _null⟩ := domain
  obtain ⟨nonnull, first⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read validVersion
  have failure := inflateInit2_memfail (w := 15) get fresh failed allocators.1 allocators.2 nonnull first
  change inflateInit2_ (some r) 15 version 112 before = .ok (Z_OK, initialized) at actual
  rw [actual] at failure
  cases failure

theorem history_header_fields
    {r : ZStreamRef} {h : Heap} {log : DataLog} {physical : List UInt8}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (history : DataHistory r h log physical) (current : DefaultStateJ h r zs z s) :
    s.wrap = 5 ∧ (s.mode ≤ DICT → log.output = []) := by
  obtain ⟨index, stream, state, good, _allocator, _dictionary, wrap, low, _suffix⟩ := history.logical_suffix
  have sameZ : stream = z := Option.some.inj (good.good.live.hz.symm.trans current.good.live.hz)
  subst stream
  have sameIndex : index = zs := by
    simpa using good.good.live.zst.symm.trans current.good.live.zst
  subst index
  have sameState : state = s := Option.some.inj (good.good.live.hs.symm.trans current.good.live.hs)
  simpa only [sameState] using And.intro wrap low

/-- The protocol token and the actual installed flag are related by the
same source executions. Physical history equals logical dictionary plus
observed output; no one-installation premise is imposed on callers. -/
theorem exact_physical_history
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : PlatformScope trace) :
    ∃ physical, DataHistory r h log physical ∧ physical = log.dictionary ++ log.output ∧
      ∃ zs z s, DefaultStateJ h r zs z s ∧ DefAlloc z ∧
        (pending = true → s.havedict = 0) ∧ (s.havedict = 0 → log.dictionary = []) := by
  induction scope with
  | @init before after version domain actual platform =>
    have allocation := successful_init_allocation domain actual
    have history : DataHistory r after {} [] := .init domain platform allocation actual
    obtain ⟨computed, z, s, run, initial, current, _reachable⟩ :=
      inflate_default_state_initial before r version domain platform allocation
    have source : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, computed) := by
      simpa only [inflateInit_, DEF_WBITS] using run
    have same := Except.ok.inj (source.symm.trans actual)
    cases same
    obtain ⟨initialZ, initialS, good, alloc, free, _head, _null, _wb, _req,
      _wrap, _reqWrap, _size, _have, _next, _hold, _bits, missing, _rest⟩ := initial
    have sameZ : initialZ = z := Option.some.inj (good.live.hz.symm.trans current.good.live.hz)
    have sameS : initialS = s := Option.some.inj (good.live.hs.symm.trans current.good.live.hs)
    subst initialZ initialS
    exact ⟨[], history, rfl, before.nextBlk, z, s, current, ⟨alloc, free⟩,
      (by intro impossible; cases impossible), (fun _ => rfl)⟩
  | @caller before after log pending prior edit earlier platform ih =>
    obtain ⟨physical, history, exactHistory, zs, z, s, current, allocator, token, empty⟩ := ih
    obtain ⟨stream, final⟩ := rebuffer_default_state current edit platform
    obtain ⟨other, fields, good⟩ := rebuffer_inflate_good current.good edit
    have same : other = stream := Option.some.inj (good.live.hz.symm.trans final.good.live.hz)
    subst other
    have finalAllocator : DefAlloc stream := by rw [fields]; exact allocator
    exact ⟨physical, .caller history edit platform, exactHistory, zs, stream, s,
      final, finalAllocator, token, empty⟩
  | @step before after log pending flush rc input output used prior actual earlier ih =>
    obtain ⟨physical, history, exactHistory, zs, z, s, current, allocator, token, empty⟩ := ih
    have nextHistory : DataHistory r after
        { log with
          input := log.input ++ input.take used
          output := log.output ++ output
          result := rc
          finished := log.finished || rc == Z_STREAM_END } (physical ++ output) :=
      .step history actual
    obtain ⟨index, stream, state, next, finalAllocator, _stored⟩ := nextHistory.invariant
    have sameIndex : index = zs := by
      have runGood := inflate_default_view_public_memory_contract current allocator
      have actualCopy := actual
      obtain ⟨beforeZ, afterZ, beforeGet, afterGet, buffers, _⟩ := actualCopy
      obtain ⟨code, computed, returnedZ, returnedS, consumed, emitted, run, returnedJ, _rest⟩ :=
        runGood buffers flush
      obtain ⟨_z0, _z1, _g0, _g1, _buf, _header, _inp, _used, _out, source⟩ := actual
      have eqRun := Except.ok.inj (run.symm.trans source)
      cases eqRun
      have sameZ : stream = returnedZ := Option.some.inj (next.good.live.hz.symm.trans returnedJ.good.live.hz)
      subst stream
      simpa using next.good.live.zst.symm.trans returnedJ.good.live.zst
    subst index
    have preserved := HaveDictPublic.dataStep_havedict_unchanged current allocator actual next.good
    refine ⟨physical ++ output, nextHistory, ?_, zs, stream, state, next, finalAllocator, ?_, ?_⟩
    · simp only [exactHistory, List.append_assoc]
    · intro requested
      have code : rc = Z_NEED_DICT := by simpa using requested
      subst rc
      exact HaveDictPublic.dataStep_need_dictionary_missing current allocator actual next.good
    · intro missing
      exact empty (preserved.symm.trans missing)
  | @dictionary before after log pending source n bytes rc prior arguments input actual allowed earlier ih =>
    obtain ⟨physical, history, exactHistory, zs, z, s, current, allocator, token, empty⟩ := ih
    obtain ⟨represented, bound, stored⟩ := dictionary_exists_bounded current.good
    have old : InflateDictionary before s (represented.drop (represented.length - 2 ^ s.wbits.toNat)) := by
      simpa only [Nat.sub_eq_zero_of_le bound, List.drop_zero] using stored
    obtain ⟨code, computed, state, run, final, _outcome⟩ :=
      inflateSetDictionary_window_history current allocator arguments input old
    have same := Except.ok.inj (run.symm.trans actual)
    cases same
    have fields := HaveDictPublic.dictionary_havedict_observed current allocator arguments actual final.good.live.hs
    have nextHistory := DataHistory.dictionary history arguments input actual
    have wrapped := (history_header_fields history current).1
    have low := (history_header_fields history current).2
    by_cases success : rc = Z_OK
    · subst rc
      have requested : pending = true := by
        rcases allowed with raw | refused | request
        · exact False.elim ((by decide : ¬ ((15 : Int32).toInt < 0)) raw)
        · exact False.elim (refused rfl)
        · exact request
      have missing := token requested
      have noDictionary := empty missing
      have mode := dictionary_success_in_DICT current.good wrapped actual
      have noOutput := low (by rw [mode]; exact UInt32.le_refl _)
      have oldPhysical : physical = [] := by simpa only [noDictionary, noOutput, List.nil_append] using exactHistory
      refine ⟨bytes, ?_, ?_, zs, z, state, final, allocator, ?_, ?_⟩
      · simpa only [oldPhysical, List.nil_append, ite_true,
          show ¬ ((15 : Int32).toInt < 0) from by decide, ite_false,
          decide_false, Bool.and_false, Bool.false_and, Bool.not_false, Bool.and_true] using nextHistory
      · simp only [ite_true, noOutput, List.append_nil,
          show ¬ ((15 : Int32).toInt < 0) from by decide, ite_false]
      · intro impossible
        change false = true at impossible
        cases impossible
      · intro zero
        have one : state.havedict = 1 := by simpa only [ite_true] using fields
        rw [one] at zero
        cases zero
    · refine ⟨physical, ?_, ?_, zs, z, state, final, allocator, ?_, ?_⟩
      · simpa only [ite_eq_right success,
          show ¬ ((15 : Int32).toInt < 0) from by decide, ite_false,
          decide_false, Bool.and_false, Bool.false_and, Bool.not_false, Bool.and_true] using nextHistory
      · simpa only [ite_eq_right success] using exactHistory
      · intro requested
        have request : pending = true := by simpa only [show ¬ ((15 : Int32).toInt < 0) from by decide, ite_false, ite_eq_right success] using requested
        have unchanged : state.havedict = s.havedict := by simpa only [ite_eq_right success] using fields
        exact unchanged.trans (token request)
      · intro missing
        have unchanged : state.havedict = s.havedict := by simpa only [ite_eq_right success] using fields
        have oldMissing : s.havedict = 0 := unchanged.symm.trans missing
        simpa only [ite_eq_right success] using empty oldMissing

/-- Every active decoder reached by the admitted protocol has precisely
the retained logical history, not merely a suffix of a larger physical
dictionary. Null lazy windows are accounted for separately. -/
theorem saved_logical_exact
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : PlatformScope trace) :
    ∃ zs z s, DefaultStateJ h r zs z s ∧ DefAlloc z ∧ s.wrap = 5 ∧
      (s.mode ≤ DICT → log.output = []) ∧
      (s.mode < CHECK →
        (s.window = .null ∧ s.whave = 0 ∧
          (log.dictionary ++ log.output).drop
            ((log.dictionary ++ log.output).length - 2 ^ s.wbits.toNat) = []) ∨
        ∃ w a, s.window = .ref (.blk w) 0 ∧ h.bytes w = some a ∧ h.ro w = false ∧
          a.size = 2 ^ s.wbits.toNat ∧
          Zlib.Inffast.Spec.MatchHistory.saved a s.wsize.toNat s.wnext.toNat s.whave.toNat 0 =
            (log.dictionary ++ log.output).drop
              ((log.dictionary ++ log.output).length - 2 ^ s.wbits.toNat)) := by
  obtain ⟨physical, history, equality, _zs, _z, _s, _current, _allocator, _token, _empty⟩ :=
    exact_physical_history trace scope
  obtain ⟨zs, z, s, current, allocator, saved⟩ := history.saved
  obtain ⟨wrap, low⟩ := history_header_fields history current
  exact ⟨zs, z, s, current, allocator, wrap, low, fun active => by
    simpa only [equality] using saved active⟩

/-- The public protocol-admission predicate supplies the actual trace.
The only further scope is the accepted per-object platform environment. -/
theorem allowed_saved_logical_exact
    {r : ZStreamRef} {h : Heap} {log : DataLog}
    (allowed : AllowedInflateProtocol 15 r h log)
    (scope : PlatformScope allowed.choose_spec) :
    ∃ zs z s, DefaultStateJ h r zs z s ∧ DefAlloc z ∧
      (s.mode < CHECK → InflateDictionary h s
        ((log.dictionary ++ log.output).drop
          ((log.dictionary ++ log.output).length - 2 ^ s.wbits.toNat))) := by
  obtain ⟨physical, history, equality, _rest⟩ := exact_physical_history allowed.choose_spec scope
  obtain ⟨zs, z, s, current, allocator, dictionary⟩ := history.invariant
  exact ⟨zs, z, s, current, allocator, fun active => by
    simpa only [equality] using dictionary active⟩

#print axioms successful_init_allocation
#print axioms history_header_fields
#print axioms exact_physical_history
#print axioms saved_logical_exact
#print axioms allowed_saved_logical_exact
end Zlib.Inflate.Proofs.ProtocolWindow
