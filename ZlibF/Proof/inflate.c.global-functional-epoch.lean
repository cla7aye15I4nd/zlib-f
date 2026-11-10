import ZlibF.Proof.«inflate.c.protocol-window-public-step»

namespace Zlib.Inflate.Proofs.FunctionalEpoch
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs.WindowHistory
set_option autoImplicit false

/-- The two independent functional clauses required of a default data epoch.
The first interprets arbitrary actual END output. The second interprets a
prefix of an independently valid source. Neither clause implies completion. -/
structure FunctionalLedger (log : DataLog) (dictionary : List UInt8) : Prop where
  ended : log.result = Z_STREAM_END →
    Api.Layer.Decodes .zlib 15 dictionary log.input log.output
  valid : ∀ source decoded,
    Api.Layer.Decodes .zlib 15 dictionary source decoded →
    Api.FullWindow .zlib 15 source → log.input <+: source →
    log.output <+: decoded ∧ log.result ≠ Z_DATA_ERROR ∧
      (log.result = Z_STREAM_END → log.input = source ∧ log.output = decoded)

/-- The ordinary ledger is dictionary-parametric before actual installation.
After installation it is specialized to the actual logical dictionary. The
source-derived decoder relation is carried as a conclusion, not in a trace
constructor. A residual parser phase is additionally needed to advance payload
calls; this necessary functional projection alone is not a liveness invariant. -/
def Meaning (h : Heap) (r : ZStreamRef) (log : DataLog) : Prop :=
  ∃ zs z s, DefaultStateJ h r zs z s ∧ DefAlloc z ∧
    ∀ dictionary, (s.havedict = 0 ∨ dictionary = log.dictionary) →
      FunctionalLedger log dictionary

def credit (log : DataLog) (input output : List UInt8) (used : Nat) (rc : Int32) : DataLog :=
  { log with
    input := log.input ++ input.take used
    output := log.output ++ output
    result := rc
    finished := log.finished || rc == Z_STREAM_END }

def install (log : DataLog) (bytes : List UInt8) (rc : Int32) : DataLog :=
  { log with dictionary := if rc = Z_OK then bytes else log.dictionary }

theorem FunctionalLedger.empty {log : DataLog} {dictionary : List UInt8}
    (empty : log.output = []) (notEnd : log.result ≠ Z_STREAM_END)
    (notError : log.result ≠ Z_DATA_ERROR) : FunctionalLedger log dictionary := by
  refine ⟨fun ended => False.elim (notEnd ended), ?_⟩
  intro source decoded _format _full _prefix
  refine ⟨?_, notError, fun ended => False.elim (notEnd ended)⟩
  rw [empty]
  exact List.nil_prefix

theorem Meaning.functional_clauses {h : Heap} {r : ZStreamRef} {log : DataLog}
    (meaning : Meaning h r log) :
    (log.singleDictionary = true → log.result = Z_STREAM_END →
      Api.Layer.Decodes .zlib 15 log.dictionary log.input log.output) ∧
    (∀ source decoded, Api.Layer.Decodes .zlib 15 log.dictionary source decoded →
      log.singleDictionary = true → Api.FullWindow .zlib 15 source → log.input <+: source →
      log.output <+: decoded ∧ log.result ≠ Z_DATA_ERROR ∧
        (log.result = Z_STREAM_END → log.input = source ∧ log.output = decoded)) := by
  obtain ⟨zs, z, s, _current, _allocator, all⟩ := meaning
  have ledger := all log.dictionary (Or.inr rfl)
  exact ⟨fun _ => ledger.ended, fun source decoded format _ => ledger.valid source decoded format⟩

theorem Meaning.of_empty {h : Heap} {r : ZStreamRef} {log : DataLog}
    {zs : Nat} {z : ZStream} {s : InflateState}
    (current : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (empty : log.output = []) (notEnd : log.result ≠ Z_STREAM_END)
    (notError : log.result ≠ Z_DATA_ERROR) : Meaning h r log :=
  ⟨zs, z, s, current, allocator, fun _ _ => FunctionalLedger.empty empty notEnd notError⟩

theorem Meaning.init {before after : Heap} {r : ZStreamRef} {version : BPtr}
    (domain : InitDomain before r version)
    (actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, after))
    (platform : ZlibF.PlatformMemory.ByteObjectsFit before) : Meaning after r {} := by
  have trace : InflateProtocolTrace 15 r after {} false := .init domain actual
  have scope : ProtocolWindow.PlatformScope trace := .init (domain := domain) (actual := actual) platform
  obtain ⟨physical, history, _exact, zs, z, s, current, allocator, _token, _missing⟩ :=
    ProtocolWindow.exact_physical_history trace scope
  exact Meaning.of_empty current allocator rfl (by decide) (by decide)

theorem Meaning.rebuffer {h after : Heap} {r : ZStreamRef} {log : DataLog}
    (meaning : Meaning h r log) (edit : Rebuffer h after r)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit after) : Meaning after r log := by
  obtain ⟨zs, z, s, current, allocator, all⟩ := meaning
  obtain ⟨stream, final⟩ := rebuffer_default_state current edit platform
  obtain ⟨other, fields, good⟩ := rebuffer_inflate_good current.good edit
  have same : other = stream := Option.some.inj (good.live.hz.symm.trans final.good.live.hz)
  subst other
  refine ⟨zs, stream, s, final, ?_, all⟩
  rw [fields]
  exact allocator

/-- Actual source classification is transported to the exact DataStep state.
This does not assume a callee contract or a desired returned code. -/
theorem dataStep_returned_modes
    {h after : Heap} {r : ZStreamRef} {zs : Nat} {z stream : ZStream} {s state : InflateState}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (current : DefaultStateJ h r zs z s) (allocator : DefAlloc z)
    (actual : DataStep .inflate h after r flush rc input output used)
    (final : Good after r zs stream state) : ReturnedModes rc state := by
  obtain ⟨beforeZ, _afterZ, beforeGet, _afterGet, buffers, _header, _input,
    _used, _output, run⟩ := actual
  have sameZ : beforeZ = z := Option.some.inj (beforeGet.symm.trans current.good.live.hz)
  subst beforeZ
  obtain ⟨code, computed, returnedZ, returnedS, consumed, made, source, next, _alloc,
    _freed, _accounting, _observed, _totals, _progress, _codes, _memory, modes, _frame, _ledger⟩ :=
    inflate_default_view_public_memory_contract current allocator buffers flush
  have same := Except.ok.inj (source.symm.trans run)
  cases same
  have sameS : returnedS = state := Option.some.inj (next.good.live.hs.symm.trans final.live.hs)
  simpa only [sameS] using modes

theorem dataStep_observed_modes
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {flush rc : Int32} {input output : List UInt8} {used : Nat}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (actual : DataStep .inflate h after r flush rc input output used) :
    ∃ zs stream state, DefaultStateJ after r zs stream state ∧ DefAlloc stream ∧ ReturnedModes rc state := by
  obtain ⟨physical, history, _exact, _stateFacts⟩ := ProtocolWindow.exact_physical_history trace scope
  obtain ⟨zs, z, s, current, allocator, stored⟩ := history.invariant
  obtain ⟨stream, state, final, finalAllocator, _stored⟩ := dataStep_history current allocator actual stored
  exact ⟨zs, stream, state, final, finalAllocator, dataStep_returned_modes current allocator actual final.good⟩

/-- Every actual call returning in a header/dictionary mode establishes the
functional ledger without a source-validity premise. Output is source-proved
empty and END/DATA_ERROR are source-proved impossible in these modes. -/
theorem Meaning.early_step
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {flush rc : Int32} {input output : List UInt8} {used zs : Nat}
    {stream : ZStream} {state : InflateState}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (actual : DataStep .inflate h after r flush rc input output used)
    (getZ : r.get after = some stream) (stateRef : stream.state = some (.inflate zs))
    (getS : after.istates zs = some state) (low : state.mode ≤ DICT) :
    Meaning after r (credit log input output used rc) := by
  obtain ⟨physical, history, _exact, _stateFacts⟩ :=
    ProtocolWindow.exact_physical_history trace scope
  obtain ⟨index, z, s, current, allocator, stored⟩ := history.invariant
  obtain ⟨nextZ, nextS, next, nextAllocator, _stored⟩ :=
    dataStep_history current allocator actual stored
  have sameZ : nextZ = stream := Option.some.inj (next.good.live.hz.symm.trans getZ)
  subst nextZ
  have sameIndex : index = zs := by simpa using next.good.live.zst.symm.trans stateRef
  subst index
  have sameS : nextS = state := Option.some.inj (next.good.live.hs.symm.trans getS)
  subst nextS
  have modes := dataStep_returned_modes current allocator actual next.good
  have nextHistory := DataHistory.step history actual
  have empty := (ProtocolWindow.history_header_fields nextHistory next).2 low
  refine Meaning.of_empty next nextAllocator empty ?_ ?_
  · intro ended
    change rc = Z_STREAM_END at ended
    have impossible := low
    rw [modes.1 ended] at impossible
    exact (by decide : ¬ DONE ≤ DICT) impossible
  · intro error
    change rc = Z_DATA_ERROR at error
    have impossible := low
    rw [modes.2.2.1 error] at impossible
    exact (by decide : ¬ BAD ≤ DICT) impossible

/-- Literal translated entry check, including the real local allocation/free.
The returned heap need not equal the caller heap. -/
theorem entry_refused_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    (current : DefaultStateJ h r zs z s) (flush : Int32)
    (rejected : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true) :
    C.run (inflate (some r) flush) h =
      .ok (Z_STREAM_ERROR, freeWin (syncAlloc h) (syncBuf h)) ∧
    DefaultStateJ (freeWin (syncAlloc h) (syncBuf h)) r zs z s := by
  have allocated := default_state_syncAlloc current
  refine ⟨?_, allocated.free_local (syncAlloc_bytes_buf h)
    (by simp only [syncJunk, Array.size_ofFn])⟩
  unfold C.run inflate
  rw [bind_app, allocLocalB_run h current.good.fresh]
  simp only []
  rw [bind_app]
  simp only [bind_app, stateCheck_live allocated.good.live,
    bne_self_eq_false, Bool.false_eq_true, ite_false,
    ldZStream_ok allocated.good.live.hz, rejected, ite_true, pure_app]
  dsimp only [syncBuf]
  rw [freeBuf_run (syncAlloc_bytes_buf h) (syncAlloc_ro_buf h)]

theorem FunctionalLedger.refusal {log : DataLog} {dictionary input : List UInt8}
    (ledger : FunctionalLedger log dictionary) :
    FunctionalLedger (credit log input [] 0 Z_STREAM_ERROR) dictionary := by
  constructor
  · intro impossible
    change Z_STREAM_ERROR = Z_STREAM_END at impossible
    exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_STREAM_END) impossible)
  · intro source decoded format full received
    have oldPrefix : log.input <+: source := by simpa only [credit, List.take_zero, List.append_nil] using received
    have old := ledger.valid source decoded format full oldPrefix
    refine ⟨?_, ?_, ?_⟩
    · simpa only [credit, List.append_nil] using old.1
    · change Z_STREAM_ERROR ≠ Z_DATA_ERROR
      decide
    · intro impossible
      change Z_STREAM_ERROR = Z_STREAM_END at impossible
      exact False.elim ((by decide : Z_STREAM_ERROR ≠ Z_STREAM_END) impossible)

/-- Refusals preserve an already established functional ledger, including
after payload output. The constructor needs only the actual C entry guard. -/
theorem Meaning.refused {h after : Heap} {r : ZStreamRef} {log : DataLog}
    {flush rc : Int32} {input output : List UInt8} {used : Nat} {stream : ZStream}
    (meaning : Meaning h r log) (get : r.get h = some stream)
    (rejected : (stream.next_out == .null || (stream.next_in == .null && stream.avail_in != 0)) = true)
    (actual : DataStep .inflate h after r flush rc input output used) :
    Meaning after r (credit log input output used rc) := by
  obtain ⟨zs, z, s, current, allocator, all⟩ := meaning
  have sameZ : stream = z := Option.some.inj (get.symm.trans current.good.live.hz)
  subst stream
  obtain ⟨expected, final⟩ := entry_refused_state current flush rejected
  obtain ⟨z0, returned, get0, get1, _buffers, _header, _input, count, observed, source⟩ := actual
  have oldZ : z0 = z := Option.some.inj (get0.symm.trans current.good.live.hz)
  subst z0
  have same := Except.ok.inj (source.symm.trans expected)
  cases same
  have nextZ : returned = z := Option.some.inj (get1.symm.trans final.good.live.hz)
  subst returned
  have zero : used = 0 := by rw [count, Nat.sub_self]
  have noOutput : output = [] := WindowHistory.bytes_zero (by simpa only [Nat.sub_self] using observed)
  refine ⟨zs, z, s, final, allocator, ?_⟩
  intro dictionary compatible
  simpa only [zero, noOutput] using (FunctionalLedger.refusal (input := input) (all dictionary compatible))

theorem FunctionalLedger.install {log : DataLog} {dictionary bytes : List UInt8} {rc : Int32}
    (ledger : FunctionalLedger log dictionary) : FunctionalLedger (install log bytes rc) dictionary := by
  exact ⟨ledger.ended, ledger.valid⟩

/-- Both actual wrapped-setter branches preserve the functional ledger.
On success the source-derived protocol token gives havedict=0, so the old
parametric ledger can be specialized to the newly installed bytes. Failures
retain the flag, logical dictionary and token. -/
theorem Meaning.dictionary
    {h after : Heap} {r : ZStreamRef} {log : DataLog} {pending : Bool}
    {p : BPtr} {n : UInt32} {bytes : List UInt8} {rc : Int32}
    (trace : InflateProtocolTrace 15 r h log pending) (scope : ProtocolWindow.PlatformScope trace)
    (meaning : Meaning h r log)
    (arguments : StreamArguments h r (.inflateSetDictionary (some r) p n))
    (input : Bytes h p n.toNat bytes)
    (actual : C.run (inflateSetDictionary (some r) p n) h = .ok (rc, after))
    (allowed : (15 : Int32).toInt < 0 ∨ rc ≠ Z_OK ∨ pending = true) :
    Meaning after r (install log bytes rc) := by
  obtain ⟨zs, z, s, current, allocator, all⟩ := meaning
  obtain ⟨represented, bound, stored⟩ := dictionary_exists_bounded current.good
  have retained : s.mode < CHECK → InflateDictionary h s
      (represented.drop (represented.length - 2 ^ s.wbits.toNat)) := by
    intro _
    simpa only [Nat.sub_eq_zero_of_le bound, List.drop_zero] using stored
  obtain ⟨code, computed, state, source, final, _window⟩ :=
    dictionary_history_guarded current allocator arguments input retained
  have same := Except.ok.inj (source.symm.trans actual)
  cases same
  have fields := HaveDictPublic.dictionary_havedict_observed current allocator arguments actual final.good.live.hs
  refine ⟨zs, z, state, final, allocator, ?_⟩
  intro dictionary compatible
  apply FunctionalLedger.install
  apply all dictionary
  by_cases success : rc = Z_OK
  · have requested : pending = true := by
      rcases allowed with raw | refused | request
      · exact False.elim ((by decide : ¬ ((15 : Int32).toInt < 0)) raw)
      · exact False.elim (refused success)
      · exact request
    obtain ⟨physical, _history, _exact, index, stream, old, oldJ, _alloc, token, _empty⟩ :=
      ProtocolWindow.exact_physical_history trace scope
    have oldZ : stream = z := Option.some.inj (oldJ.good.live.hz.symm.trans current.good.live.hz)
    subst stream
    have oldIndex : index = zs := by simpa using oldJ.good.live.zst.symm.trans current.good.live.zst
    subst index
    have oldS : old = s := Option.some.inj (oldJ.good.live.hs.symm.trans current.good.live.hs)
    exact Or.inl (by simpa only [oldS] using token requested)
  · rcases compatible with missing | installed
    · exact Or.inl ((by simpa only [ite_eq_right success] using fields : state.havedict = s.havedict).symm.trans missing)
    · exact Or.inr (by simpa only [install, ite_eq_right success] using installed)

/-- Source-only selection of the protocol trace with proved global functional
cases. The early-step rule observes only the actual returned C mode. Payload,
next-block and trailer rules are deliberately absent until their actual
semantic producers are composed; no missing callee theorem is an assumption. -/
inductive CheckedEpoch (r : ZStreamRef) : {h : Heap} → {log : DataLog} → {pending : Bool} →
    InflateProtocolTrace 15 r h log pending → Prop where
  | init {before after : Heap} {version : BPtr} {domain : InitDomain before r version}
      {actual : C.run (inflateInit2_ (some r) 15 version 112) before = .ok (Z_OK, after)} :
      ZlibF.PlatformMemory.ByteObjectsFit before → CheckedEpoch r (.init domain actual)
  | caller {before after : Heap} {log : DataLog} {pending : Bool}
      {prior : InflateProtocolTrace 15 r before log pending} {edit : Rebuffer before after r} :
      CheckedEpoch r prior → ZlibF.PlatformMemory.ByteObjectsFit after → CheckedEpoch r (.caller prior edit)
  | early {before after : Heap} {log : DataLog} {pending : Bool}
      {prior : InflateProtocolTrace 15 r before log pending} {flush rc : Int32}
      {input output : List UInt8} {used zs : Nat} {stream : ZStream} {state : InflateState}
      {actual : DataStep .inflate before after r flush rc input output used} :
      CheckedEpoch r prior → r.get after = some stream → stream.state = some (.inflate zs) →
      after.istates zs = some state → state.mode ≤ DICT → CheckedEpoch r (.step prior actual)
  | refused {before after : Heap} {log : DataLog} {pending : Bool}
      {prior : InflateProtocolTrace 15 r before log pending} {flush rc : Int32}
      {input output : List UInt8} {used : Nat} {stream : ZStream}
      {actual : DataStep .inflate before after r flush rc input output used} :
      CheckedEpoch r prior → r.get before = some stream →
      (stream.next_out == .null || (stream.next_in == .null && stream.avail_in != 0)) = true →
      CheckedEpoch r (.step prior actual)
  | dictionary {before after : Heap} {log : DataLog} {pending : Bool}
      {prior : InflateProtocolTrace 15 r before log pending} {p : BPtr} {n : UInt32}
      {bytes : List UInt8} {rc : Int32}
      {arguments : StreamArguments before r (.inflateSetDictionary (some r) p n)}
      {input : Bytes before p n.toNat bytes}
      {actual : C.run (inflateSetDictionary (some r) p n) before = .ok (rc, after)}
      {allowed : (15 : Int32).toInt < 0 ∨ rc ≠ Z_OK ∨ pending = true} :
      CheckedEpoch r prior → CheckedEpoch r (.dictionary prior arguments input actual allowed)

theorem CheckedEpoch.checked {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    {trace : InflateProtocolTrace 15 r h log pending} (selected : CheckedEpoch r trace) :
    ProtocolWindow.PlatformScope trace ∧ Meaning h r log := by
  induction selected with
  | @init before after version domain actual platform =>
    exact ⟨.init (domain := domain) (actual := actual) platform, Meaning.init domain actual platform⟩
  | @caller before after log pending prior edit selected platform ih =>
    exact ⟨.caller (edit := edit) ih.1 platform, ih.2.rebuffer edit platform⟩
  | @early before after log pending prior flush rc input output used zs stream state actual selected getZ ref getS low ih =>
    exact ⟨.step (actual := actual) ih.1, Meaning.early_step prior ih.1 actual getZ ref getS low⟩
  | @refused before after log pending prior flush rc input output used stream actual selected get guard ih =>
    exact ⟨.step (actual := actual) ih.1, ih.2.refused get guard actual⟩
  | @dictionary before after log pending prior p n bytes rc arguments input actual allowed selected ih =>
    refine ⟨.dictionary (arguments := arguments) (input := input) (actual := actual) (allowed := allowed) ih.1, ?_⟩
    simpa only [install, show ¬ ((15 : Int32).toInt < 0) from by decide, ite_false,
      decide_false, Bool.and_false, Bool.false_and, Bool.not_false, Bool.and_true] using
      Meaning.dictionary prior ih.1 ih.2 arguments input actual allowed

/-- The checked composition core simultaneously exposes the exact physical
history, actual decoder representation, protocol flag relation, saved logical
window and dictionary-parametric functional ledger on one actual state. -/
theorem CheckedEpoch.data_epoch_invariant
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    {trace : InflateProtocolTrace 15 r h log pending} (selected : CheckedEpoch r trace) :
    ∃ physical zs z s,
      DataHistory r h log physical ∧ physical = log.dictionary ++ log.output ∧
      DefaultStateJ h r zs z s ∧ DefAlloc z ∧ s.wrap = 5 ∧
      (s.mode ≤ DICT → log.output = []) ∧
      (pending = true → s.havedict = 0) ∧ (s.havedict = 0 → log.dictionary = []) ∧
      (s.mode < CHECK → InflateDictionary h s
        ((log.dictionary ++ log.output).drop
          ((log.dictionary ++ log.output).length - 2 ^ s.wbits.toNat))) ∧
      (∀ dictionary, (s.havedict = 0 ∨ dictionary = log.dictionary) → FunctionalLedger log dictionary) := by
  obtain ⟨scope, meaning⟩ := selected.checked
  obtain ⟨physical, history, equality, zs, z, s, current, allocator, token, emptyDictionary⟩ :=
    ProtocolWindow.exact_physical_history trace scope
  obtain ⟨index, stream, state, observed, _allocator, dictionary⟩ := history.invariant
  have sameZ : stream = z := Option.some.inj (observed.good.live.hz.symm.trans current.good.live.hz)
  subst stream
  have sameIndex : index = zs := by simpa using observed.good.live.zst.symm.trans current.good.live.zst
  subst index
  have sameS : state = s := Option.some.inj (observed.good.live.hs.symm.trans current.good.live.hs)
  subst state
  obtain ⟨otherIndex, otherZ, otherS, other, _allocator, ledger⟩ := meaning
  have sameZ : otherZ = z := Option.some.inj (other.good.live.hz.symm.trans current.good.live.hz)
  subst otherZ
  have sameIndex : otherIndex = zs := by simpa using other.good.live.zst.symm.trans current.good.live.zst
  subst otherIndex
  have sameS : otherS = s := Option.some.inj (other.good.live.hs.symm.trans current.good.live.hs)
  subst otherS
  obtain ⟨wrap, low⟩ := ProtocolWindow.history_header_fields history current
  exact ⟨physical, zs, z, s, history, equality, current, allocator, wrap, low, token,
    emptyDictionary, (by simpa only [equality] using dictionary), ledger⟩

/-- This is exactly the default functional sequence projection for the
source-only checked epoch. It makes no claim about omitted payload calls,
unrestricted sequence safety, other configurations, or InflateCompletes. -/
theorem CheckedEpoch.functional_clauses
    {r : ZStreamRef} {h : Heap} {log : DataLog} {pending : Bool}
    {trace : InflateProtocolTrace 15 r h log pending} (selected : CheckedEpoch r trace) :
    (log.singleDictionary = true → log.result = Z_STREAM_END →
      Api.Layer.Decodes .zlib 15 log.dictionary log.input log.output) ∧
    (∀ source decoded, Api.Layer.Decodes .zlib 15 log.dictionary source decoded →
      log.singleDictionary = true → Api.FullWindow .zlib 15 source → log.input <+: source →
      log.output <+: decoded ∧ log.result ≠ Z_DATA_ERROR ∧
        (log.result = Z_STREAM_END → log.input = source ∧ log.output = decoded)) :=
  selected.checked.2.functional_clauses

/-- The entry-refusal branch of completion is closed on the actual source.
It does not require a valid compressed stream or enough output capacity. -/
theorem completion_entry_refusal
    {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (current : DefaultStateJ h r zs z s) (flush : Int32)
    (rejected : z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0)) :
    ∃ rc after, C.run (inflate (some r) flush) h = .ok (rc, after) ∧
      rc = Z_STREAM_ERROR ∧
      (z.next_out = .null ∨ (z.next_in = .null ∧ z.avail_in ≠ 0)) ∧ Good after r zs z s := by
  have guard : (z.next_out == .null || (z.next_in == .null && z.avail_in != 0)) = true := by
    rcases rejected with null | ⟨null, nonzero⟩
    · simp [null]
    · simp [null, nonzero]
  obtain ⟨actual, final⟩ := entry_refused_state current flush guard
  exact ⟨Z_STREAM_ERROR, _, actual, rfl, rejected, final.good⟩

#print axioms Meaning.functional_clauses
#print axioms Meaning.init
#print axioms Meaning.rebuffer
#print axioms dataStep_returned_modes
#print axioms dataStep_observed_modes
#print axioms Meaning.early_step
#print axioms entry_refused_state
#print axioms Meaning.refused
#print axioms Meaning.dictionary
#print axioms CheckedEpoch.checked
#print axioms CheckedEpoch.data_epoch_invariant
#print axioms CheckedEpoch.functional_clauses
#print axioms completion_entry_refusal

end Zlib.Inflate.Proofs.FunctionalEpoch
