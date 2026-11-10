import ZlibF.Proof.«inflate.c.default-completion-domain-witness»
import ZlibF.Proof.«inflate.c.default-public-memory-contract»

namespace Zlib.Inflate.Proofs.CompletionSuccessWitness
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open CompletionDomainWitness
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def initialized : Heap := initOkHeap callerHeap (.tab 0) default 5 15
def initialStream : ZStream := resetKeepStream (initStream2 default callerHeap.nextBlk)
  (resetPre (reset2Pre 5 15 (initState (.tab 0))))
def stream : ZStream := { initialStream with next_in := .ref (.blk 1) 2, avail_in := 8, next_out := .ref (.blk 2) 0, avail_out := 1 }
def incoming : Heap := (ZStreamRef.tab 0).put initialized stream

theorem actual_init :
    C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) callerHeap = .ok (Z_OK, initialized) := by
  obtain ⟨fresh, _uniq, _globals, version, z, get, allocators, _null⟩ := caller_domain
  have same : z = (default : ZStream) := by
    have beforeGet : (ZStreamRef.tab 0).get callerHeap = some (default : ZStream) := by
      simp [ZStreamRef.get, callerHeap, witnessHeap]
    exact Option.some.inj (get.symm.trans beforeGet)
  subst z
  obtain ⟨nonnull, first⟩ := ZlibF.Spec.Public.Proofs.InflateInit.version_value_read version
  exact inflateInit2_success get fresh rfl allocators.1 allocators.2 nonnull first (by decide)

theorem initial_stream_get : (ZStreamRef.tab 0).get initialized = some initialStream := by rfl

def actualEndTag : Bool :=
  match C.run (inflate (some (.tab 0)) Z_FINISH) incoming with
  | .ok (rc, _) => rc == Z_STREAM_END
  | .error _ => false

set_option maxRecDepth 30000 in
theorem actual_end_tag : actualEndTag = true := by decide +kernel

theorem domain_on_concrete_heap :
    ∃ initialized z s incoming stream,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) callerHeap = .ok (Z_OK, initialized) ∧
      initialized = CompletionSuccessWitness.initialized ∧
      incoming = CompletionSuccessWitness.incoming ∧ stream = CompletionSuccessWitness.stream ∧
      InitDomain callerHeap (.tab 0) (.ref (.blk 1) 0) ∧
      Rebuffer initialized incoming (.tab 0) ∧
      (∃ trace : InflateProtocolTrace 15 (.tab 0) incoming {} false, ProtocolWindow.PlatformScope trace) ∧
      AllowedInflateProtocol 15 (.tab 0) incoming {} ∧
      StreamReachable .inflate incoming (.tab 0) ∧
      DefaultStateJ incoming (.tab 0) callerHeap.nextBlk stream s ∧ DefAlloc stream ∧
      initialized.streams 0 = some z ∧
      Fresh incoming ∧ Uniq incoming ∧ LibraryGlobals incoming ∧
      ZlibF.PlatformMemory.ByteObjectsFit incoming ∧ NoAllocationFailure incoming ∧
      StreamBuffers incoming (.tab 0) ∧ ActiveHeader incoming (.tab 0) ∧
      s.mode = HEAD ∧ s.bits = 0 ∧ s.havedict = 0 ∧
      stream.next_in = .ref (.blk 1) 2 ∧ stream.avail_in = 8 ∧
      stream.next_out = .ref (.blk 2) 0 ∧ stream.avail_out = 1 ∧
      stream.next_in ≠ .null ∧ stream.next_out ≠ .null ∧
      Api.Layer.Decodes .zlib 15 [] source [] ∧ Api.FullWindow .zlib 15 source ∧
      ([] : List UInt8) <+: source ∧
      Bytes incoming stream.next_in stream.avail_in.toNat (source.drop 0) ∧
      ([] : List UInt8).length ≤ ([] : List UInt8).length + stream.avail_out.toNat := by
  obtain ⟨initialized, z, s, initRun, initial, invariant, reachable⟩ :=
    inflate_default_state_initial callerHeap (.tab 0) (.ref (.blk 1) 0)
      caller_domain caller_platform rfl
  have heapEq : initialized = CompletionSuccessWitness.initialized :=
    congrArg Prod.snd (Except.ok.inj (initRun.symm.trans actual_init))
  subst initialized
  have streamEq : z = initialStream :=
    Option.some.inj (invariant.good.live.hz.symm.trans initial_stream_get)
  subst z
  obtain ⟨iz, is, initialGood, alloc, free, head, window,
    _wbits, _reqbits, _wrap, _reqwrap, _wsize, _whave, _wnext, _hold, bits, dict, header,
    _totalIn, _totalOut, _msg, frame, _ledger⟩ := initial
  have sameZ : iz = initialStream := Option.some.inj (initialGood.live.hz.symm.trans invariant.good.live.hz)
  have sameS : is = s := Option.some.inj (initialGood.live.hs.symm.trans invariant.good.live.hs)
  subst iz is
  have first := frame.2.2.2.2.2 1
    (by simp [Heap.live, callerHeap, witnessHeap, Heap.empty]) (by change ¬ (1 : Nat) = 0; decide)
  have second := frame.2.2.2.2.2 2
    (by simp [Heap.live, callerHeap, witnessHeap, Heap.empty]) (by change ¬ (2 : Nat) = 0; decide)
  let stream := { initialStream with next_in := .ref (.blk 1) 2, avail_in := 8, next_out := .ref (.blk 2) 0, avail_out := 1 }
  let incoming := (ZStreamRef.tab 0).put initialized stream
  have current : DefaultStateJ incoming (.tab 0) callerHeap.nextBlk stream s :=
    default_view_rebind invariant _ _ _ _
  have currentAlloc : DefAlloc stream := ⟨alloc, free⟩
  have inputGet : incoming.bytes 1 = some callerBytes := by simpa [incoming, callerHeap] using first.1
  have outputGet : incoming.bytes 2 = some (Array.replicate 32768 0) := by
    simpa [incoming, callerHeap, witnessHeap, Heap.empty] using second.1
  have outputRo : incoming.ro 2 = false := by
    simpa [incoming, callerHeap, witnessHeap, Heap.empty] using second.2.2.2.2.2.2.2
  have unowned : ∀ b, b = 1 ∨ b = 2 → ¬ StreamOwned incoming (.tab 0) b := by
    intro b caller owned
    rcases (current.good.streamOwned_iff b).mp owned with state | win
    · change b = 3 at state
      rcases caller with equal | equal <;> omega
    · rw [window] at win
      cases win
  have bytes : Bytes incoming stream.next_in stream.avail_in.toNat source :=
    Or.inr ⟨.blk 1, 2, callerBytes, rfl, inputGet, by change 2 + 8 ≤ 10; decide, rfl⟩
  have buffers : StreamBuffers incoming (.tab 0) := by
    refine ⟨stream, current.good.live.hz, Or.inr ⟨⟨source, bytes⟩, ?_, ?_⟩, Or.inr ⟨?_, ?_, ?_⟩, ?_⟩
    · intro impossible
      cases impossible
    · intro b root
      exact unowned b (Or.inl root)
    · exact ⟨[0], Or.inr ⟨.blk 2, 0, Array.replicate 32768 0, rfl, outputGet,
        by simp only [Array.size_replicate]; change 1 ≤ 32768; decide, by
          change [0] = ((Array.replicate 32768 (0 : UInt8)).toList.drop 0).take 1
          simp only [Array.toList_replicate, List.drop_zero, List.take_replicate]
          rfl⟩⟩
    · intro writing
      exact Or.inr ⟨.blk 2, 0, Array.replicate 32768 0, rfl, outputGet, outputRo,
        by simp only [Array.size_replicate]; change 1 ≤ 32768; decide⟩
    · intro b root
      exact unowned b (Or.inr root)
    · simp [Separate, stream]
  have streamRootUnowned : ¬ StreamOwned initialized (.tab 0) 0 := by
    intro owned
    rcases (invariant.good.streamOwned_iff 0).mp owned with stateRoot | win
    · change (0 : Nat) = 3 at stateRoot
      cases stateRoot
    · rw [window] at win
      cases win
  have beforeStream : initialized.streams 0 = some initialStream := invariant.good.live.hz
  have frameRebind : Frame initialized incoming (fun b => ¬ StreamOwned initialized (.tab 0) b) := by
    simp only [Frame, incoming, ZStreamRef.put, beforeStream, Nat.le_refl, true_and]
    intro b live outside
    have different : b ≠ 0 := by intro same; subst b; exact outside streamRootUnowned
    simp only [upd_ne _ _ _ _ different, and_self]
  have edit : Rebuffer initialized incoming (.tab 0) :=
    ⟨current.good.fresh, current.good.uniq, current.globals, frameRebind,
      initialStream, stream, invariant.good.live.hz, current.good.live.hz, rfl⟩
  have init2 : C.run (inflateInit2_ (some (.tab 0)) 15 (.ref (.blk 1) 0) 112) callerHeap =
      .ok (Z_OK, initialized) := initRun
  let trace : InflateProtocolTrace 15 (.tab 0) incoming {} false := .caller (.init caller_domain init2) edit
  have scope : ProtocolWindow.PlatformScope trace :=
    ProtocolWindow.PlatformScope.caller (prior := .init caller_domain init2) (edit := edit)
      (ProtocolWindow.PlatformScope.init (domain := caller_domain) (actual := init2) caller_platform)
      current.platform
  have noFailure : NoAllocationFailure incoming := by
    intro n
    simp only [incoming, ZStreamRef.put_allocOk]
    rw [← frame.2.1]
    rfl
  have active : ActiveHeader incoming (.tab 0) := by
    refine ⟨stream, current.good.live.hz, ?_, ?_⟩
    · intro i state statePointer stateGet
      have index : i = callerHeap.nextBlk := by simpa using statePointer.symm.trans current.good.live.zst
      subst i
      have sameState : state = s := Option.some.inj (stateGet.symm.trans current.good.live.hs)
      subst state
      exact Or.inl header
    · intro i state statePointer _
      rw [current.good.live.zst] at statePointer
      cases statePointer
  exact ⟨CompletionSuccessWitness.initialized, initialStream, s, incoming, stream, initRun, rfl, rfl, rfl, caller_domain, edit, ⟨trace, scope⟩,
    ⟨false, trace⟩, .rebuffer reachable edit, current, currentAlloc, invariant.good.live.hz,
    current.good.fresh, current.good.uniq, current.globals, current.platform, noFailure, buffers, active,
    head, bits, dict, rfl, rfl, rfl, rfl, (by intro impossible; cases impossible),
    (by intro impossible; cases impossible), source_decodes, Or.inl rfl, List.nil_prefix,
    bytes, Nat.zero_le _⟩


theorem actual_end_run :
    ∃ after, C.run (inflate (some (.tab 0)) Z_FINISH) incoming = .ok (Z_STREAM_END, after) := by
  have tag := actual_end_tag
  cases actual : C.run (inflate (some (.tab 0)) Z_FINISH) incoming with
  | error fault => simp only [actualEndTag, actual] at tag; cases tag
  | ok pair =>
    obtain ⟨rc, after⟩ := pair
    have ended : rc = Z_STREAM_END := by simpa only [actualEndTag, actual, beq_iff_eq] using tag
    subst rc
    exact ⟨after, rfl⟩

/-- Check only the scalar observations of this concrete returning call;
the full memory/result proof below uses the real public preservation theorem. -/
def actualCountsTag : Bool :=
  match C.run (inflate (some (.tab 0)) Z_FINISH) incoming with
  | .ok (_, after) => match (ZStreamRef.tab 0).get after with
    | some z => z.avail_in == 0 && z.avail_out == 1 && z.total_in == 8 && z.total_out == 0
    | none => false
  | .error _ => false

set_option maxRecDepth 30000 in
theorem actual_counts_tag : actualCountsTag = true := by decide +kernel

/-- A nonvacuous actual default init/rebuffer/data-call success. The same
concrete admitted heap returns END, consumes all eight stream bytes and
produces the independently specified empty output. The full default state
relation, terminal mode and exact caller frame/ledger are retained.
This finite instance is not the universal public completion theorem. -/
theorem default_empty_stream_actual_completion :
    ∃ beforeState after finalStream finalState,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) callerHeap = .ok (Z_OK, initialized) ∧
      Rebuffer initialized incoming (.tab 0) ∧ AllowedInflateProtocol 15 (.tab 0) incoming {} ∧
      DefaultStateJ incoming (.tab 0) callerHeap.nextBlk stream beforeState ∧
      C.run (inflate (some (.tab 0)) Z_FINISH) incoming = .ok (Z_STREAM_END, after) ∧
      DefaultStateJ after (.tab 0) callerHeap.nextBlk finalStream finalState ∧ DefAlloc finalStream ∧
      finalState.mode = DONE ∧ finalStream.avail_in = 0 ∧ finalStream.avail_out = 1 ∧
      finalStream.total_in = 8 ∧ finalStream.total_out = 0 ∧
      StreamAccounting stream finalStream 8 0 ∧ Bytes after stream.next_out 0 [] ∧
      Api.Layer.Decodes .zlib 15 [] source [] ∧
      BufferFrame incoming after
        (fun b => StreamRoot (.tab 0) b ∨ InflateOwned callerHeap.nextBlk beforeState b)
        [⟨stream.next_out, 0⟩] ∧
      LiveChange incoming after
        (fun b => InflateOwned callerHeap.nextBlk finalState b ∧ ¬ incoming.live b) (fun _ => False) := by
  obtain ⟨oldInitialized, oldZ, s, oldIncoming, oldStream, _initRun, sameInitialized,
    sameIncoming, sameStream, _domain, edit, _scope, allowed, _reachable, current, allocator,
    _get, _fresh, _uniq, _globals, _fit, _noFailure, buffers, _active, _head, _bits, _dict,
    _nextIn, _availIn, _nextOut, _availOut, _nonNullIn, _nonNullOut, format, _full,
    _prefix, _bytes, _room⟩ := domain_on_concrete_heap
  subst oldInitialized oldIncoming oldStream
  obtain ⟨rc, after, finalStream, finalState, used, output, run, final, finalAllocator,
    _freed, account, observed, _totals, _progress, _codes, _memory, modes, frame, ledger⟩ :=
    inflate_default_view_public_memory_contract current allocator buffers Z_FINISH
  have ended : rc = Z_STREAM_END := by
    simpa only [actualEndTag, run, beq_iff_eq] using actual_end_tag
  subst rc
  have counts : finalStream.avail_in = 0 ∧ finalStream.avail_out = 1 ∧
      finalStream.total_in = 8 ∧ finalStream.total_out = 0 := by
    simpa only [actualCountsTag, run, final.good.live.hz, Bool.and_eq_true, beq_iff_eq, and_assoc] using actual_counts_tag
  obtain ⟨inputEmpty, outputRoom, totalIn, totalOut⟩ := counts
  have consumed : used = 8 := by
    have inputCount := account.2.2.1
    rw [inputEmpty] at inputCount
    change 0 + used = 8 at inputCount
    omega
  have outputLength : output.length = 0 := by
    have outputCount := account.2.2.2.1
    rw [outputRoom] at outputCount
    change 1 + output.length = 1 at outputCount
    omega
  have empty : output = [] := List.eq_nil_of_length_eq_zero outputLength
  subst output used
  exact ⟨s, after, finalStream, finalState, actual_init, edit, allowed, current, run,
    final, finalAllocator, modes.1 rfl, inputEmpty, outputRoom, totalIn, totalOut,
    account, observed, format, frame, ledger⟩

#print axioms actual_init
#print axioms initial_stream_get
#print axioms actual_end_tag
#print axioms domain_on_concrete_heap
#print axioms actual_end_run
#print axioms actual_counts_tag
#print axioms default_empty_stream_actual_completion
end Zlib.Inflate.Proofs.CompletionSuccessWitness
