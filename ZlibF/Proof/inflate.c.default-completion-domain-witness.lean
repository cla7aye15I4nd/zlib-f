import ZlibF.Proof.«inflate.c.default-view-witness»
import ZlibF.Proof.«inflate.c.protocol-window-history»
import ZlibF.Spec.Api.Examples

namespace Zlib.Inflate.Proofs.CompletionDomainWitness
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false
set_option maxRecDepth 8192

/-- A fixed-Huffman empty zlib stream, including its Adler-32 trailer. -/
def source : List UInt8 := [0x78, 0x9c, 0x03, 0x00, 0x00, 0x00, 0x00, 0x01]
def callerBytes : Array UInt8 := #[49, 0, 0x78, 0x9c, 0x03, 0x00, 0x00, 0x00, 0x00, 0x01]
def callerHeap : Heap := { witnessHeap with bytes := upd witnessHeap.bytes 1 (some callerBytes) }

theorem source_decodes : Api.Layer.Decodes .zlib 15 [] source [] := by
  refine ⟨?_, Or.inr ⟨0x78, rfl, by decide⟩⟩
  refine ⟨0x78, 0x9c, [], _, rfl, by decide, ?_, ?_⟩
  · intro _
    exact ⟨rfl, _, .last rfl rfl (.fixed (.eob rfl)), by decide⟩
  · intro impossible
    exact False.elim ((by decide : ¬ (0x9c : UInt8).toNat / 32 % 2 = 1) impossible)

theorem caller_domain : InitDomain callerHeap (.tab 0) (.ref (.blk 1) 0) := by
  have oldGet : witnessHeap.bytes 1 = some #[49, 0] := by simp [witnessHeap, Heap.empty]
  have shape := shape_setB oldGet callerBytes
  refine ⟨shape.fresh rfl ZlibF.Spec.Public.Proofs.InflateInit.public_witness_fresh,
    shape.uniq ZlibF.Spec.Public.Proofs.InflateInit.public_witness_uniq, rfl, ?_, default, ?_, ?_, rfl⟩
  · exact Or.inr ⟨49, rfl, Or.inr ⟨.blk 1, 0, callerBytes, rfl, by simp [callerHeap, Space.get],
        by decide, rfl⟩⟩
  · simp [ZStreamRef.get, callerHeap, witnessHeap]
  · exact ⟨Or.inl rfl, Or.inl rfl⟩

set_option maxRecDepth 8192 in
theorem caller_platform : ZlibF.PlatformMemory.ByteObjectsFit callerHeap := by
  intro ref a get
  cases ref with
  | blk b =>
    by_cases one : b = 1
    · subst b
      simp only [BRef.get_blk, callerHeap, upd_same] at get
      cases get
      decide
    · have oldGet : Space.get witnessHeap (BRef.blk b) = some a := by
        simpa [Space.get, callerHeap, upd_ne _ _ _ _ one] using get
      exact inflate_default_witness_platform _ _ oldGet
  | str i => exact inflate_default_witness_platform (.str i) a (by simpa [Space.get, staticStringBytes, callerHeap] using get)
  | dstate_depth i => exact inflate_default_witness_platform (.dstate_depth i) a (by simpa [Space.get, callerHeap] using get)
  | st_dist_code => exact inflate_default_witness_platform .st_dist_code a (by simpa [Space.get, callerHeap] using get)
  | st_length_code => exact inflate_default_witness_platform .st_length_code a (by simpa [Space.get, callerHeap] using get)

/-- Non-vacuity of the original default completion antecedents. The init
and caller edit are real; no inflate execution or completion is assumed.
The output binding is a distinct non-null writable object with one byte of
room even though this independently decoded stream produces no output. -/
theorem default_completion_domain_witness :
    ∃ initialized z s incoming stream,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) callerHeap = .ok (Z_OK, initialized) ∧
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
  obtain ⟨iz, is, initialGood, alloc, free, head, window,
    _wbits, _reqbits, _wrap, _reqwrap, _wsize, _whave, _wnext, _hold, bits, dict, header,
    _totalIn, _totalOut, _msg, frame, _ledger⟩ := initial
  have sameZ : iz = z := Option.some.inj (initialGood.live.hz.symm.trans invariant.good.live.hz)
  have sameS : is = s := Option.some.inj (initialGood.live.hs.symm.trans invariant.good.live.hs)
  subst iz is
  have first := frame.2.2.2.2.2 1
    (by simp [Heap.live, callerHeap, witnessHeap, Heap.empty]) (by change ¬ (1 : Nat) = 0; decide)
  have second := frame.2.2.2.2.2 2
    (by simp [Heap.live, callerHeap, witnessHeap, Heap.empty]) (by change ¬ (2 : Nat) = 0; decide)
  let stream := { z with next_in := .ref (.blk 1) 2, avail_in := 8, next_out := .ref (.blk 2) 0, avail_out := 1 }
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
  have beforeStream : initialized.streams 0 = some z := invariant.good.live.hz
  have frameRebind : Frame initialized incoming (fun b => ¬ StreamOwned initialized (.tab 0) b) := by
    simp only [Frame, incoming, ZStreamRef.put, beforeStream, Nat.le_refl, true_and]
    intro b live outside
    have different : b ≠ 0 := by intro same; subst b; exact outside streamRootUnowned
    simp only [upd_ne _ _ _ _ different, and_self]
  have edit : Rebuffer initialized incoming (.tab 0) :=
    ⟨current.good.fresh, current.good.uniq, current.globals, frameRebind,
      z, stream, invariant.good.live.hz, current.good.live.hz, rfl⟩
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
  exact ⟨initialized, z, s, incoming, stream, initRun, caller_domain, edit, ⟨trace, scope⟩,
    ⟨false, trace⟩, .rebuffer reachable edit, current, currentAlloc, invariant.good.live.hz,
    current.good.fresh, current.good.uniq, current.globals, current.platform, noFailure, buffers, active,
    head, bits, dict, rfl, rfl, rfl, rfl, (by intro impossible; cases impossible),
    (by intro impossible; cases impossible), source_decodes, Or.inl rfl, List.nil_prefix,
    bytes, Nat.zero_le _⟩

/-- The exact original completion antecedents, specialized to default
zlib/15, the empty epoch and Z_FINISH, have a concrete admitted caller.
No result of the data call occurs in this proposition. -/
theorem default_completion_original_antecedents :
    ∃ h z s,
      Api.inflWbits (15 : Int32).toInt = some (.zlib, 15) ∧
      AllowedInflateProtocol 15 (.tab 0) h {} ∧
      ({} : DataLog).singleDictionary = true ∧ ({} : DataLog).finished = false ∧
      Api.Layer.Decodes .zlib 15 ({} : DataLog).dictionary source [] ∧ Api.FullWindow .zlib 15 source ∧
      ({} : DataLog).input <+: source ∧ Good h (.tab 0) callerHeap.nextBlk z s ∧
      s.mode ≠ BAD ∧ s.mode ≠ MEM ∧ s.mode ≠ SYNC ∧ (s.mode = DICT → s.havedict ≠ 0) ∧
      StreamBuffers h (.tab 0) ∧ ActiveHeader h (.tab 0) ∧ NoAllocationFailure h ∧
      Bytes h z.next_in z.avail_in.toNat (source.drop ({} : DataLog).input.length) ∧
      ([] : List UInt8).length ≤ ({} : DataLog).output.length + z.avail_out.toNat ∧
      (Z_FINISH = Z_NO_FLUSH ∨ Z_FINISH = Z_SYNC_FLUSH ∨ Z_FINISH = Z_FINISH) ∧
      z.next_out ≠ .null := by
  obtain ⟨initialized, z, s, incoming, stream, _initRun, _domain, _edit, _scope,
    allowed, _reachable, current, _allocator, _get, _fresh, _uniq, _globals, _fit,
    noFailure, buffers, active, head, _bits, _dict, _nextIn, _availIn, _nextOut, _availOut,
    _nonNullIn, nonNullOut, format, full, inputPrefix, inputBytes, outputRoom⟩ :=
    default_completion_domain_witness
  refine ⟨incoming, stream, s, by decide, allowed, rfl, rfl, format, full, inputPrefix,
    current.good, ?_, ?_, ?_, ?_, buffers, active, noFailure, inputBytes, outputRoom,
    Or.inr (Or.inr rfl), nonNullOut⟩
  · rw [head]; decide
  · rw [head]; decide
  · rw [head]; decide
  · intro impossible
    rw [head] at impossible
    cases impossible

#print axioms source_decodes
#print axioms caller_domain
#print axioms caller_platform
#print axioms default_completion_domain_witness
#print axioms default_completion_original_antecedents
end Zlib.Inflate.Proofs.CompletionDomainWitness
