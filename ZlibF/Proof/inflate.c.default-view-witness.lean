import ZlibF.Proof.«inflate.c.default-view-public»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Rebinding only the four public buffer fields retains the default state
relation. Readable/writable buffer ranges remain separate caller obligations. -/
theorem default_view_rebind {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s)
    (input output : BPtr) (available left : UInt32) :
    let stream := { z with next_in := input, avail_in := available, next_out := output, avail_out := left }
    DefaultStateJ (r.put h stream) r zs stream s := by
  dsimp only
  let stream := { z with next_in := input, avail_in := available, next_out := output, avail_out := left }
  have same : setI (r.put h stream) zs s = r.put h stream :=
    tcSetI_same (by simpa only [ZStreamRef.put_istates] using invariant.good.live.hs)
  have good : Good (r.put h stream) r zs stream s := by
    have current := invariant.good.setZI (z' := stream) (st' := s) rfl
      invariant.good.live.zalloc invariant.good.live.zfree rfl invariant.good.live.mode invariant.good.inv
    rwa [same] at current
  have tables : DataTableInvariant (r.put h stream) s := by
    intro active
    have old := invariant.tables active
    constructor
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.lengthTable
      exact ⟨ref, offset, array, pointer, (code_views_put_stream h r stream ref).trans get, safe⟩
    · obtain ⟨ref, offset, array, pointer, get, safe⟩ := old.distanceTable
      exact ⟨ref, offset, array, pointer, (code_views_put_stream h r stream ref).trans get, safe⟩
    · exact old.lengthLeaves_frame rfl rfl (fun ref _ _ => code_views_put_stream h r stream ref)
  have globals : LibraryGlobals (r.put h stream) := by
    change (r.put h stream).static = _
    rw [ZStreamRef.put_static]
    exact invariant.globals
  exact ⟨⟨good, tables, invariant.pending, invariant.lengths, invariant.headerLengths,
    invariant.held, invariant.window, invariant.wrapper, invariant.header, invariant.modes,
    invariant.trailer, globals, invariant.platform.put_stream r stream⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

/-- Non-vacuity of the actual default public state-preservation result. Actual default
initialization supplies J. Ordinary public buffer binding supplies distinct
byte objects already present in the fixed caller heap. The concrete input
is a malformed two-byte header; no successful-decoding claim is made here. The translated public
inflate then returns and frees its local object. No callee contract is assumed. -/
theorem inflate_default_view_state_witness :
    ∃ initialized z s incoming stream rc after finalStream finalState,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, initialized) ∧
      DefaultStateJ initialized (.tab 0) witnessHeap.nextBlk z s ∧
      stream = { z with next_in := .ref (.blk 1) 0, avail_in := 2, next_out := .ref (.blk 2) 0, avail_out := 1 } ∧
      incoming = (ZStreamRef.tab 0).put initialized stream ∧
      DefaultStateJ incoming (.tab 0) witnessHeap.nextBlk stream s ∧ DefAlloc stream ∧ s.head = none ∧
      StreamBuffers incoming (.tab 0) ∧
      Rebuffer initialized incoming (.tab 0) ∧ StreamReachable .inflate incoming (.tab 0) ∧
      C.run (inflate (some (.tab 0)) Z_FINISH) incoming = .ok (rc, after) ∧
      DefaultStateJ after (.tab 0) witnessHeap.nextBlk finalStream finalState ∧
      DefAlloc finalStream ∧ after.bytes incoming.nextBlk = none := by
  obtain ⟨initialized, z, s, initRun, initial, invariant, reachable⟩ :=
    inflate_default_state_initial witnessHeap (.tab 0) (.ref (.blk 1) 0)
      ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain inflate_default_witness_platform rfl
  obtain ⟨iz, is, initialGood, alloc, free, head, window,
    _, _, _, _, _, _, _, _, _, _, headNone, _, _, _, frame, ledger⟩ := initial
  have sameZ : iz = z := Option.some.inj (initialGood.live.hz.symm.trans invariant.good.live.hz)
  have sameS : is = s := Option.some.inj (initialGood.live.hs.symm.trans invariant.good.live.hs)
  subst iz
  subst is
  have first := frame.2.2.2.2.2 1
    (by simp [Heap.live, witnessHeap, Heap.empty]) (by change ¬ (1 : Nat) = 0; decide)
  have second := frame.2.2.2.2.2 2
    (by simp [Heap.live, witnessHeap, Heap.empty]) (by change ¬ (2 : Nat) = 0; decide)
  let stream := { z with next_in := .ref (.blk 1) 0, avail_in := 2, next_out := .ref (.blk 2) 0, avail_out := 1 }
  let incoming := (ZStreamRef.tab 0).put initialized stream
  have current : DefaultStateJ incoming (.tab 0) witnessHeap.nextBlk stream s :=
    default_view_rebind invariant _ _ _ _
  have currentAlloc : DefAlloc stream := ⟨alloc, free⟩
  have inputGet : incoming.bytes 1 = some #[49, 0] := by simpa [incoming, witnessHeap, Heap.empty] using first.1
  have outputGet : incoming.bytes 2 = some (Array.replicate 32768 0) := by simpa [incoming, witnessHeap, Heap.empty] using second.1
  have outputRo : incoming.ro 2 = false := by simpa [incoming, witnessHeap, Heap.empty] using second.2.2.2.2.2.2.2
  have unowned : ∀ b, b = 1 ∨ b = 2 → ¬ StreamOwned incoming (.tab 0) b := by
    intro b caller owned
    have ownedFields := current.good.streamOwned_iff b |>.mp owned
    rcases ownedFields with state | win
    · change b = 3 at state
      rcases caller with equal | equal <;> omega
    · rw [window] at win
      cases win
  have buffers : StreamBuffers incoming (.tab 0) := by
    refine ⟨stream, current.good.live.hz, Or.inr ⟨?_, ?_, ?_⟩, Or.inr ⟨?_, ?_, ?_⟩, ?_⟩
    · exact ⟨[49, 0], Or.inr ⟨.blk 1, 0, #[49, 0], rfl, inputGet, by change 2 ≤ 2; decide, rfl⟩⟩
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
      exact Or.inr ⟨.blk 2, 0, Array.replicate 32768 0, rfl, outputGet, outputRo, by simp only [Array.size_replicate]; change 1 ≤ 32768; decide⟩
    · intro b root
      exact unowned b (Or.inr root)
    · simp [Separate, stream]
  have streamRootUnowned : ¬ StreamOwned initialized (.tab 0) 0 := by
    intro owned
    have oldOwned := (invariant.good.streamOwned_iff 0).mp owned
    rcases oldOwned with stateRoot | win
    · change (0 : Nat) = 3 at stateRoot
      cases stateRoot
    · rw [window] at win
      cases win
  have beforeStream : initialized.streams 0 = some z := invariant.good.live.hz
  have frameRebind : Frame initialized incoming
      (fun b => ¬ StreamOwned initialized (.tab 0) b) := by
    simp only [Frame, incoming, ZStreamRef.put, beforeStream, Nat.le_refl, true_and]
    intro b live outside
    have different : b ≠ 0 := by
      intro same
      subst b
      exact outside streamRootUnowned
    simp only [upd_ne _ _ _ _ different, and_self]
  have edit : Rebuffer initialized incoming (.tab 0) :=
    ⟨current.good.fresh, current.good.uniq, current.globals, frameRebind,
      z, stream, invariant.good.live.hz, current.good.live.hz, rfl⟩
  have reachableInput : StreamReachable .inflate incoming (.tab 0) :=
    StreamReachable.rebuffer reachable edit (fun _ => current.platform)
  have entry : EntryHeaderFacts incoming (.tab 0) s stream := EntryHeaderFacts.of_none headNone
  obtain ⟨rc, after, finalStream, finalState, run, final, finalAllocator, freed⟩ :=
    inflate_default_view_state_safe current currentAlloc buffers entry Z_FINISH
  exact ⟨initialized, z, s, incoming, stream, rc, after, finalStream, finalState,
    initRun, invariant, rfl, rfl, current, currentAlloc, headNone, buffers, edit, reachableInput, run, final, finalAllocator, freed⟩

#print axioms inflate_default_view_state_witness
end Zlib.Inflate.Proofs
