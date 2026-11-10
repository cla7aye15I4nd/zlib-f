import ZlibF.Proof.«inflate.c.default-public»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Rebinding only the four public buffer fields retains the default state
relation. Readable/writable buffer ranges remain separate caller obligations. -/
theorem default_state_rebind {h : Heap} {r : ZStreamRef} {zs : Nat}
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
  have globals : LibraryGlobals (r.put h stream) := by
    change (r.put h stream).static = _
    rw [ZStreamRef.put_static]
    exact invariant.globals
  exact ⟨⟨good, tables, invariant.pending, invariant.lengths, invariant.headerLengths,
    invariant.held, invariant.window, invariant.wrapper, invariant.header, invariant.modes,
    invariant.trailer, globals, invariant.platform.put_stream r stream⟩,
    invariant.requestedBits, invariant.requestedWrap, invariant.phase⟩

/-- Non-vacuity of the actual default public safety result. Actual default
initialization supplies J. Ordinary public buffer binding supplies distinct
raw objects already present in the fixed caller heap. The translated public
inflate then returns and frees its local object. No callee contract is assumed. -/
theorem inflate_default_raw_safe_witness :
    ∃ initialized z s incoming stream rc after finalStream finalState,
      C.run (inflateInit_ (some (.tab 0)) (.ref (.blk 1) 0) 112) witnessHeap = .ok (Z_OK, initialized) ∧
      DefaultStateJ initialized (.tab 0) witnessHeap.nextBlk z s ∧
      stream = { z with next_in := .ref (.blk 1) 0, avail_in := 2, next_out := .ref (.blk 2) 0, avail_out := 1 } ∧
      incoming = (ZStreamRef.tab 0).put initialized stream ∧
      DefaultStateJ incoming (.tab 0) witnessHeap.nextBlk stream s ∧ DefAlloc stream ∧
      StreamBuffers incoming (.tab 0) ∧ RawFastIO (dispatchRegs stream s) ∧
      C.run (inflate (some (.tab 0)) Z_FINISH) incoming = .ok (rc, after) ∧
      Good after (.tab 0) witnessHeap.nextBlk finalStream finalState ∧ after.bytes incoming.nextBlk = none := by
  obtain ⟨initialized, z, s, initRun, initial, invariant, reachable⟩ :=
    inflate_default_state_initial witnessHeap (.tab 0) (.ref (.blk 1) 0)
      ZlibF.Spec.Public.Proofs.InflateInit.public_witness_domain inflate_default_witness_platform rfl
  obtain ⟨iz, is, initialGood, alloc, free, head, window,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, frame, ledger⟩ := initial
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
    default_state_rebind invariant _ _ _ _
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
  have raw : RawFastIO (dispatchRegs stream s) := ⟨1, 0, 2, 0, rfl, rfl, by decide⟩
  obtain ⟨rc, after, finalStream, finalState, run, good, tables, pending, held, bits, freed⟩ :=
    inflate_default_raw_safe current currentAlloc buffers raw Z_FINISH
  exact ⟨initialized, z, s, incoming, stream, rc, after, finalStream, finalState,
    initRun, invariant, rfl, rfl, current, currentAlloc, buffers, raw, run, good, freed⟩

end Zlib.Inflate.Proofs
