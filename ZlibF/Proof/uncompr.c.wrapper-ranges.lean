import ZlibF.Proof.«uncompr.c.wrapper-init»

/-!
# Actual initialized caller ranges and counted core execution

Old caller storage stays outside the new decoder-owned graph. The real reserved
field supplies the NULL+zero output binding. Successful init therefore feeds the
finite core theorem with no initialized-representation assumption from the caller.
The complete wrapper reaches its original ordered finish with exact counts. Full
finish safety and independent data correctness remain separate obligations.
-/

namespace Zlib.Uncompr.Proof.WrapperRanges
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.PostRanges Zlib.Uncompr.Proof.Cells

private theorem root_lt (h : Heap) (fresh : Fresh h) (ref : BRef) (off x : Nat) (a : Array UInt8)
    (get : Space.get h ref = some a) (root : ByteRoot (.ref ref off) x) : x < h.nextBlk := by
  cases ref with
  | blk b =>
    change x = b at root
    subst x
    exact fresh.lt (Or.inl (by simp [show h.bytes b = some a from get]))
  | dstate_depth b =>
    change x = b at root
    subst x
    cases state : h.dstates b with
    | none => simp [Space.get, state] at get
    | some state => exact fresh.lt (by simp [Heap.live, state])
  | str i => cases root
  | st_dist_code => cases root
  | st_length_code => cases root

theorem core_get (h : Heap) (fresh : Fresh h) (source dest : BPtr) (capacity : UInt64)
    (ref : BRef) (a : Array UInt8) (get : Space.get h ref = some a) :
    Space.get (coreHeap h source dest capacity) ref = some a := by
  cases ref with
  | blk b =>
    have oldGet : h.bytes b = some a := get
    have below : b < h.nextBlk := fresh.lt (Or.inl (by simp [oldGet]))
    simpa [Space.get, coreHeap_eq, show b ≠ h.nextBlk + 1 by omega] using get
  | dstate_depth b => simpa only [Space.get, coreHeap_eq] using get
  | str i => exact get
  | st_dist_code => simpa only [Space.get, coreHeap_eq] using get
  | st_length_code => simpa only [Space.get, coreHeap_eq] using get

theorem core_ro (h : Heap) (fresh : Fresh h) (source dest : BPtr) (capacity : UInt64)
    (ref : BRef) (a : Array UInt8) (get : Space.get h ref = some a) :
    Space.ro (coreHeap h source dest capacity) ref = Space.ro h ref := by
  cases ref with
  | blk b =>
    have oldGet : h.bytes b = some a := get
    have below : b < h.nextBlk := fresh.lt (Or.inl (by simp [oldGet]))
    simp [Space.ro, coreHeap_eq, show b ≠ h.nextBlk + 1 by omega]
  | dstate_depth b => rfl
  | str i => rfl
  | st_dist_code => rfl
  | st_length_code => rfl

theorem initial_window_null (h : Heap) : (initializedState h).window = .null := rfl

/-- All actual old caller ranges lie outside the newly initialized decoder graph. -/
theorem core_old_range (h : Heap) (fresh : Fresh h) (source dest p : BPtr) (capacity : UInt64)
    (n : Nat) (xs : List UInt8) (write : Bool)
    (good : Good (coreHeap h source dest capacity) (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h))
    (readable : Bytes h p n xs) (writable : write = true → Writable h p n) :
    CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk) p n write := by
  rcases readable with null | ⟨ref, off, a, ptr, get, fit, values⟩
  · exact Or.inl null.1
  · subst p
    refine Or.inr ⟨⟨xs, Or.inr ⟨ref, off, a, rfl, core_get h fresh source dest capacity ref a get, fit, values⟩⟩,
      ?_, ?_⟩
    · intro writing
      rcases writable writing with null | ⟨ref', off', a', ptr, get', ro, fit'⟩
      · cases null.1
      · cases ptr
        exact Or.inr ⟨ref, off, a', rfl, core_get h fresh source dest capacity ref a' get',
          (core_ro h fresh source dest capacity ref a' get').trans ro, fit'⟩
    · intro x root owned
      have below := root_lt h fresh ref off x a get root
      rw [good.streamOwned_iff] at owned
      rcases owned with decoder | window
      · omega
      · rw [initial_window_null] at window
        cases window

theorem writable_bytes (h : Heap) (p : BPtr) (n : Nat) (writable : Writable h p n) :
    ∃ xs, Bytes h p n xs := by
  rcases writable with null | ⟨ref, off, a, ptr, get, _, fit⟩
  · exact ⟨[], Or.inl ⟨null.1, null.2, rfl⟩⟩
  · exact ⟨(a.toList.drop off).take n, Or.inr ⟨ref, off, a, ptr, get, fit, rfl⟩⟩

/-- The real local reserved field supplies a writable nonnull range, including
when NULL+zero output is normalized to it. It is outside the decoder-owned state. -/
theorem core_reserved_range (h : Heap) (source dest : BPtr) (capacity : UInt64) (n : Nat) (write : Bool)
    (good : Good (coreHeap h source dest capacity) (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h)) (bound : n ≤ 8) :
    CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk)
      (.ref (.blk (h.nextBlk + 1)) 0) n write := by
  have get : Space.get (coreHeap h source dest capacity) (.blk (h.nextBlk + 1) : BRef) = some (junkBytes h) := by
    simp [Space.get, coreHeap_eq]
  have fit : 0 + n ≤ (junkBytes h).size := by simpa [junkBytes] using bound
  refine Or.inr ⟨⟨(junkBytes h).toList.take n, Or.inr ⟨.blk (h.nextBlk + 1), 0, junkBytes h,
    rfl, get, fit, by simp⟩⟩, ?_, ?_⟩
  · intro _
    exact Or.inr ⟨.blk (h.nextBlk + 1), 0, junkBytes h, rfl, get, by simp [Space.ro, coreHeap_eq], fit⟩
  · intro x root owned
    change x = h.nextBlk + 1 at root
    rw [good.streamOwned_iff] at owned
    rcases owned with decoder | window
    · omega
    · rw [initial_window_null] at window
      cases window

theorem core_output_range (h : Heap) (fresh : Fresh h) (source dest : BPtr) (capacity : UInt64)
    (good : Good (coreHeap h source dest capacity) (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h))
    (writable : Writable h dest capacity.toNat) (valid : dest = .null → capacity = 0) :
    CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk) (normalizedDest h dest capacity) capacity.toNat true := by
  by_cases null : dest = .null
  · have zero := valid null
    simpa [normalizedDest, null, zero] using core_reserved_range h source dest capacity 0 true good (by omega)
  · obtain ⟨xs, readable⟩ := writable_bytes h dest capacity.toNat writable
    have range := core_old_range h fresh source dest dest capacity capacity.toNat xs true good readable (fun _ => writable)
    simpa [normalizedDest, null] using range

theorem core_remaining_buffers (h : Heap) (fresh : Fresh h) (source dest : BPtr) (n capacity : UInt64)
    (xs : List UInt8)
    (good : Good (coreHeap h source dest capacity) (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h))
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat) (valid : dest = .null → capacity = 0) :
    RemainingBuffers (coreHeap h source dest capacity) h.nextBlk (coreStream h source dest capacity)
      { err := Z_OK, len := n, left := capacity } := by
  have input := core_old_range h fresh source dest source capacity n.toNat xs false good readable (by simp)
  have output := core_output_range h fresh source dest capacity good writable valid
  have separation : Separate source n.toNat (normalizedDest h dest capacity) capacity.toNat := by
    by_cases null : dest = .null
    · simp [Separate, normalizedDest, null, valid null]
    · simpa [normalizedDest, null] using separate
  exact ⟨input, output, separation⟩

theorem core_cell_range (h : Heap) (fresh : Fresh h) (source dest p : BPtr) (capacity v : UInt64)
    (good : Good (coreHeap h source dest capacity) (.tab h.nextBlk) (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h)) (cell : LengthCell h p v) :
    CallerRange (coreHeap h source dest capacity) (.tab h.nextBlk) p 8 true :=
  core_old_range h fresh source dest p capacity 8 (lengthBytes v) true good cell.1 (fun _ => cell.2)

theorem separate_normalized (h : Heap) (p dest : BPtr) (n : Nat) (capacity : UInt64)
    (separate : Separate p n dest capacity.toNat) (valid : dest = .null → capacity = 0) :
    Separate p n (normalizedDest h dest capacity) capacity.toNat := by
  by_cases null : dest = .null
  · simp [Separate, normalizedDest, null, valid null]
  · simpa [normalizedDest, null] using separate

theorem reserved_separate_old (h : Heap) (fresh : Fresh h) (p : BPtr) (n : Nat) (xs : List UInt8)
    (readable : Bytes h p n xs) : Separate (.ref (.blk (h.nextBlk + 1)) 0) 8 p n := by
  rcases readable with null | ⟨ref, off, a, ptr, get, _, _⟩
  · simp [Separate, null.1]
  · subst p
    have distinct : (.blk (h.nextBlk + 1) : BRef) ≠ ref := by
      intro same
      subst ref
      have live : h.live (h.nextBlk + 1) := Or.inl (by simp [show h.bytes (h.nextBlk + 1) = some a from get])
      exact fresh (h.nextBlk + 1) (by omega) live
    exact Or.inr (Or.inr (Or.inl distinct))

/-- Actual successful init supplies the invariant and ranges to the finite core proof.
Both initial and later allocation behavior belongs to the actual execution. -/
theorem initialized_core_safe (h : Heap) (source dest : BPtr) (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ last after stream state used made,
      C.run (cdoWhile (Zlib.Uncompr.Proof.Loop.loopBody (some (.tab h.nextBlk)))
        Zlib.Uncompr.Proof.Loop.loopCondition { err := Z_OK, len := n, left := capacity })
        (coreHeap h source dest capacity) = .ok (last, after) ∧
      DefaultStateJ after (.tab h.nextBlk) (h.nextBlk + 2) stream state ∧ DefAlloc stream ∧
      RemainingBuffers after h.nextBlk stream last ∧ stream.next_out ≠ .null ∧
      last.err ≠ Z_OK ∧ PublicInflateCode last.err ∧
      remainingInput stream last + used = n.toNat ∧ remainingOutput stream last + made = capacity.toNat ∧
      LiveChange (coreHeap h source dest capacity) after
        (fun x => InflateOwned (h.nextBlk + 2) state x ∧ ¬ (coreHeap h source dest capacity).live x) (fun _ => False) ∧
      (∀ x, (coreHeap h source dest capacity).live x →
        (InflateOwned (h.nextBlk + 2) state x ↔ InflateOwned (h.nextBlk + 2) (initializedState h) x)) := by
  obtain ⟨initial, allocator⟩ := core_boundary h source dest capacity fresh uniq globals platform allocation
  have ranges := core_remaining_buffers h fresh source dest n capacity xs initial.good readable writable separate validOutput
  have nonnull : (coreStream h source dest capacity).next_out ≠ .null := normalizedDest_nonnull h dest capacity validOutput
  have inputNull : (coreStream h source dest capacity).next_in = .null →
      remainingInput (coreStream h source dest capacity) { err := Z_OK, len := n, left := capacity } = 0 := by
    intro null
    have sourceNull : source = .null := null
    simp [remainingInput, coreStream, outputStream, initializedStream, resetKeepStream,
      initStream2, initStream, Wrapper.preparedStream, validInput sourceNull]
  obtain ⟨last, after, stream, state, used, made, run, final, finalAllocator,
    finalRanges, finalNonnull, stop, codes, input, output⟩ :=
    loop_safe (coreHeap h source dest capacity) h.nextBlk (h.nextBlk + 2)
      (coreStream h source dest capacity) (initializedState h)
      { err := Z_OK, len := n, left := capacity } initial allocator ranges nonnull inputNull
  obtain ⟨ledger, owner⟩ := Zlib.Uncompr.Proof.Resources.loop_go_resources C.fuel
    (coreHeap h source dest capacity) after h.nextBlk (h.nextBlk + 2)
    (coreStream h source dest capacity) stream (initializedState h) state
    { err := Z_OK, len := n, left := capacity } last initial allocator ranges nonnull run final.good
  refine ⟨last, after, stream, state, used, made, run, final, finalAllocator,
    finalRanges, finalNonnull, stop, codes, ?_, ?_, ledger, owner⟩
  · simpa [remainingInput, coreStream, outputStream, initializedStream, resetKeepStream,
      initStream2, initStream, Wrapper.preparedStream] using input
  · simpa [remainingOutput, coreStream, outputStream] using output

/-- The complete real wrapper has executed its checks, successful initialization
and finite counted core before reaching the original ordered finish continuation. -/
theorem uncompress2_z_to_finish (h : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8)
    (fresh : Fresh h) (uniq : Uniq h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0) :
    ∃ last after stream state used made,
      C.run (uncompress2_z dest destLen source sourceLen) h =
        finish (some (.tab h.nextBlk)) (.ref (.blk (h.nextBlk + 1)) 0) destLen sourceLen last after ∧
      DefaultStateJ after (.tab h.nextBlk) (h.nextBlk + 2) stream state ∧ DefAlloc stream ∧
      RemainingBuffers after h.nextBlk stream last ∧ stream.next_out ≠ .null ∧
      last.err ≠ Z_OK ∧ PublicInflateCode last.err ∧
      remainingInput stream last + used = n.toNat ∧ remainingOutput stream last + made = capacity.toNat := by
  obtain ⟨last, after, stream, state, used, made, run, current, allocator, ranges, nonnull,
    stop, codes, input, output, _ledger, _owner⟩ :=
    initialized_core_safe h source dest n capacity xs fresh uniq globals platform allocation
      readable writable separate validInput validOutput
  refine ⟨last, after, stream, state, used, made, ?_, current, allocator, ranges, nonnull,
    stop, codes, input, output⟩
  rw [uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh uniq globals platform
    allocation inputCell outputCell validInput validOutput]
  simp only [C.run] at run
  simp only [bind_app, run]

#print axioms core_remaining_buffers
#print axioms initialized_core_safe
#print axioms uncompress2_z_to_finish

end Zlib.Uncompr.Proof.WrapperRanges
