import ZlibF.Proof.«uncompr.c.local-output-store»
import ZlibF.Proof.«uncompr.c.local-wrapper-frame»
import ZlibF.Proof.«uncompr.c.scalar-frame-mirror»

namespace Zlib.Uncompr.Proof.LocalCoreStores
open C ZlibF.Spec.Public Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges
open Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.Buffers Zlib.Uncompr.Proof.PostRanges
open Zlib.Uncompr.Proof.Cells
set_option autoImplicit false

private theorem bytes_root_live (h : Heap) (p : BPtr) (count : Nat) (xs : List UInt8)
    (bytes : Bytes h p count xs) (b : Nat) (root : ByteRoot p b) : h.live b := by
  rcases bytes with null | ⟨ref, off, array, ptr, get, _⟩
  · rw [null.1] at root; cases root
  · subst p
    cases ref with
    | blk i =>
      change b = i at root
      subst b
      exact Or.inl (by simp [show h.bytes i = some array from get])
    | dstate_depth i =>
      change b = i at root
      subst b
      cases state : h.dstates i with
      | none => simp [Space.get, state] at get
      | some s => simp [Heap.live, state]
    | str i => cases root
    | st_dist_code => cases root
    | st_length_code => cases root

/-- The actual initialized whole loop determines one exact caller output
Store. Null plus zero output uses the real reserved object internally but
is observed as an empty Store at the original null pointer. -/
theorem core_output_store (h after : Heap) (source dest : BPtr) (n capacity : UInt64)
    (xs : List UInt8) (last : UncLoop) (stream : ZStream) (state : InflateState)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (validOutput : dest = .null → capacity = 0)
    (run : C.run (cdoWhile (loopBody (some (.tab h.nextBlk))) loopCondition
      { err := Z_OK, len := n, left := capacity }) (coreHeap h source dest capacity) = .ok (last, after))
    (current : LocalStateJ after h.nextBlk (.tab h.nextBlk) (h.nextBlk + 2) stream state) :
    ∃ output expected,
      remainingOutput stream last + output.length = capacity.toNat ∧
      Store h dest output expected ∧ Shape h expected ∧
      Frame expected after (fun root => StreamRoot (.tab h.nextBlk) root ∨
        InflateOwned (h.nextBlk + 2) (initializedState h) root) := by
  have initial := LocalDefaultEntry.core_state h source dest capacity fresh allocation globals platform
  have allocator := (LocalInitialization.core_local h source dest capacity fresh allocation).2
  have ranges := LocalWrapperRanges.core_remaining_buffers h fresh source dest n capacity xs
    initial.good readable writable separate validOutput
  have nonnull := normalizedDest_nonnull h dest capacity validOutput
  obtain ⟨made, output, coreExpected, count, cursor, length, observed, outputRange,
      frame, store, expectedFrame, _array, _objects⟩ :=
    LocalOutputPrefix.loop_output_store (coreHeap h source dest capacity) after h.nextBlk h.nextBlk
      (h.nextBlk + 2) (coreStream h source dest capacity) stream (initializedState h) state
      { err := Z_OK, len := n, left := capacity } last initial allocator ranges nonnull run current
  have count0 : remainingOutput stream last + output.length = capacity.toNat := by
    rw [length]
    simpa [remainingOutput, coreStream, outputStream] using count
  have initFrame := CallerFrame.core_frame h source dest capacity fresh
  by_cases null : dest = .null
  · have zero : output = [] := by
      have cap0 := validOutput null
      rw [cap0] at count0
      simp only [UInt64.toNat_zero] at count0
      have size : output.length = 0 := by omega
      exact List.length_eq_zero_iff.mp size
    have coreEq : coreExpected = coreHeap h source dest capacity := by
      rw [zero] at store
      exact store.empty_eq
    rw [coreEq] at expectedFrame
    refine ⟨[], h, by simpa only [zero] using count0, Or.inl ⟨rfl,rfl⟩, Shape.refl h, ?_⟩
    apply CallerFrame.frame_trans_restrict initFrame expectedFrame
    intro b live outside
    exact ⟨by simp, outside⟩
  · have ptr : (coreStream h source dest capacity).next_out = dest := by
      simp [coreStream, outputStream, normalizedDest, null]
    rw [ptr] at store
    obtain ⟨out, outRead⟩ := WrapperRanges.writable_bytes h dest capacity.toNat writable
    obtain ⟨expected, write, mirror⟩ := FrameMirror.store_mirror initFrame
      (fun b root => ⟨bytes_root_live h dest capacity.toNat out outRead b root, by simp⟩) store
    refine ⟨output,expected,count0,write,write.shape,?_⟩
    apply CallerFrame.frame_trans_restrict mirror expectedFrame
    intro b live outside
    exact ⟨by simp, outside⟩

#print axioms core_output_store
end Zlib.Uncompr.Proof.LocalCoreStores
