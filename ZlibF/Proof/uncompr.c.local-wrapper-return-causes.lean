import ZlibF.Proof.«uncompr.c.local-finish-return-causes»
import ZlibF.Proof.«uncompr.c.local-wrapper-memory»
import ZlibF.Proof.«uncompr.c.local-initialized-objects»
import ZlibF.Proof.«uncompr.c.wrapper-return-causes»
import ZlibF.Proof.«uncompr.c.initial-refusal»
import ZlibF.Proof.«uncompr.c.local-core-safe»

namespace Zlib.Uncompr.Proof.LocalReturnCauses
open C Zlib.Gzguts Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs Zlib.Inflate.Local ZlibF.Spec.Public
open Zlib.Uncompr.Proof.ReturnCauses
open Zlib.Uncompr.Proof.Wrapper Zlib.Uncompr.Proof.WrapperRanges Zlib.Uncompr.Proof.Objects
open Zlib.Uncompr.Proof.Finish Zlib.Uncompr.Proof.Loop Zlib.Uncompr.Proof.PostRanges
set_option autoImplicit false

private theorem resultCode_causes (err : Int32) (remaining : UInt64)
    (stopped : err ≠ Z_OK) (allowed : PublicInflateCode err) (notStream : err ≠ Z_STREAM_ERROR) :
    UncompressCode (resultCode err remaining) ∧
    (resultCode err remaining = Z_MEM_ERROR → err = Z_MEM_ERROR) ∧
    (resultCode err remaining = Z_BUF_ERROR → err = Z_BUF_ERROR ∧ remaining ≠ 0) := by
  rcases allowed with eq | eq | eq | eq | eq | eq | eq
  · exact False.elim (stopped eq)
  · subst err; simp [resultCode, UncompressCode, Z_STREAM_END, Z_OK, Z_NEED_DICT, Z_MEM_ERROR, Z_BUF_ERROR, Z_DATA_ERROR]
  · subst err; simp [resultCode, UncompressCode, Z_STREAM_END, Z_OK, Z_NEED_DICT, Z_MEM_ERROR, Z_BUF_ERROR, Z_DATA_ERROR]
  · exact False.elim (notStream eq)
  · subst err; simp [resultCode, UncompressCode, Z_STREAM_END, Z_OK, Z_NEED_DICT, Z_MEM_ERROR, Z_BUF_ERROR, Z_DATA_ERROR]
  · subst err; simp [resultCode, UncompressCode, Z_STREAM_END, Z_OK, Z_NEED_DICT, Z_MEM_ERROR, Z_BUF_ERROR, Z_DATA_ERROR]
  · subst err
    by_cases zero : remaining = 0 <;>
      simp [resultCode, UncompressCode, zero, Z_STREAM_END, Z_OK, Z_NEED_DICT, Z_MEM_ERROR, Z_BUF_ERROR, Z_DATA_ERROR]

/-- The actual counted wrapper's initialized branch has only the standard
uncompress result codes. Final MEM is a genuine same-run failure; final
BUF means the entire caller output capacity was written. The explicit scalar/range separation and per-object platform premises
remain; no uniqueness is required for old caller objects. -/
theorem uncompress2_z_initialized_return_causes (h after : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (rc : Int32)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h) (allocation : h.allocOk h.nalloc = true)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat) (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
    (run : C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after)) :
    UncompressCode rc ∧ (rc = Z_MEM_ERROR → AllocationFailed h after) ∧
    (rc = Z_BUF_ERROR → LengthCell after destLen capacity) := by
  obtain ⟨last, coreAfter, stream, state, used, made, coreRun, current, allocator,
    ranges, nonnull, stopped, code, countIn, countOut, _⟩ :=
    LocalWrapperRanges.initialized_core_safe h source dest n capacity xs fresh globals platform allocation
      readable writable separate validInput validOutput
  have initial := LocalDefaultEntry.core_state h source dest capacity fresh allocation globals platform
  have initialAllocator := (LocalInitialization.core_local h source dest capacity fresh allocation).2
  have initialRanges := LocalWrapperRanges.core_remaining_buffers h fresh source dest n capacity xs initial.good readable writable separate validOutput
  have initialNonnull : (coreStream h source dest capacity).next_out ≠ .null :=
    normalizedDest_nonnull h dest capacity validOutput
  have inputNull : (coreStream h source dest capacity).next_in = .null →
      remainingInput (coreStream h source dest capacity) { err := Z_OK, len := n, left := capacity } = 0 := by
    intro null
    have sourceNull : source = .null := null
    simp [remainingInput, coreStream, outputStream, initializedStream, resetKeepStream,
      initStream2, initStream, Wrapper.preparedStream, validInput sourceNull]
  have ready : Ready (initializedState h) := by change HEAD ≠ MEM ∧ HEAD ≠ SYNC; decide
  obtain ⟨_, notStream, memory, buffer, _, _⟩ := loop_return_causes
    (coreHeap h source dest capacity) coreAfter h.nextBlk h.nextBlk (h.nextBlk + 2)
    (coreStream h source dest capacity) stream (initializedState h) state
    { err := Z_OK, len := n, left := capacity } last initial initialAllocator initialRanges initialNonnull inputNull ready coreRun current.good
  obtain ⟨inputRange, inputCell1, outputRange, outputCell1⟩ :=
    LocalObjects.initialized_loop_cells h coreAfter source dest sourceLen destLen n capacity xs last stream state
      fresh globals platform allocation inputCell outputCell readable writable separate
      sourceSeparate destSeparate validOutput coreRun current
  have tailRun : C.run (finish (some (.tab h.nextBlk)) (.ref (.blk (h.nextBlk + 1)) 0) destLen sourceLen last) coreAfter =
      .ok (rc, after) := by
    rw [FreshCoreEntry.uncompress2_z_to_core h source dest sourceLen destLen n capacity fresh
      allocation inputCell outputCell validInput validOutput] at run
    simp only [C.run] at coreRun ⊢
    simpa only [bind_app, coreRun] using run
  obtain ⟨mapped, allocations, oracle⟩ := finish_return_causes coreAfter after h.nextBlk h.nextBlk (h.nextBlk + 2)
    (h.nextBlk + 1) stream state sourceLen destLen n capacity last rc current allocator
    inputCell1 outputCell1 inputRange outputRange cellSeparate tailRun
  obtain ⟨allowed, memCode, bufCode⟩ := resultCode_causes last.err (last.len + stream.avail_in.toUInt64) stopped code notStream
  refine ⟨by rw [mapped]; exact allowed, ?_, ?_⟩
  · intro selected
    have selected' := memCode (mapped.symm.trans selected)
    obtain ⟨i, lower, upper, rejected⟩ := memory selected'
    have initialCount : (coreHeap h source dest capacity).nalloc = h.nalloc + 1 := by rw [coreHeap_eq]
    have initialOracle : (coreHeap h source dest capacity).allocOk = h.allocOk := by rw [coreHeap_eq]
    refine ⟨i, ?_, ?_, ?_⟩
    · rw [initialCount] at lower; omega
    · rw [allocations]; exact upper
    · rw [initialOracle] at rejected
      exact rejected
  · intro selected
    obtain ⟨isBuffer, remains⟩ := bufCode (mapped.symm.trans selected)
    have exhausted := buffer isBuffer
    have remainingPositive : remainingInput stream last ≠ 0 := by
      intro zero
      have natZero : (last.len + stream.avail_in.toUInt64).toNat = 0 := by
        have exactCount := final_count_exact n last.len stream.avail_in (by unfold remainingInput at countIn; omega)
        rw [exactCount.1]
        exact zero
      exact remains (UInt64.toNat_inj.mp natZero)
    have outputZero := exhausted.resolve_left remainingPositive
    have reserved := LocalObjects.initialized_loop_reserved h coreAfter source dest n capacity xs
      last stream state fresh globals platform allocation readable writable separate validOutput coreRun current
    obtain ⟨mid, written, clean, finishRun, _, _, _, _, finalCell, _⟩ := LocalFinish.finish_safe coreAfter h.nextBlk h.nextBlk
      (h.nextBlk + 2) (h.nextBlk + 1) stream state sourceLen destLen n capacity last (junkBytes h).toList
      current allocator inputCell1 outputCell1 inputRange outputRange cellSeparate reserved.2 reserved.1
      (reserved_separate_old h fresh sourceLen 8 (lengthBytes n) inputCell.1)
      (reserved_separate_old h fresh destLen 8 (lengthBytes capacity) outputCell.1)
    have same := Except.ok.inj (finishRun.symm.trans tailRun)
    have heaps : releasedHeap clean h.nextBlk (h.nextBlk + 1) = after := congrArg Prod.snd same
    have cell := released_cell clean h.nextBlk (h.nextBlk + 1) destLen _ finalCell
      (by
        intro off ptr
        rw [ptr] at outputCell
        rcases outputCell.1 with null | ⟨ref, off', a, equal, get, _⟩
        · cases null.1
        · cases equal
          exact fresh (h.nextBlk + 1) (by omega) (Or.inl (by simp [show h.bytes (h.nextBlk + 1) = some a from get])))
    have zeroLeft : last.left + stream.avail_out.toUInt64 = 0 := by
      apply UInt64.toNat_inj.mp
      have exactCount := final_count_exact capacity last.left stream.avail_out (by unfold remainingOutput at countOut; omega)
      rw [exactCount.1]
      exact outputZero
    rw [heaps, zeroLeft, UInt64.sub_zero] at cell
    exact cell

/-- Both actual initialization outcomes are included. No successful-first-
allocation premise remains; first MEM preserves caller length cells. -/
theorem uncompress2_z_return_causes (h after : Heap) (source dest sourceLen destLen : BPtr)
    (n capacity : UInt64) (xs : List UInt8) (rc : Int32)
    (fresh : Fresh h) (globals : LibraryGlobals h)
    (platform : ZlibF.PlatformMemory.ByteObjectsFit h)
    (inputCell : LengthCell h sourceLen n) (outputCell : LengthCell h destLen capacity)
    (readable : Bytes h source n.toNat xs) (writable : Writable h dest capacity.toNat)
    (separate : Separate source n.toNat dest capacity.toNat)
    (sourceSeparate : Separate sourceLen 8 dest capacity.toNat)
    (destSeparate : Separate destLen 8 dest capacity.toNat) (cellSeparate : Separate sourceLen 8 destLen 8)
    (validInput : source = .null → n = 0) (validOutput : dest = .null → capacity = 0)
    (run : C.run (uncompress2_z dest destLen source sourceLen) h = .ok (rc, after)) :
    UncompressCode rc ∧ (rc = Z_MEM_ERROR → AllocationFailed h after) ∧
    (rc = Z_BUF_ERROR → LengthCell after destLen capacity) := by
  by_cases allocation : h.allocOk h.nalloc = true
  · exact uncompress2_z_initialized_return_causes h after source dest sourceLen destLen n capacity xs rc
      fresh globals platform allocation inputCell outputCell readable writable separate
      sourceSeparate destSeparate cellSeparate validInput validOutput run
  · have actual := Zlib.Uncompr.Proof.InitialRefusal.uncompress2_z_initial_refusal h source dest sourceLen destLen n capacity
      fresh allocation inputCell outputCell validInput validOutput
    have same := Except.ok.inj (actual.symm.trans run)
    have code : Z_MEM_ERROR = rc := congrArg Prod.fst same
    have heap : Zlib.Uncompr.Proof.InitialRefusal.refusedHeap h = after := congrArg Prod.snd same
    refine ⟨by rw [←code]; exact Or.inr (Or.inl rfl), ?_, ?_⟩
    · intro _
      refine ⟨h.nalloc, Nat.le_refl _, ?_, ?_⟩
      · rw [←heap]
        change h.nalloc < h.nalloc + 1
        omega
      · cases value : h.allocOk h.nalloc with
        | false => rfl
        | true => exact False.elim (allocation value)
    · intro impossible
      exact False.elim ((by decide : Z_MEM_ERROR ≠ Z_BUF_ERROR) (code.trans impossible))

#print axioms uncompress2_z_return_causes
#print axioms uncompress2_z_initialized_return_causes
end Zlib.Uncompr.Proof.LocalReturnCauses
