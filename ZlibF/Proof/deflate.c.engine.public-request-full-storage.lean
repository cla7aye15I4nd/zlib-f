import ZlibF.Proof.«deflate.c.engine.public-first-full-storage»
import ZlibF.Proof.«deflate.c.engine.public-busy-full-storage»
import ZlibF.Proof.«deflate.c.engine.finishing-full-storage»
import ZlibF.Proof.«deflate.c.engine.public-output-bytes»
import ZlibF.Proof.«deflate.c.engine.public-busy-counters»
import ZlibF.Proof.«deflate.c.engine.finishing-counters»
import ZlibF.Proof.«deflate.c.engine.refusal-counters»
import ZlibF.Proof.«deflate.c.engine.ordinary-request-history»

/-! # Every initialized ordinary public request has exact totals -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual ordinary NO_FLUSH request over the initialized boundary
has exact totals, including all entry and duplicate-request refusals. -/
theorem DefaultFinishBoundary.no_flush_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) Z_NO_FLUSH h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ ByteRoot z.next_out b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ Z_NO_FLUSH ≠ Z_FINISH) ∨ z.avail_out = 0
  · obtain ⟨shape, frame, liveA, alloc, next⟩ := boundary.entry_refusal_run_full_storage (by decide) (by decide) refused run
    exact ⟨shape, full_frame_weaken frame (fun _ root => Or.inl root), liveA, alloc, next⟩
  · have nonnull : z.next_out ≠ .null := fun eq => refused (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have unfinished : d.status ≠ FINISH_STATE := fun eq => refused (Or.inr (Or.inr (Or.inl ⟨eq, by decide⟩)))
    have nonzero : z.avail_out ≠ 0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0 < z.avail_out.toNat := by
      have neq : z.avail_out.toNat ≠ 0 := fun zero => nonzero (UInt32.toNat_inj.mp zero)
      omega
    obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z.next_out = .ref (.blk ob) oo := raw.resolve_left nonnull
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      obtain ⟨read, written, other, ze, de, tested, _goodA, _accountA, _inputA, _outputA, storage⟩ :=
        public_first_no_flush_full_storage_execution start level state buffers pointer output boundary.configuration.memory valid
      have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      rw [← eq]
      simpa only [pointer, ByteRoot] using storage
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      by_cases resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2
      · obtain ⟨read, written, other, ze, de, tested, _goodA, _accountA, _inputA, _outputA, storage⟩ :=
          public_busy_no_flush_full_storage_execution state buffers status level strategy pointer output
            boundary.configuration.memory boundary.configuration.wrap valid resume boundary.lower boundary.upper
        have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
        rw [← eq]
        simpa only [pointer, ByteRoot] using storage
      · have pending : d.pending = 0 := by
          by_cases zero : d.pending = 0
          · exact zero
          · exact False.elim (resume (Or.inl zero))
        have inputEmpty : z.avail_in = 0 := by
          by_cases zero : z.avail_in = 0
          · exact zero
          · exact False.elim (resume (Or.inr (Or.inl zero)))
        have lower : 0 ≤ d.last_flush.toInt := by
          have low := boundary.lower
          have notRetry : d.last_flush.toInt ≠ -1 := fun eq => resume (Or.inr (Or.inr (Or.inl (Int32.toInt_inj.mp eq))))
          have notInitial : d.last_flush.toInt ≠ -2 := fun eq => resume (Or.inr (Or.inr (Or.inr (Int32.toInt_inj.mp eq))))
          omega
        obtain ⟨shape, frame, liveA, alloc, next⟩ := public_duplicate_no_flush_run_full_storage boundary.good status inputEmpty pending nonnull nonzero
          lower boundary.upper run
        exact ⟨shape, full_frame_weaken frame (fun _ changed => changed.elim Or.inl
          (fun same => Or.inr (Or.inl (Or.inl same)))), liveA, alloc, next⟩
    · exact False.elim (unfinished finishing.status)

/-- Every actual FINISH request over the initialized boundary has exact
totals. New input after finishing and pending-first refusal are included. -/
theorem DefaultFinishBoundary.finish_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) Z_FINISH h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ ByteRoot z.next_out b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ Z_FINISH ≠ Z_FINISH) ∨ z.avail_out = 0
  · obtain ⟨shape, frame, liveA, alloc, next⟩ := boundary.entry_refusal_run_full_storage (by decide) (by decide) refused run
    exact ⟨shape, full_frame_weaken frame (fun _ root => Or.inl root), liveA, alloc, next⟩
  · have nonnull : z.next_out ≠ .null := fun eq => refused (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have nonzero : z.avail_out ≠ 0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0 < z.avail_out.toNat := by
      have neq : z.avail_out.toNat ≠ 0 := fun zero => nonzero (UInt32.toNat_inj.mp zero)
      omega
    obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z.next_out = .ref (.blk ob) oo := raw.resolve_left nonnull
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      obtain ⟨read, written, computed, other, ze, de, tested, _goodA, _accountA, _inputA, _outputA, storage⟩ :=
        public_first_finish_full_storage_execution start level state buffers pointer output boundary.configuration.memory valid
      have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      rw [← eq]
      simpa only [pointer, ByteRoot] using storage
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      obtain ⟨read, written, computed, other, ze, de, tested, _goodA, _accountA, _inputA, _outputA, storage⟩ :=
        public_busy_finish_full_storage_execution state buffers status level strategy pointer boundary.configuration.memory
          boundary.configuration.wrap output valid boundary.lower boundary.upper
      have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
      rw [← eq]
      simpa only [pointer, ByteRoot] using storage
    · by_cases empty : z.avail_in = 0
      · obtain ⟨written, computed, other, ze, de, tested, _goodA, _accountA, _inputA, _outputA, storage⟩ :=
          public_finishing_full_storage_execution boundary.good buffers finishing pointer empty output boundary.lower boundary.upper
        have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
        rw [← eq]
        simpa only [pointer, ByteRoot] using storage
      · obtain ⟨written, computed, other, ze, de, tested, _goodA, _accountA, _inputA, _outputA, storage⟩ :=
          public_finishing_new_input_full_storage_execution boundary.good buffers finishing pointer valid empty output boundary.lower boundary.upper
        have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
        rw [← eq]
        simpa only [pointer, ByteRoot] using storage

/-- Every actual ordinary request retains its full object/allocation frame. -/
theorem DefaultFinishBoundary.ordinary_run_full_storage {h after : Heap} {r : ZStreamRef}
    {ds : Nat} {z : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) flush h = .ok (rc, after)) :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ ByteRoot z.next_out b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  rcases flag with rfl | rfl
  · exact boundary.no_flush_run_full_storage buffers raw run
  · exact boundary.finish_run_full_storage buffers raw run

/-- Every ordinary request actually returns its initialized boundary, exact output bytes and counters,
with the full heap/allocation frame. The frame still permits the whole caller output allocation. -/
theorem DefaultFinishBoundary.request_with_full_storage {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used written rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat written.length ∧
      Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ ByteRoot z.next_out b) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  obtain ⟨used, written, rc, after, z', result, run, stateA, buffersA, accountA,
      bytesA, inputA, outputA, allowed⟩ := boundary.request_with_output flush flag buffers raw
  have storage := boundary.ordinary_run_full_storage flag buffers raw run
  exact ⟨used, written, rc, after, z', result, run, stateA, buffersA, accountA, bytesA,
    inputA, outputA, storage.1, storage.2.1, storage.2.2.1, storage.2.2.2.1,
    storage.2.2.2.2, allowed⟩

end Zlib.Deflate.Engine.Proofs
