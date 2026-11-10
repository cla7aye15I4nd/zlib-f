import ZlibF.Proof.«deflate.c.engine.public-first-output-interval»
import ZlibF.Proof.«deflate.c.engine.public-busy-output-interval»
import ZlibF.Proof.«deflate.c.engine.finishing-output-interval»
import ZlibF.Proof.«deflate.c.engine.refusal-output-interval»

/-! # Precise public caller-buffer frames for actual ordinary requests -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Every actual initialized NO_FLUSH request preserves its exact caller output interval, including refusals. -/
theorem DefaultFinishBoundary.no_flush_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds ob oo used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) Z_NO_FLUSH h = .ok (rc, after)) (live : r.get after = some returned)
    (account : StreamAccounting z returned used produced) :
    RawOutputInterval h after ob oo produced := by
  by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ Z_NO_FLUSH ≠ Z_FINISH) ∨ z.avail_out = 0
  · exact boundary.entry_refusal_run_output_effect buffers pointer (by decide) (by decide) refused run
  · have nonnull : z.next_out ≠ .null := fun eq => refused (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have unfinished : d.status ≠ FINISH_STATE := fun eq => refused (Or.inr (Or.inr (Or.inl ⟨eq, by decide⟩)))
    have nonzero : z.avail_out ≠ 0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0 < z.avail_out.toNat := by
      have neq : z.avail_out.toNat ≠ 0 := fun zero => nonzero (UInt32.toNat_inj.mp zero)
      omega
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      obtain ⟨read, written, other, ze, de, tested, goodA, accountA, inputA, outputA, intervalA⟩ :=
        public_first_no_flush_output_execution start level state buffers pointer output boundary.configuration.memory valid
      exact RawOutputInterval.identify tested run goodA.live.hz live accountA account intervalA
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      by_cases resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2
      · obtain ⟨read, written, other, ze, de, tested, goodA, accountA, inputA, outputA, intervalA⟩ :=
          public_busy_no_flush_output_execution state buffers status level strategy pointer output
            boundary.configuration.memory boundary.configuration.wrap valid resume boundary.lower boundary.upper
        exact RawOutputInterval.identify tested run goodA.live.hz live accountA account intervalA
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
        exact public_duplicate_no_flush_run_output_effect boundary.good buffers pointer status inputEmpty pending nonnull nonzero
          lower boundary.upper run
    · exact False.elim (unfinished finishing.status)

/-- Every actual initialized FINISH request preserves its exact caller output interval, including finishing retries and refusals. -/
theorem DefaultFinishBoundary.finish_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds ob oo used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) Z_FINISH h = .ok (rc, after)) (live : r.get after = some returned)
    (account : StreamAccounting z returned used produced) :
    RawOutputInterval h after ob oo produced := by
  by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ Z_FINISH ≠ Z_FINISH) ∨ z.avail_out = 0
  · exact boundary.entry_refusal_run_output_effect buffers pointer (by decide) (by decide) refused run
  · have nonnull : z.next_out ≠ .null := fun eq => refused (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have nonzero : z.avail_out ≠ 0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0 < z.avail_out.toNat := by
      have neq : z.avail_out.toNat ≠ 0 := fun zero => nonzero (UInt32.toNat_inj.mp zero)
      omega
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      obtain ⟨read, written, computed, other, ze, de, tested, goodA, accountA, inputA, outputA, intervalA⟩ :=
        public_first_finish_output_execution start level state buffers pointer output boundary.configuration.memory valid
      exact RawOutputInterval.identify tested run goodA.live.hz live accountA account intervalA
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      obtain ⟨read, written, computed, other, ze, de, tested, goodA, accountA, inputA, outputA, intervalA⟩ :=
        public_busy_finish_output_execution state buffers status level strategy pointer boundary.configuration.memory
          boundary.configuration.wrap output valid boundary.lower boundary.upper
      exact RawOutputInterval.identify tested run goodA.live.hz live accountA account intervalA
    · by_cases empty : z.avail_in = 0
      · obtain ⟨written, computed, other, ze, de, tested, goodA, accountA, inputA, outputA, intervalA⟩ :=
          public_finishing_output_execution boundary.good buffers finishing pointer empty output boundary.lower boundary.upper
        exact RawOutputInterval.identify tested run goodA.live.hz live accountA account intervalA
      · obtain ⟨written, computed, other, ze, de, tested, goodA, accountA, inputA, outputA, intervalA⟩ :=
          public_finishing_new_input_output_execution boundary.good buffers finishing pointer valid empty output boundary.lower boundary.upper
        exact RawOutputInterval.identify tested run goodA.live.hz live accountA account intervalA

/-- Every actual ordinary initialized request preserves its exact accounted caller output interval. -/
theorem DefaultFinishBoundary.ordinary_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds ob oo used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) flush h = .ok (rc, after)) (live : r.get after = some returned)
    (account : StreamAccounting z returned used produced) :
    RawOutputInterval h after ob oo produced := by
  rcases flag with rfl | rfl
  · exact boundary.no_flush_run_output_effect buffers pointer run live account
  · exact boundary.finish_run_output_effect buffers pointer run live account

/-- Every actual ordinary initialized request returns its exact public BufferFrame,
invariant, byte slice, counters and no-allocation ledger. Null output and every
entry, duplicate and finishing refusal are included. This covers NO_FLUSH/FINISH,
level 6, memory level 8, the zlib wrapper and null/raw output. Other flags,
advanced operations and encoded-output history remain separate obligations. -/
theorem DefaultFinishBoundary.request_with_buffer_frame {h : Heap} {r : ZStreamRef} {ds : Nat}
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
      Shape h after ∧ BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  obtain ⟨used, written, rc, after, z', result, run, stateA, buffersA, accountA, bytesA,
      inputA, outputA, shapeA, frameA, liveA, allocA, nextA, allowed⟩ := boundary.request_with_full_storage flush flag buffers raw
  have frame : BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] := by
    rcases raw with null | ⟨ob, oo, pointer⟩
    · have privateFrame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) := by
        simpa only [null, ByteRoot, or_false] using frameA
      rw [null]
      exact null_output_buffer_frame privateFrame
    · have effect := boundary.ordinary_run_output_effect flag buffers pointer run stateA.good.live.hz accountA
      have fullFrame : Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) := by
        simpa only [pointer, ByteRoot] using frameA
      exact effect.buffer_frame boundary.good stateA.good buffers buffersA pointer accountA shapeA fullFrame
  exact ⟨used, written, rc, after, z', result, run, stateA, buffersA, accountA, bytesA,
    inputA, outputA, shapeA, frame, liveA, allocA, nextA, allowed⟩

end Zlib.Deflate.Engine.Proofs
