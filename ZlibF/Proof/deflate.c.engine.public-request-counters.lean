import ZlibF.Proof.«deflate.c.engine.public-first-counters»
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
theorem DefaultFinishBoundary.no_flush_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) Z_NO_FLUSH h = .ok (rc, after)) (live : r.get after = some returned)
    (account : StreamAccounting z returned used produced) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧
      returned.total_out = z.total_out + UInt64.ofNat produced := by
  by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ Z_NO_FLUSH ≠ Z_FINISH) ∨ z.avail_out = 0
  · exact boundary.entry_refusal_run_counter_effects (by decide) (by decide) refused run live account
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
      obtain ⟨read, written, other, ze, de, tested, goodA, accountA, inputA, outputA⟩ :=
        public_first_no_flush_counter_execution start level state buffers pointer output boundary.configuration.memory valid
      have same := actual_run_stream_unique tested run goodA.live.hz live
      exact stream_counter_effects_identify same accountA account inputA outputA
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      by_cases resume : d.pending ≠ 0 ∨ z.avail_in ≠ 0 ∨ d.last_flush = -1 ∨ d.last_flush = -2
      · obtain ⟨read, written, other, ze, de, tested, goodA, accountA, inputA, outputA⟩ :=
          public_busy_no_flush_counter_execution state buffers status level strategy pointer output
            boundary.configuration.memory boundary.configuration.wrap valid resume boundary.lower boundary.upper
        have same := actual_run_stream_unique tested run goodA.live.hz live
        exact stream_counter_effects_identify same accountA account inputA outputA
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
        exact public_duplicate_no_flush_run_counter_effects boundary.good status inputEmpty pending nonnull nonzero
          lower boundary.upper run live account
    · exact False.elim (unfinished finishing.status)

/-- Every actual FINISH request over the initialized boundary has exact
totals. New input after finishing and pending-first refusal are included. -/
theorem DefaultFinishBoundary.finish_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) Z_FINISH h = .ok (rc, after)) (live : r.get after = some returned)
    (account : StreamAccounting z returned used produced) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧
      returned.total_out = z.total_out + UInt64.ofNat produced := by
  by_cases refused : z.next_out = .null ∨ (z.avail_in ≠ 0 ∧ z.next_in = .null) ∨
      (d.status = FINISH_STATE ∧ Z_FINISH ≠ Z_FINISH) ∨ z.avail_out = 0
  · exact boundary.entry_refusal_run_counter_effects (by decide) (by decide) refused run live account
  · have nonnull : z.next_out ≠ .null := fun eq => refused (Or.inl eq)
    have valid : z.avail_in ≠ 0 → z.next_in ≠ .null := fun count eq => refused (Or.inr (Or.inl ⟨count, eq⟩))
    have nonzero : z.avail_out ≠ 0 := fun eq => refused (Or.inr (Or.inr (Or.inr eq)))
    have output : 0 < z.avail_out.toNat := by
      have neq : z.avail_out.toNat ≠ 0 := fun zero => nonzero (UInt32.toNat_inj.mp zero)
      omega
    obtain ⟨ob, oo, pointer⟩ : ∃ ob oo, z.next_out = .ref (.blk ob) oo := raw.resolve_left nonnull
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      obtain ⟨read, written, computed, other, ze, de, tested, goodA, accountA, inputA, outputA⟩ :=
        public_first_finish_counter_execution start level state buffers pointer output boundary.configuration.memory valid
      have same := actual_run_stream_unique tested run goodA.live.hz live
      exact stream_counter_effects_identify same accountA account inputA outputA
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      obtain ⟨read, written, computed, other, ze, de, tested, goodA, accountA, inputA, outputA⟩ :=
        public_busy_finish_counter_execution state buffers status level strategy pointer boundary.configuration.memory
          boundary.configuration.wrap output valid boundary.lower boundary.upper
      have same := actual_run_stream_unique tested run goodA.live.hz live
      exact stream_counter_effects_identify same accountA account inputA outputA
    · by_cases empty : z.avail_in = 0
      · obtain ⟨written, computed, other, ze, de, tested, goodA, accountA, inputA, outputA⟩ :=
          public_finishing_counter_execution boundary.good buffers finishing pointer empty output boundary.lower boundary.upper
        have same := actual_run_stream_unique tested run goodA.live.hz live
        exact stream_counter_effects_identify same accountA account (by simpa using inputA) outputA
      · obtain ⟨written, computed, other, ze, de, tested, goodA, accountA, inputA, outputA⟩ :=
          public_finishing_new_input_counter_execution boundary.good buffers finishing pointer valid empty output boundary.lower boundary.upper
        have same := actual_run_stream_unique tested run goodA.live.hz live
        exact stream_counter_effects_identify same accountA account (by simpa using inputA) outputA

/-- The complete ordinary initialized request has the same exact counters
for the actual accepted and delivered byte counts, on every return code. -/
theorem DefaultFinishBoundary.ordinary_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds used produced : Nat} {z returned : ZStream} {d : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo)
    (run : deflate (some r) flush h = .ok (rc, after)) (live : r.get after = some returned)
    (account : StreamAccounting z returned used produced) :
    returned.total_in = z.total_in + UInt64.ofNat used ∧
      returned.total_out = z.total_out + UInt64.ofNat produced := by
  rcases flag with rfl | rfl
  · exact boundary.no_flush_run_counter_effects buffers raw run live account
  · exact boundary.finish_run_counter_effects buffers raw run live account

/-- Every ordinary request actually returns, preserves the initialized
protocol and has exact wrapping public total counters. No successful-run,
callee contract, positive-capacity or accepted-request premise is assumed. -/
theorem DefaultFinishBoundary.request_with_counters {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config) (flush : Int32)
    (flag : flush = Z_NO_FLUSH ∨ flush = Z_FINISH) (buffers : StreamBuffers h r)
    (raw : z.next_out = .null ∨ ∃ ob oo, z.next_out = .ref (.blk ob) oo) :
    ∃ used produced rc after z' result,
      deflate (some r) flush h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used produced ∧ z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat produced ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) := by
  obtain ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, allowed⟩ := boundary.request flush flag buffers raw
  have effects := boundary.ordinary_run_counter_effects flag buffers raw run stateA.good.live.hz accountA
  exact ⟨used, produced, rc, after, z', result, run, stateA, buffersA, accountA, effects.1, effects.2, allowed⟩

end Zlib.Deflate.Engine.Proofs
