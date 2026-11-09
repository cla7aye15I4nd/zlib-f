import ZlibF.Proof.«deflate.c.engine.wrapper-byte-progress»
import ZlibF.Spec.PlatformMemory

/-! # Byte progress for default ordinary requests -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Accounting and stream liveness transfer byte progress between two
proofs of the same actual call. -/
theorem matching_run_byte_progress {h after expected : Heap} {r : ZStreamRef}
    {z za ze : ZStream} {used produced accepted delivered : Nat} {rc code : Int32}
    {call : C.M Int32}
    (actualRun : C.run call h = .ok (rc, after))
    (expectedRun : C.run call h = .ok (code, expected))
    (actualLive : r.get after = some za) (expectedLive : r.get expected = some ze)
    (actualAccount : StreamAccounting z za used produced)
    (expectedAccount : StreamAccounting z ze accepted delivered)
    (progress : code = Z_OK → accepted ≠ 0 ∨ delivered ≠ 0) :
    rc = Z_OK → used ≠ 0 ∨ produced ≠ 0 := by
  obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (expectedRun.symm.trans actualRun))
  subst code expected
  have streams : ze = za := Option.some.inj (expectedLive.symm.trans actualLive)
  subst ze
  obtain ⟨input, output⟩ := stream_accounting_counts_unique expectedAccount actualAccount
  simpa only [input, output] using progress

/-- Ordinary requests with positive raw output make byte progress whenever
they return OK. Empty NO_FLUSH calls are explicitly excluded. Default
level six, memory eight, zlib wrapping and the default allocator are
inherited from the initialized boundary. -/
theorem DefaultFinishBoundary.ordinary_run_byte_progress
    {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z za : ZStream} {d : DeflateState} {config : EngineConfig}
    {flush rc : Int32} {used produced : Nat}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (ordinary : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (guard : flush = Z_NO_FLUSH → z.avail_in ≠ 0)
    (run : C.run (deflate (some r) flush) h = .ok (rc, after))
    (live : r.get after = some za) (account : StreamAccounting z za used produced) :
    rc = Z_OK → used ≠ 0 ∨ produced ≠ 0 := by
  rcases ordinary with noFlush | finish
  · subst flush
    have nonempty := guard rfl
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      obtain ⟨accepted, delivered, final, ze, de, _input, _origin, _base, _ys,
          expectedRun, stateE, _buffersE, accountE, _statusE, _lastE, progress⟩ :=
        public_default_first_no_flush_byte_progress start level state buffers pointer output boundary.configuration.memory valid
      exact matching_run_byte_progress run expectedRun live stateE.good.live.hz account accountE (fun _ => Or.inr (by omega))
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      obtain ⟨accepted, delivered, final, ze, de, _input, _origin, _base, _ys,
          expectedRun, stateE, _buffersE, accountE, _statusE, _lastE, progress⟩ :=
        public_default_busy_no_flush_byte_progress state buffers status level strategy pointer output
          boundary.configuration.memory boundary.configuration.wrap valid (Or.inr (Or.inl nonempty)) boundary.lower boundary.upper
      exact matching_run_byte_progress run expectedRun live stateE.good.live.hz account accountE (fun _ => progress nonempty)
    · obtain ⟨err, final, ze, allowed, expectedRun, stateE, _buffersE, accountE⟩ :=
        boundary.entry_refusals Z_NO_FLUSH buffers (by decide) (by decide)
          (Or.inr (Or.inr (Or.inl ⟨finishing.status, by decide⟩)))
      apply matching_run_byte_progress run expectedRun live stateE.good.live.hz account accountE
      intro ok
      rcases allowed with streamError | bufError
      · rw [streamError] at ok
        cases (by decide : Z_STREAM_ERROR ≠ Z_OK) ok
      · rw [bufError] at ok
        cases (by decide : Z_BUF_ERROR ≠ Z_OK) ok
  · subst flush
    rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
    · have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      by_cases one : z.avail_out = 1
      · obtain ⟨final, ze, de, expectedRun, goodE, _buffersE, accountE, _rest⟩ :=
          public_default_first_finish_one start level buffers pointer one valid
        exact matching_run_byte_progress run expectedRun live goodE.live.hz account accountE (fun _ => Or.inr (by decide))
      · have room : 2 ≤ z.avail_out.toNat := by
          have notOne : z.avail_out.toNat ≠ 1 := fun eq => one (UInt32.toNat_inj.mp eq)
          omega
        have publish : PublishReady d := ⟨start.pending, start.pendingOut, state.bits⟩
        obtain ⟨accepted, delivered, code, final, ze, de, expectedRun, goodE, _buffersE, accountE, _rest⟩ :=
          public_default_first_finish_header_fits start level (state.strategy publish) state.end_frontier buffers
            pointer room boundary.configuration.memory valid
        exact matching_run_byte_progress run expectedRun live goodE.live.hz account accountE (fun _ => Or.inr (by omega))
    · obtain ⟨input, origin, base, xs, state, status⟩ := working
      have level : d.level = 6 := (congrArg EngineConfig.level state.configuration).trans boundary.configuration.level
      have strategy : d.strategy = 0 := (congrArg EngineConfig.strategy state.configuration).trans boundary.configuration.strategy
      obtain ⟨accepted, delivered, code, final, ze, de, expectedRun, goodE, _buffersE, accountE,
          _allowedE, _bitsE, _phaseE, _lastE, _endedE, progress, _emptyE⟩ :=
        public_default_busy_finish_byte_progress state buffers status level strategy pointer boundary.configuration.memory
          boundary.configuration.wrap output valid boundary.lower boundary.upper
      exact matching_run_byte_progress run expectedRun live goodE.live.hz account accountE (fun ok => Or.inr (by have := progress ok; omega))
    · by_cases empty : z.avail_in = 0
      · obtain ⟨delivered, code, final, ze, de, expectedRun, goodE, _buffersE, accountE,
            _allowedE, _phaseE, _lastE, _emptyE, _endedE, _balanceE, progress⟩ :=
          public_finishing_publication_progress boundary.good buffers finishing pointer empty output boundary.lower boundary.upper
        exact matching_run_byte_progress run expectedRun live goodE.live.hz account accountE (fun ok => Or.inr (by have := progress ok; omega))
      · obtain ⟨delivered, code, final, ze, de, expectedRun, goodE, _buffersE, accountE,
            _allowedE, _phaseE, _lastE, _inputE, exhausted⟩ :=
          public_default_finishing_new_input boundary.good buffers finishing pointer valid empty output boundary.lower boundary.upper
        apply matching_run_byte_progress run expectedRun live goodE.live.hz account accountE
        intro ok
        right
        have outE := exhausted ok
        have balance := accountE.2.2.2.1
        rw [outE] at balance
        simp only [UInt32.toNat_zero, Nat.zero_add] at balance
        omega

/-- The exact ordinary safety/count/frame request theorem, strengthened
on its own actual returned heap by byte progress. Each byte object is
allowed up to the platform memory limit. -/
theorem DefaultFinishBoundary.guarded_ordinary_progress
    {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} {flush : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (_objects : ZlibF.PlatformMemory.ByteObjectsFit h)
    (pointer : z.next_out = .ref (.blk ob) oo) (output : 0 < z.avail_out.toNat)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (ordinary : flush = Z_NO_FLUSH ∨ flush = Z_FINISH)
    (guard : flush = Z_NO_FLUSH → z.avail_in ≠ 0) :
    ∃ used written rc after z' result,
      C.run (deflate (some r) flush) h = .ok (rc, after) ∧
      DefaultFinishBoundary after r ds z' result config ∧ StreamBuffers after r ∧
      StreamAccounting z z' used written.length ∧ Bytes after z.next_out written.length written ∧
      z'.total_in = z.total_in + UInt64.ofNat used ∧
      z'.total_out = z.total_out + UInt64.ofNat written.length ∧
      (rc = Z_OK ∨ rc = Z_STREAM_END ∨ rc = Z_STREAM_ERROR ∨ rc = Z_BUF_ERROR) ∧
      (rc = Z_OK → used ≠ 0 ∨ written ≠ []) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out, written.length⟩] ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨used, written, rc, after, z', result, run, stateA, buffersA, goodA, account,
      bytes, inputTotal, outputTotal, allowed, _error, _invalid, _ended, _shape,
      frame, live, allocations, next⟩ :=
    boundary.all_scalar_request_contract flush buffers (Or.inr ⟨ob, oo, pointer⟩)
  refine ⟨used, written, rc, after, z', result, run, stateA, buffersA, account, bytes,
    inputTotal, outputTotal, allowed, ?_, frame, live, allocations, next⟩
  intro ok
  rcases boundary.ordinary_run_byte_progress buffers pointer output valid ordinary guard run goodA.live.hz account ok with consumed | emitted
  · exact Or.inl consumed
  · exact Or.inr (fun empty => emitted (by rw [empty]; rfl))

end Zlib.Deflate.Engine.Proofs
