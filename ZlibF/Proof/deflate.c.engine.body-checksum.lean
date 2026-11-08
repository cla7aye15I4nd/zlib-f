import ZlibF.Proof.«deflate.c.engine.fill-checksum»
import ZlibF.Proof.«deflate.c.engine.decision-checksum»
import ZlibF.Proof.«deflate.c.engine.body-counters»

/-! # Complete ordinary bodies checksum exactly their accepted caller bytes -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The zero-length slice is readable at every admitted caller input. -/
theorem caller_input_zero_slice {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r) :
    Bytes h z.next_in 0 [] := by
  cases pointer : z.next_in with
  | null => exact Or.inl ⟨rfl, rfl, rfl⟩
  | ref ref io =>
    obtain ⟨array, get, bound⟩ := caller_input_array good buffers pointer
    exact Or.inr ⟨ref, io, array, rfl, get, by omega, by simp⟩

/-- The same actual returned stream and accounting determine the same
accepted byte count and therefore the same checksum observation. -/
theorem accounted_adler_identify {h : Heap} {z expected returned : ZStream}
    {accepted delivered used produced : Nat} {before copied : List UInt8}
    (same : expected = returned) (known : StreamAccounting z expected accepted delivered)
    (account : StreamAccounting z returned used produced)
    (slice : Bytes h z.next_in accepted copied) (length : copied.length = accepted)
    (checksum : expected.adler = (ZlibF.Spec.adler32 (before ++ copied)).toUInt64) :
    ∃ bytes, Bytes h z.next_in used bytes ∧ bytes.length = used ∧
      returned.adler = (ZlibF.Spec.adler32 (before ++ bytes)).toUInt64 := by
  rw [same] at known checksum
  have count := (stream_accounting_counts_unique known account).1
  rw [← count]
  exact ⟨copied, slice, length, checksum⟩

/-- Every actual FINISH body checksums its exact consumed input slice.
All refill, sliding, pending insertion, short tail and output capacities
are included. The initial checksum describes accepted earlier bytes. -/
theorem slow_finish_body_run_adler {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS} {before : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (checksum : z.adler = (ZlibF.Spec.adler32 before).toUInt64)
    (run : deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    ∃ copied, Bytes h z.next_in used copied ∧ copied.length = used ∧
      returned.adler = (ZlibF.Spec.adler32 (before ++ copied)).toUInt64 := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨accepted, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    obtain ⟨copied, copiedSlice, copiedLength, checksumF⟩ := fill_window_run_adler
      boundary.toPendingBoundary short wrapD buffers inputValid checksum fillRun filledState.good.live.hz fillAccount
    have source := slow_finish_body_after_fill boundary.good.live.hs filledState.good.live.hs short fillRun st
    by_cases empty : filled.lookahead = 0
    · have actualRun : deflate_slow_body (some (.tab ds)) Z_FINISH st h =
          .ok ({ st with brk := true }, filledHeap) := by
        rw [source]
        simp only [empty, beq_self_eq_true, ite_true]
      have same := actual_run_stream_unique actualRun run filledState.good.live.hz live
      exact accounted_adler_identify same fillAccount account copiedSlice copiedLength checksumF
    · have nonzero : 1 ≤ filled.lookahead.toNat := by
        have bound : filled.lookahead.toNat ≠ 0 := fun zero => empty (UInt32.toNat_inj.mp zero)
        omega
      have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
        rw [fillAccount.2.2.2.2.2.1, advance_zero]
        exact pointer
      have roomF := fill_window_run_comparison_room boundary.toPendingBoundary short wrapD buffers inputValid fillRun filledState.good.live.hs
      obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, checksumE⟩ :=
        slow_search_decision_adler_execution filledState filledEnd filledBuffers nonzero (fun _ => roomF)
          positive pointerF memory (publish.fill frameF) Z_FINISH st
      have actualRun : deflate_slow_body (some (.tab ds)) Z_FINISH st h = .ok (expected, other) := by
        rw [source]
        simp only [beq_eq_false_iff_ne.mpr empty, Bool.false_eq_true, ite_false]
        exact suffix
      have same := actual_run_stream_unique actualRun run goodE.live.hz live
      have combined := stream_accounting_trans fillAccount accountE
      have checksumA : ze.adler = (ZlibF.Spec.adler32 (before ++ copied)).toUInt64 := checksumE.trans checksumF
      exact accounted_adler_identify same combined account copiedSlice copiedLength checksumA
  · have look : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, checksumE⟩ :=
      slow_search_decision_adler_execution boundary frontier buffers (by omega) (fun _ => room)
        positive pointer memory publish Z_FINISH st
    have actualRun := (slow_ready_body_source boundary.good.live.hs look Z_FINISH st).trans suffix
    have same := actual_run_stream_unique actualRun run goodE.live.hz live
    exact accounted_adler_identify same accountE account (caller_input_zero_slice boundary.good buffers) rfl
      (by simpa only [List.append_nil] using checksumE.trans checksum)

/-- Every actual NO_FLUSH body checksums exactly its accepted caller
slice, including refill waits and all selected compression decisions. -/
theorem slow_no_flush_body_run_adler {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base used produced : Nat} {z returned : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {st next : LoopS} {before : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1) (publish : PublishReady d)
    (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (checksum : z.adler = (ZlibF.Spec.adler32 before).toUInt64)
    (run : deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (next, after))
    (live : r.get after = some returned) (account : StreamAccounting z returned used produced) :
    ∃ copied, Bytes h z.next_in used copied ∧ copied.length = used ∧
      returned.adler = (ZlibF.Spec.adler32 (before ++ copied)).toUInt64 := by
  by_cases short : d.lookahead.toNat < 262
  · obtain ⟨accepted, filledHeap, filledZ, filled, extended, nextOrigin, fillRun, filledState, filledEnd,
        fillAccount, filledBuffers, _startF, _lookF, _agreesF, _stoppedF, frameF⟩ :=
      fill_window_strategy_end_boundary boundary frontier short wrap buffers inputValid
    have wrapD : d.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).trans wrap
    obtain ⟨copied, copiedSlice, copiedLength, checksumF⟩ := fill_window_run_adler
      boundary.toPendingBoundary short wrapD buffers inputValid checksum fillRun filledState.good.live.hz fillAccount
    by_cases ready : 262 ≤ filled.lookahead.toNat
    · have roomF : filled.strstart.toNat + 262 ≤ filled.window_size.toNat := by
        have range := filledState.range
        dsimp only [fillEnd] at range
        omega
      have pointerF : filledZ.next_out = .ref (.blk ob) oo := by
        rw [fillAccount.2.2.2.2.2.1, advance_zero]
        exact pointer
      obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, checksumE⟩ :=
        slow_search_decision_adler_execution filledState filledEnd filledBuffers (by omega) (fun _ => roomF)
          positive pointerF memory (publish.fill frameF) Z_NO_FLUSH st
      have actualRun : deflate_slow_body (some (.tab ds)) Z_NO_FLUSH st h = .ok (expected, other) := by
        exact ((slow_body_fill_ready boundary.good.live.hs filledState.good.live.hs short ready fillRun Z_NO_FLUSH st).trans
          (slow_ready_body_source filledState.good.live.hs ready Z_NO_FLUSH st)).trans suffix
      have same := actual_run_stream_unique actualRun run goodE.live.hz live
      have combined := stream_accounting_trans fillAccount accountE
      have checksumA : ze.adler = (ZlibF.Spec.adler32 (before ++ copied)).toUInt64 := checksumE.trans checksumF
      exact accounted_adler_identify same combined account copiedSlice copiedLength checksumA
    · have actualRun := slow_body_fill_wait boundary.good.live.hs filledState.good.live.hs short (by omega) fillRun st
      have same := actual_run_stream_unique actualRun run filledState.good.live.hz live
      exact accounted_adler_identify same fillAccount account copiedSlice copiedLength checksumF
  · have look : 262 ≤ d.lookahead.toNat := by omega
    have room : d.strstart.toNat + 262 ≤ d.window_size.toNat := by
      have range := boundary.range
      dsimp only [fillEnd] at range
      omega
    obtain ⟨delivered, expected, other, ze, de, suffix, goodE, accountE, checksumE⟩ :=
      slow_search_decision_adler_execution boundary frontier buffers (by omega) (fun _ => room)
        positive pointer memory publish Z_NO_FLUSH st
    have actualRun := (slow_ready_body_source boundary.good.live.hs look Z_NO_FLUSH st).trans suffix
    have same := actual_run_stream_unique actualRun run goodE.live.hz live
    exact accounted_adler_identify same accountE account (caller_input_zero_slice boundary.good buffers) rfl
      (by simpa only [List.append_nil] using checksumE.trans checksum)

end Zlib.Deflate.Engine.Proofs
