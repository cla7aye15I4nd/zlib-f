import ZlibF.Proof.«deflate.c.engine.public-finish-ready»
import ZlibF.Proof.«deflate.c.engine.counter-effects»
import ZlibF.Proof.«deflate.c.engine.public-finish-pending-entry»

/-! # Exact FINISH control with a reserved trailer

The premise concerns the count of one given actual strategy run. It is
not a contract for an unproved callee or a compressed-size estimate.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (entry pending drain).
A given actual copy that exactly fills caller output returns OK from the
entry, even when its pending count becomes zero. This early return differs
from the final trailer's pending-based return. The count premises are
observations of that given copy, not an assumed flush_pending contract. -/
theorem public_pending_finish_complete_exact_drain
    {h middle : Heap} {r : ZStreamRef} {ds : Nat}
    {z zm : ZStream} {d result : DeflateState} {produced : Nat}
    (good : DGood h r ds z d) (goodM : DGood middle r ds zm result)
    (out : z.next_out ≠ .null) (positive : z.avail_out ≠ 0)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null) (pending : d.pending ≠ 0)
    (run : flush_pending (some r) (setD h ds { d with last_flush := Z_FINISH }) = .ok ((), middle))
    (account : StreamAccounting z zm 0 produced)
    (count : result.pending.toNat + produced = d.pending.toNat)
    (exactOutput : produced = z.avail_out.toNat) (complete : produced = d.pending.toNat) :
    deflate (some r) Z_FINISH h = .ok (Z_OK, setD middle ds { result with last_flush := -1 }) ∧
    zm.avail_out = 0 ∧ result.pending = 0 := by
  have exhausted : zm.avail_out = 0 := UInt32.toNat_inj.mp (by
    change zm.avail_out.toNat = 0
    have balance := account.2.2.2.1
    omega)
  have drained : result.pending = 0 := UInt64.toNat_inj.mp (by
    change result.pending.toNat = 0
    omega)
  exact ⟨public_pending_finish_exhausted good goodM out positive valid pending run exhausted, exhausted, drained⟩

/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
The existing complete strategy proof classifies this given actual run.
Both early returns exhaust output, including an intermediate block flush.
Only finish_done retains output after final-block publication. -/
theorem slow_finish_run_classification
    {h middle : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z zm : ZStream} {d : DeflateState} {xs : List Symbol}
    {input : Nat → UInt8} {config : EngineConfig} {ret : block_state}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, middle))
    (live : r.get middle = some zm) :
    (ret = need_more ∧ zm.avail_out = 0) ∨
    (ret = finish_started ∧ zm.avail_out = 0 ∧ zm.avail_in = 0) ∨
    (ret = finish_done ∧ 0 < zm.avail_out.toNat ∧ zm.avail_in = 0) := by
  obtain ⟨_used, _produced, expectedRet, expected, ze, de, _base, _ys, _input, _origin,
      expectedRun, stateE, _endE, _buffersE, _accountE, _agreesE, _endpointE,
      _baseE, _finishingE, classification⟩ :=
    deflate_slow_finish_ready boundary frontier buffers positive pointer memory wrap publish valid
  obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (expectedRun.symm.trans run))
  subst expectedRet expected
  have streams : ze = zm := Option.some.inj (stateE.good.live.hz.symm.trans live)
  subst ze
  exact classification

/-- `local block_state deflate_slow(deflate_state *s, int flush)`.
Four bytes left by this actual run exclude need_more and finish_started.
The count is the actual run's accounting, including every earlier flush. -/
theorem slow_finish_run_done_of_trailer_reserve
    {h middle : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z zm : ZStream} {d : DeflateState} {xs : List Symbol}
    {input : Nat → UInt8} {config : EngineConfig} {ret : block_state}
    {used produced : Nat}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, middle))
    (live : r.get middle = some zm) (account : StreamAccounting z zm used produced)
    (reserve : produced + 4 ≤ z.avail_out.toNat) :
    ret = finish_done ∧ 4 ≤ zm.avail_out.toNat ∧ zm.avail_in = 0 := by
  have room : 4 ≤ zm.avail_out.toNat := by have balance := account.2.2.2.1; omega
  have classification := slow_finish_run_classification boundary frontier buffers positive pointer memory wrap publish valid run live
  rcases classification with ⟨_ret, empty⟩ | ⟨_ret, empty, _input⟩ | ⟨done, _positive, empty⟩
  · rw [empty] at room
    change 4 ≤ 0 at room
    omega
  · rw [empty] at room
    change 4 ≤ 0 at room
    omega
  · exact ⟨done, room, empty⟩

/-- `int ZEXPORT deflate(z_streamp strm, int flush)` (prepared FINISH).
If this given actual strategy run leaves four bytes for the trailer, the
same data dispatch returns STREAM_END. Exact final capacity is included:
the trailer may leave avail_out zero, since its final return tests pending.
This does not derive the reserve from compressBound. -/
theorem public_busy_slow_finish_end_of_strategy_reserve
    {h middle : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z zm : ZStream} {d : DeflateState} {xs : List Symbol}
    {input : Nat → UInt8} {config : EngineConfig} {ret : block_state}
    {used produced : Nat}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (status : d.status = BUSY_STATE) (level : d.level = 6) (strategy : d.strategy = 0)
    (pointer : z.next_out = .ref (.blk ob) oo) (memory : config.memory.toNat = 16384)
    (wrap : config.wrap = 1) (publish : PublishReady d)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (run : deflate_slow (some (.tab ds)) Z_FINISH h = .ok (ret, middle))
    (live : r.get middle = some zm) (account : StreamAccounting z zm used produced)
    (reserve : produced + 4 ≤ z.avail_out.toNat) :
    ret = finish_done ∧ ∃ after z' result,
      publicDataTail (some r) (some (.tab ds)) Z_FINISH h = .ok (Z_STREAM_END, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' used (produced + 4) ∧ z'.avail_in = 0 ∧
      result.status = FINISH_STATE ∧ result.wrap = -1 ∧ result.pending = 0 ∧
      result.lookahead = 0 ∧ result.bi_valid.toInt = 0 := by
  have positive : 0 < config.level.toInt := by
    have same := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at same
    rw [← same, level]
    decide
  obtain ⟨done, room, empty⟩ := slow_finish_run_done_of_trailer_reserve boundary frontier buffers positive
    pointer memory wrap publish valid run live account reserve
  refine ⟨done, ?_⟩
  obtain ⟨usedE, producedE, retE, expected, ze, de, _baseE, _ysE, _inputE, _originE,
      expectedRun, stateE, _endE, buffersE, accountE, _agreesE, _endpointE,
      _baseLeE, finishing, _classification⟩ :=
    deflate_slow_finish_ready boundary frontier buffers positive pointer memory wrap publish valid
  obtain ⟨codes, heaps⟩ := Prod.mk.inj (Except.ok.inj (expectedRun.symm.trans run))
  subst retE expected
  have streams : ze = zm := Option.some.inj (stateE.good.live.hz.symm.trans live)
  subst ze
  obtain ⟨usedEq, producedEq⟩ := stream_accounting_counts_unique accountE account
  subst usedE producedE
  have finished := finishing (by rw [done]; decide)
  have ready := stateE.resume (by omega)
  have pointerM : zm.next_out = .ref (.blk ob) (oo + produced) := by
    rw [account.2.2.2.2.2.1, pointer]
    rfl
  have wrapM : de.wrap = 1 := (congrArg EngineConfig.wrap stateE.configuration).trans wrap
  obtain ⟨pb, buf, trees, _ledger, _balance⟩ := stateE.symbols
  obtain ⟨trailerProduced, after, z', result, _written, _remaining, trailerRun, goodA,
      buffersA, accountA, _sizes, _storage, amount, left, wrapA, bitsA, fields,
      _bytes, _pendingA, _trailerBits⟩ :=
    zlib_trailer_publish (finish_status_good stateE.good) (finish_status_trees trees)
      (finish_status_buffers stateE.good buffersE) pointerM wrapM ready.1 ready.2.1 finished.2
  have four : trailerProduced = 4 := amount.trans (Nat.min_eq_left room)
  have noPending : result.pending = 0 := UInt64.toNat_inj.mp (by change result.pending.toNat = 0; omega)
  rw [noPending] at trailerRun
  change publicFinishTail (some r) (some (.tab ds)) Z_FINISH
    (setD middle ds { de with status := FINISH_STATE }) = .ok (Z_STREAM_END, after) at trailerRun
  have source : publicDataTail (some r) (some (.tab ds)) Z_FINISH h =
      publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH ret middle := by
    rw [public_busy_finish_slow_source boundary.good.live.hz boundary.good.live.hs status level strategy]
    simp only [bind_app, run]
  have terminal := (public_strategy_finish_done stateE.good.live.hz stateE.good.live.hs).trans trailerRun
  have joined : StreamAccounting z z' used (produced + 4) := by
    simpa only [Nat.add_zero, four] using stream_accounting_trans account accountA
  have emptyA : z'.avail_in = 0 := UInt32.toNat_inj.mp (by
    change z'.avail_in.toNat = 0
    have balance := accountA.2.2.1
    rw [empty] at balance
    change z'.avail_in.toNat + 0 = 0 at balance
    omega)
  refine ⟨after, z', result, ?_, goodA, buffersA, joined, emptyA, ?_, wrapA, noPending, ?_, bitsA⟩
  · rw [done] at source
    exact source.trans terminal
  · rw [fields]
  · rw [fields]
    exact finished.1

end Zlib.Deflate.Engine.Proofs
