import ZlibF.Proof.«deflate.c.engine.first-finish-size-entry»
import ZlibF.Proof.«deflate.c.engine.finish-counted-size»
import ZlibF.Proof.«deflate.c.engine.finish-trailer-reserve»
import ZlibF.Math.DeflateCountedBudget

/-! # Actual first FINISH completion within the full offer's compressBound -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateBound
set_option autoImplicit false
set_option maxRecDepth 10000

/-- A fresh default stream whose entire source and advertised room fit
the first uInt offers completes the actual first FINISH call within
compressBound. Header, real loop/block costs, one final block and trailer
share one execution. Exact final exhaustion is allowed. Multi-offer
utility histories remain a separate obligation in the full public goal. -/
theorem public_first_finish_compress_bound {h : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : config.memory.toNat = 16384) (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (capacity : ZlibF.Spec.Api.compressBound z.avail_in.toNat ≤ z.avail_out.toNat) :
    ∃ produced after z' result,
      deflate (some r) Z_FINISH h = .ok (Z_STREAM_END, after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' z.avail_in.toNat produced ∧
      produced ≤ ZlibF.Spec.Api.compressBound z.avail_in.toNat ∧ z'.avail_in = 0 ∧
      result.status = FINISH_STATE ∧ result.wrap = -1 ∧ result.pending = 0 ∧
      result.lookahead = 0 ∧ result.bi_valid.toInt = 0 := by
  have object : z.avail_in.toNat < 2 ^ 63 := by have size := z.avail_in.toNat_lt; omega
  have headerRoom : 2 ≤ z.avail_out.toNat := by
    have formula := compress_bound_object_formula z.avail_in.toNat object
    omega
  obtain ⟨pb, buf, output, _get, _outGet, first, stateH, endH, buffersH, publishH, accountH,
    candidateH, floorH, _windowH, endpointH, bitsH⟩ :=
    first_finish_size_entry initial level boundary buffers pointer headerRoom valid
  have positive : 0 < config.level.toInt := by
    have eq := congrArg EngineConfig.level boundary.configuration
    change d.level = config.level at eq
    rw [← eq, level]; decide
  have wrap : config.wrap = 1 := (congrArg EngineConfig.wrap boundary.configuration).symm.trans initial.wrap
  have window : config.windowBits = 15 := (congrArg EngineConfig.windowBits boundary.configuration).symm.trans initial.windowBits
  have strategy : config.strategy = Z_DEFAULT_STRATEGY :=
    (congrArg EngineConfig.strategy boundary.configuration).symm.trans initial.strategy
  have pointerH : (headerCompleteStream z ob oo).next_out = .ref (.blk ob) (oo + 2) := rfl
  obtain ⟨used, amount, ret, middle, zm, dm, blocks, delta, remaining, closed,
    run, goodM, _buffersM, accountM, minimum, mass, cost, _early, _final⟩ :=
    deflate_slow_finish_counted_size stateH endH buffersH positive pointerH memory wrap window strategy publishH valid
      candidateH floorH (by simp)
  rw [endpointH] at mass
  simp only [Nat.zero_add, Nat.add_zero, Nat.sub_zero] at mass
  rw [bitsH] at cost
  simp only [show (0 : Int32).toInt = 0 from rfl, Int.toNat_zero, show 7 / 8 = 0 from rfl,
    Nat.zero_add] at cost
  have blockCount : blocks ≤ used / 16383 := counted_blocks_le_input minimum (by omega)
  have extra : (if closed then 5 else 0) ≤ (5 : Nat) := by cases closed <;> decide
  have strategyBudget : amount ≤ used + 5 * (used / 16383) + 5 := by omega
  have accepted : used ≤ z.avail_in.toNat := by
    have firstInput := accountH.2.2.1
    have usedBound := accountM.1
    omega
  have totalBudget : amount + 6 ≤ ZlibF.Spec.Api.compressBound z.avail_in.toNat :=
    accepted_strategy_budget_fits object accepted strategyBudget
  have reserve : amount + 4 ≤ (headerCompleteStream z ob oo).avail_out.toNat := by
    have outputBalance := accountH.2.2.2.1
    omega
  obtain ⟨_done, after, z', result, tailRun, goodA, buffersA, accountA, emptyA, statusA, wrapA, pendingA, lookA, bitsA⟩ :=
    public_busy_slow_finish_end_of_strategy_reserve stateH endH buffersH rfl level initial.strategy pointerH
      memory wrap publishH valid run goodM.live.hz accountM reserve
  have total : StreamAccounting z z' used (amount + 6) := by
    have combined := stream_accounting_trans accountH accountA
    simpa only [Nat.zero_add, show 2 + (amount + 4) = amount + 6 from by omega] using combined
  have allInput : used = z.avail_in.toNat := by
    have inputBalance := total.2.2.1
    rw [emptyA] at inputBalance
    simpa only [UInt32.toNat_zero, Nat.zero_add] using inputBalance
  rw [allInput] at total
  exact ⟨amount + 6, after, z', result, first.trans tailRun, goodA, buffersA, total, totalBudget,
    emptyA, statusA, wrapA, pendingA, lookA, bitsA⟩

end Zlib.Deflate.Engine.Proofs
