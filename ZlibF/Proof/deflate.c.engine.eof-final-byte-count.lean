import ZlibF.Proof.«deflate.c.engine.flush-macro-size»
import ZlibF.Proof.«deflate.c.engine.eof-tail»

/-! # Counted cost of the actual last slow block -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (outBits_length)
set_option autoImplicit false
set_option maxRecDepth 10000

/-- `local block_state finish_tail(deflate_state *s, int flush)`.
The given actual final macro pays its represented bytes and one five-byte
block overhead. Pending publication is included in that same budget. -/
theorem finish_tail_final_run_byte_count {h after : Heap} {r : ZStreamRef}
    {ds ob oo origin base produced : Nat} {z zr : ZStream} {d result : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {ret : block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (ready : PublishReady d)
    (memory : d.lit_bufsize.toNat = 16384) (clear : BlockInit.BlockClear d)
    (available : d.match_available = 0) (wrap : d.wrap = 1)
    (strategy : d.strategy = Z_DEFAULT_STRATEGY) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (run : finish_tail (some (.tab ds)) Z_FINISH h = .ok (ret, after))
    (live : after.dstates ds = some result) (stream : r.get after = some zr)
    (account : StreamAccounting z zr 0 produced) :
    produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
      (d.bi_valid.toInt.toNat + 7) / 8 + represented xs + 5 := by
  obtain ⟨amount, computed, ze, de, macroRun, stateE, buffersE, accountE, _clearE, frameE⟩ :=
    flush_block_only_content_boundary boundary buffers positive pointer ready.2.1 memory ready.1
      (by have low := ready.2.2; omega) clear available true
  have macroRun1 : FLUSH_BLOCK_ONLY (some (.tab ds)) 1 h = .ok ((), computed) := macroRun
  have wrapE : de.wrap = 1 := by rw [frameE]; exact wrap
  have expected : finish_tail (some (.tab ds)) Z_FINISH h =
      .ok ((if ze.avail_out == 0 then finish_started else finish_done), computed) := by
    unfold finish_tail FLUSH_BLOCK
    simp only [beq_self_eq_true, ite_true, bind_app, macroRun1, ldDeflateState_tab stateE.good.live.hs,
      stateE.good.live.back, zrd_eq, stateE.good.live.hz]
    by_cases empty : (ze.avail_out == 0) = true <;> simp [empty, pure_app, wrapE]
  have heaps : computed = after := (Prod.mk.inj (Except.ok.inj (expected.symm.trans run))).2
  rw [heaps] at stateE
  have states : de = result := Option.some.inj (stateE.good.live.hs.symm.trans live)
  have streams : ze = zr := Option.some.inj (stateE.good.live.hz.symm.trans stream)
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, window, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have accounted : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  have cost := flush_macro_run_byte_count boundary.good trees buffers positive pointer ready.2.1 memory strategy
    ready.1 (by have low := ready.2.2; omega) ledger clear boundary.trace quality floor win get boundary.range
    balance0 accounted view true macroRun (by rw [heaps]; exact stateE.good.live.hs)
    (by rw [heaps]; exact stateE.good.live.hz) accountE
  have count : amount = produced := by
    have first := accountE.2.2.2.1
    have second := account.2.2.2.1
    rw [streams] at first
    omega
  rw [states, count, outBits_length, ready.1, UInt64.toNat_zero, Nat.mul_zero, Nat.zero_add] at cost
  exact cost

/-- `local block_state deflate_slow(deflate_state *s, int flush)` (EOF tail).
The real optional deferred literal and insertion write precede one actual
final block. The output count includes pending bytes and held bits. Only
this final-block path pays the extra five bytes. -/
theorem slow_eof_finish_tail_byte_count {h : Heap} {r : ZStreamRef}
    {ds ob oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs (engineConfig d))
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (ready : PublishReady d)
    (memory : d.lit_bufsize.toNat = 16384) (wrap : d.wrap = 1)
    (strategy : d.strategy = Z_DEFAULT_STRATEGY) (floor : StoredSourceFloor d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096) :
    ∃ produced after z' result ys,
      slowEofTail (some (.tab ds)) Z_FINISH h =
        .ok ((if z'.avail_out == 0 then finish_started else finish_done), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented ys) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      base + represented ys = origin + d.strstart.toNat ∧
      produced + result.pending.toNat + (result.bi_valid.toInt.toNat + 7) / 8 ≤
        (d.bi_valid.toInt.toNat + 7) / 8 + represented ys + 5 := by
  obtain ⟨settledHeap, settled, ys, settleRun, stateS, endS, buffersS,
      flagS, lookS, startS, _countS, clearS, configS, frameS, symbols⟩ :=
    slow_eof_literal_content_frame boundary.toContentBoundary frontier buffers empty boundary.strict boundary.clear
  let inserted := eofInsert settled
  let hi := setD settledHeap ds inserted
  obtain ⟨insertRun, stateI, _endI, configI⟩ := eof_insert_content_boundary stateS endS lookS
  have owned := stream_owned_keys stateS.good stateI.good rfl rfl rfl rfl
  have buffersI := stream_buffers_private_read stateS.good.live.hz stateI.good.live.hz buffersS
    (byte_frame_setD settledHeap ds inserted)
    (fun k equal => (stream_owned_deflate stateS.good k).mpr (Or.inl equal)) owned (stream_accounting_zero z) (by rfl)
  have configuration : ConfigFrame d inserted := configS.trans configI
  have readyI : PublishReady inserted := by
    refine ⟨?_, ?_, ?_⟩
    · change settled.pending = 0; rw [frameS]; exact ready.1
    · change settled.pending_out = settled.pending_buf; rw [frameS]; exact ready.2.1
    · change settled.bi_valid.toInt < 8; rw [frameS]; exact ready.2.2
  have floorI : StoredSourceFloor inserted := by
    intro negative
    change settled.block_start.toInt < 0 at negative
    rw [frameS] at negative
    change 32506 ≤ settled.strstart.toNat
    rw [startS]
    exact floor negative
  have qualityI : ∀ s ∈ ys, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096 := by
    rcases symbols with same | ⟨wa, same⟩
    · rw [same]; exact quality
    · rw [same]
      intro s member nonzero zero
      rcases List.mem_append.mp member with old | fresh
      · exact quality s old nonzero zero
      · have same : s = emittedLiteral d wa := List.mem_singleton.mp fresh
        subst s
        exact False.elim (nonzero rfl)
  have bitsI : (eofInsert settled).bi_valid.toInt ≤ 7 := by
    change settled.bi_valid.toInt ≤ 7
    rw [frameS]
    change d.bi_valid.toInt ≤ 7
    have low := ready.2.2
    omega
  have strategyI : (eofInsert settled).strategy = Z_DEFAULT_STRATEGY := by
    change settled.strategy = Z_DEFAULT_STRATEGY
    rw [frameS]
    exact strategy
  obtain ⟨produced, after, z', result, tailRun, stateA, buffersA, accountA,
      _clearA, _frameA, _lowA, _phaseA⟩ :=
    finish_tail_final_boundary stateI buffersI
      (by rw [configuration.level]; exact positive) pointer readyI.2.1
      (by rw [configuration.memory]; exact memory) readyI.1
      bitsI ⟨clearS.bl, clearS.opt, clearS.fixed⟩ flagS
      (by rw [configuration.wrap]; exact wrap)
  have cost := finish_tail_final_run_byte_count stateI buffersI
    (by rw [configuration.level]; exact positive) pointer readyI
    (by rw [configuration.memory]; exact memory) ⟨clearS.bl, clearS.opt, clearS.fixed⟩ flagS
    (by rw [configuration.wrap]; exact wrap) strategyI
    floorI qualityI tailRun stateA.good.live.hs stateA.good.live.hz accountA
  have held : inserted.bi_valid = d.bi_valid := by change settled.bi_valid = d.bi_valid; rw [frameS]
  rw [held] at cost
  have mass : base + represented ys = origin + d.strstart.toNat := by
    have same : inserted.strstart = d.strstart := startS
    have before := stateI.accounted
    change base + represented ys + pendingCredit inserted = origin + inserted.strstart.toNat at before
    have flag : inserted.match_available = 0 := flagS
    simpa only [pendingCredit, flag, ite_true, Nat.add_zero, same] using before
  refine ⟨produced, after, z', result, ys, ?_, stateA, buffersA, accountA, mass, cost⟩
  unfold slowEofTail
  rw [bind_app, settleRun]
  simp only []
  rw [bind_app, insertRun]
  exact tailRun

end Zlib.Deflate.Engine.Proofs
