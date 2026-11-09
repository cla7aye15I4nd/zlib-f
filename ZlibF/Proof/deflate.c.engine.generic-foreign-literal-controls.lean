import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-content»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-literal-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-search-prefix»
import ZlibF.Proof.«deflate.c.engine.strategy-controls»
import ZlibF.Proof.«deflate.c.engine.finish-ready-step»
import ZlibF.Proof.«deflate.c.engine.positive-flush-loop»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-match-controls»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_slow_literal_full_run_controls {h after : Heap} {r : ZStreamRef}
    {ds w owner oo origin base : Nat} {z : ZStream} {d result : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : d.lit_bufsize.toNat = 16384)
    (comparisonRoom : d.strstart.toNat + 262 ≤ d.window_size.toNat)
    (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : after.dstates ds = some result) : StrategyControls d result := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := cut.symbols
  have balance1 : BlockBalance d xs 1 := by
    simpa only [deferredCredit, available, ite_false] using balance
  have accounted : base + represented xs + 1 = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_false] using cut.accounted
  obtain ⟨_produced, computed, _z', state, _written, _remaining, _kind, _body,
      tested, goodA, _buffersA, _accountA, _chainsA, _windowA, _bytesA,
      _startA, _lookA, _endA, _countA, _clearA, _symbolsA, frameA,
      _accountedA, _configA, _bitsA, _phaseA, cursorA, _rest⟩ :=
    default_foreign_slow_literal_full_flush_loop cut.good trees buffers cut.frontier positive pointer ready.2.1
      memory comparisonRoom ready.1 (by have bits := ready.2.2; omega)
      ledger clear cut.trace cut.window cut.bytes cut.range lookahead (cut.deferred available)
      balance1 accounted cut.view branch available full flush st candidate
  have heaps : computed = after := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [heaps] at goodA
  have states : state = result := Option.some.inj (goodA.live.hs.symm.trans live)
  rw [← states]
  exact ⟨cursorA, by rw [frameA]; rfl, by rw [frameA]; rfl⟩

end Zlib.Deflate.Engine.Proofs
