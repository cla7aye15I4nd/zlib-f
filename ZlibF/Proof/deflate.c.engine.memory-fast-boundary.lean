import ZlibF.Proof.«deflate.c.engine.memory-fast-block-clear»
import ZlibF.Proof.«deflate.c.engine.buffered-boundary»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (InitialFrequencies)
open Zlib.Deflate.Proofs.MemoryInit (MemoryInitStart)
set_option autoImplicit false

/-- Fast strategy parameters with the actual allocation and hash geometry
of every legal memLevel. The selected level, window and wrapper stay explicit. -/
structure MemoryFastConfig (memory : Nat) (config : EngineConfig) : Prop where
  memory_low : 1 ≤ memory
  memory_high : memory ≤ 9
  level_low : 1 ≤ config.level.toInt
  level_high : config.level.toInt ≤ 3
  strategy : config.strategy = 0
  slots : config.memory = UInt32.ofNat (2 ^ (memory + 6))
  window : config.windowBits = 15
  hash : config.hashBits = UInt32.ofNat (memory + 7)
  wrap : config.wrap = 1
  header : config.header = none

/-- The initialized fast boundary retains the parameterized allocation,
content and chain frontiers. This is separate from a full-buffer cost bound. -/
structure MemoryFastBoundary (memory : Nat) (h : Heap) (r : ZStreamRef) (ds : Nat)
    (z : ZStream) (d : DeflateState) (input : Nat → UInt8) (origin base : Nat)
    (xs : List Symbol) (config : EngineConfig) : Prop
    extends BufferedBoundary h r ds z d input origin base xs config where
  options : MemoryFastConfig memory config
  match_small : d.match_length.toNat ≤ 2
  previous_length : d.prev_length = 2
  no_deferred : d.match_available = 0

/-- The actual initializer's content, not geometry alone, establishes
all symbol frequencies and the empty logical trace at every memory level. -/
theorem MemoryFastBoundary.initial {memory : Nat} {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (start : MemoryInitStart memory h r ds z d)
    (frequencies : InitialFrequencies d.dyn_ltree d.dyn_dtree)
    (clear : BlockInit.BlockClear d) (low : 1 ≤ d.level.toInt) (high : d.level.toInt ≤ 3)
    (header : d.gzhead = none) (input : Nat → UInt8) :
    MemoryFastBoundary memory h r ds z d input 0 0 [] (engineConfig d) := by
  obtain ⟨d0, b, buf, trees⟩ := start.good.trees
  have same : d0 = d := Option.some.inj (trees.base.dstate.symm.trans start.good.live.hs)
  subst d0
  have symbol : SymbolBoundary h ds d [] := by
    refine ⟨b, buf, trees, empty_symbol_ledger start.symbols frequencies, ?_⟩
    simp [BlockBalance, deferredCredit, start.start, start.blockStart, start.matchAvailable, represented]
  have startNat : d.strstart.toNat = 0 := by rw [start.start]; rfl
  have lookNat : d.lookahead.toNat = 0 := by rw [start.lookahead]; rfl
  have endNat : fillEnd d = 0 := by simp [fillEnd, startNat, lookNat]
  have chain : HeapChains h d d.strstart.toNat := by rw [startNat]; exact start.chains
  have slow : SlowBoundary h r ds z d input 0 [] := by
    refine ⟨start.good, chain, by rw [endNat]; omega,
      logical_history_initial start.matchLength input 0, ?_, symbol, ?_⟩
    · intro available
      exact False.elim (available start.matchAvailable)
    · obtain ⟨w, p, q, pb, blocks⟩ := start.good.inv.blocks
      obtain ⟨wa, get, _⟩ := blocks.wa
      refine ⟨w, wa, blocks.win, get, ?_, ?_⟩
      · intro i bound; rw [endNat] at bound; omega
      · intro large; omega
  have pending : PendingBoundary h r ds z d input 0 [] := by
    refine ⟨slow, ?_, ?_, fun _ => start.insert⟩
    · rw [start.start, start.insert]; decide
    · simpa only [start.insert, show (0 : UInt32).toNat = 0 from rfl, Nat.sub_zero] using chain
  have content : ContentBoundary h r ds z d input 0 0 [] := by
    refine ⟨pending, .empty, ?_⟩
    simp [represented, pendingCredit, start.start, start.matchAvailable]
  have frontier : EndFrontier h d := by
    unfold EndFrontier
    rw [startNat, Nat.zero_min]
    exact start.chains
  have strict : d.sym_next.toNat < d.sym_end.toNat := by
    have extent := trees.base.sym_end
    have minimum := trees.base.lit_lo
    rw [start.symbols]
    change 0 < d.sym_end.toNat
    omega
  have options : MemoryFastConfig memory (engineConfig d) :=
    ⟨start.memoryLow, start.memoryHigh, low, high, start.strategy, start.literalSlots,
      start.windowBits, start.hashBits, start.wrap, header⟩
  exact ⟨⟨content, rfl, clear, by rw [start.bits]; decide, strict, frontier, fun _ => start.pendingOut⟩,
    options, by rw [start.matchLength]; decide, start.previousLength, start.matchAvailable⟩

/-- Caller replacement preserves the same parameterized private state. -/
theorem MemoryFastBoundary.rebuffer {memory : Nat} {h g : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : MemoryFastBoundary memory h r ds z d input origin base xs config) (edit : Rebuffer h g r) :
    ∃ zg, r.get g = some zg ∧ MemoryFastBoundary memory g r ds zg d input origin base xs config := by
  have header : d.gzhead = none := (congrArg EngineConfig.header boundary.configuration).trans boundary.options.header
  obtain ⟨zg, get, bufferedG⟩ := rebuffer_buffered_boundary boundary.toBufferedBoundary edit header
  exact ⟨zg, get, bufferedG, boundary.options, boundary.match_small, boundary.previous_length, boundary.no_deferred⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.MemoryFastBoundary.initial
#print axioms Zlib.Deflate.Engine.Proofs.MemoryFastBoundary.rebuffer
