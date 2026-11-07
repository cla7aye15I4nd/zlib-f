import ZlibF.Proof.«deflate.c.engine.pending-private-frame»
import ZlibF.Proof.«deflate.c.engine.short-search-frontier»
import ZlibF.Proof.«deflate.c.engine.content-boundary»

/-! # A caller-buffer-independent boundary for public pending phases -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The initialized private content between public calls. Publication
readiness is established after the actual pending drain, rather than
depending on the caller's replaceable output capacity. -/
structure BufferedBoundary (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (input : Nat → UInt8) (origin base : Nat) (xs : List Symbol) (config : EngineConfig) : Prop
    extends ContentBoundary h r ds z d input origin base xs where
  configuration : engineConfig d = config
  clear : BlockInit.BlockClear d
  bits : d.bi_valid.toInt < 8
  strict : d.sym_next.toNat < d.sym_end.toNat
  end_frontier : EndFrontier h d
  empty_cursor : d.pending = 0 → d.pending_out = d.pending_buf

theorem StrategyBoundary.buffered {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : StrategyBoundary h r ds z d input origin base xs config) (frontier : EndFrontier h d)
    (emptyCursor : d.pending = 0 → d.pending_out = d.pending_buf) :
    BufferedBoundary h r ds z d input origin base xs config :=
  ⟨boundary.toContentBoundary, boundary.configuration, boundary.clear, boundary.bits, boundary.strict, frontier, emptyCursor⟩

theorem BufferedBoundary.strategy {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (publish : PublishReady d) :
    StrategyBoundary h r ds z d input origin base xs config :=
  ⟨boundary.toContentBoundary, boundary.configuration, boundary.clear, boundary.bits, boundary.strict, fun _ => publish⟩

/-- Legal rebuffering preserves this same private boundary even when
previously exhausted output is replaced by a positive-capacity buffer. -/
theorem rebuffer_buffered_boundary {h g : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config)
    (edit : Rebuffer h g r) (header : d.gzhead = none) :
    ∃ z', r.get g = some z' ∧ BufferedBoundary g r ds z' d input origin base xs config := by
  obtain ⟨z', get, content⟩ := rebuffer_content_boundary boundary.toContentBoundary edit header
  exact ⟨z', get, content, boundary.configuration, boundary.clear, boundary.bits, boundary.strict,
    rebuffer_chains boundary.good edit boundary.end_frontier, boundary.empty_cursor⟩

/-- Retaining the window and hash arrays transports every chain frontier
through a state update confined to output controls. -/
theorem control_heap_chains {h after : Heap} {d result : DeflateState} {top : Nat}
    (chain : HeapChains h d top)
    (bytes : ∀ b, d.window = .ref (.blk b) 0 → after.bytes b = h.bytes b)
    (words : after.words = h.words)
    (fields : result = { d with
      pending := result.pending, pending_out := result.pending_out,
      status := result.status, last_flush := result.last_flush, wrap := result.wrap }) :
    HeapChains after result top := by
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chain
  refine ⟨w, p, q, wa, pa, qa, ?_, ?_, ?_, (bytes w win).trans hw, ?_, ?_, ?_⟩
  · rw [fields]; exact win
  · rw [fields]; exact prev
  · rw [fields]; exact head
  · rw [words]; exact hp
  · rw [words]; exact hq
  · rw [fields]; exact H

/-- Changes confined to the public output controls preserve every
logical content field when the actual private arrays are retained. -/
theorem content_control_transfer {h after : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z z' : ZStream} {d result : DeflateState} {input : Nat → UInt8} {xs : List Symbol}
    (boundary : ContentBoundary h r ds z d input origin base xs) (goodA : DGood after r ds z' result)
    (bytes : ∀ b, d.window = .ref (.blk b) 0 ∨ d.pending_buf = .ref (.blk b) 0 → after.bytes b = h.bytes b)
    (words : after.words = h.words)
    (fields : result = { d with
      pending := result.pending, pending_out := result.pending_out,
      status := result.status, last_flush := result.last_flush, wrap := result.wrap }) :
    ContentBoundary after r ds z' result input origin base xs := by
  have chains : ∀ top, HeapChains h d top → HeapChains after result top :=
    fun _ chain => control_heap_chains chain (fun b win => bytes b (Or.inl win)) words fields
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  have ledgerA : SymbolLedger buf result xs :=
    ledger.keep (by rw [fields]) (by rw [fields]) (by rw [fields]) (by rw [fields])
  have symbols : SymbolBoundary after ds result xs :=
    symbol_boundary_of_ledger goodA (by rw [fields]; exact trees.base.pbuf)
      ((bytes pb (Or.inr trees.base.pbuf)).trans trees.base.bytes) ledgerA
      (by rw [fields]; exact balance)
  obtain ⟨w, wa, win, get, view, form⟩ := boundary.data
  refine ⟨⟨⟨goodA, ?_, ?_, ?_, ?_, symbols, ?_⟩, ?_, ?_, ?_⟩, boundary.trace, ?_⟩
  · have startEq : result.strstart = d.strstart := by rw [fields]
    rw [startEq]
    exact chains d.strstart.toNat boundary.chains
  · rw [fields]; exact boundary.range
  · rw [fields]; exact boundary.history
  · rw [fields]; exact boundary.deferred
  · refine ⟨w, wa, ?_, (bytes w (Or.inl win)).trans get, ?_, ?_⟩
    · rw [fields]; exact win
    · rw [fields]; exact view
    · rw [fields]; exact form
  · rw [fields]; exact boundary.insert_le
  · have startEq : result.strstart = d.strstart := by rw [fields]
    have insertEq : result.insert = d.insert := by rw [fields]
    rw [startEq, insertEq]
    exact chains (d.strstart.toNat - d.insert.toNat) boundary.frontier
  · rw [fields]; exact boundary.ready
  · rw [fields]; exact boundary.accounted

/-- A real output-control update retains the buffered boundary when its
actual private arrays, wrapper configuration and empty-cursor phase hold. -/
theorem buffered_control_transfer {h after : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z z' : ZStream} {d result : DeflateState} {input : Nat → UInt8} {xs : List Symbol} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base xs config) (goodA : DGood after r ds z' result)
    (bytes : ∀ b, d.window = .ref (.blk b) 0 ∨ d.pending_buf = .ref (.blk b) 0 → after.bytes b = h.bytes b)
    (words : after.words = h.words)
    (fields : result = { d with
      pending := result.pending, pending_out := result.pending_out,
      status := result.status, last_flush := result.last_flush, wrap := result.wrap })
    (wrap : result.wrap = d.wrap)
    (emptyCursor : result.pending = 0 → result.pending_out = result.pending_buf) :
    BufferedBoundary after r ds z' result input origin base xs config := by
  have contentA := content_control_transfer boundary.toContentBoundary goodA bytes words fields
  have startEq : result.strstart = d.strstart := by rw [fields]
  have endEq : fillEnd result = fillEnd d := by rw [fields]; rfl
  have endA : EndFrontier after result := by
    unfold EndFrontier
    rw [startEq, endEq]
    exact control_heap_chains boundary.end_frontier (fun b win => bytes b (Or.inl win)) words fields
  have config : ConfigFrame d result := by rw [fields, wrap]; rfl
  refine ⟨contentA, Eq.trans config boundary.configuration, ?_, ?_, ?_, endA, emptyCursor⟩
  · rw [fields]
    exact ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩
  · rw [fields]
    exact boundary.bits
  · rw [fields]
    exact boundary.strict
end Zlib.Deflate.Engine.Proofs
