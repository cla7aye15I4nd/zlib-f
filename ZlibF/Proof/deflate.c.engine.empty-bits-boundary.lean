import ZlibF.Proof.«deflate.c.engine.header-buffered»
import ZlibF.Proof.«deflate.c.engine.block-windup»

/-! # Bit output preserves the completed-block content boundary -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- Bit-output fields do not change the real window or hash-chain view. -/
theorem bits_heap_chains {h after : Heap} {d result : DeflateState} {top : Nat}
    (chain : HeapChains h d top)
    (bytes : ∀ b, d.window = .ref (.blk b) 0 → after.bytes b = h.bytes b)
    (words : after.words = h.words) (fields : BitsDiff d result) :
    HeapChains after result top := by
  obtain ⟨_, _, _, _, equal⟩ := fields
  rw [equal]
  obtain ⟨w, p, q, wa, pa, qa, win, prev, head, hw, hp, hq, H⟩ := chain
  exact ⟨w, p, q, wa, pa, qa, win, prev, head, (bytes w win).trans hw,
    by rw [words]; exact hp, by rw [words]; exact hq, H⟩

/-- After a completed block the empty symbol ledger has no unread packed
bytes. Actual bit writes may replace the pending buffer while preserving
all input history, window data, frequencies and hash frontiers. -/
theorem empty_content_bits_transfer {h after : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z z' : ZStream} {d result : DeflateState} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base []) (goodA : DGood after r ds z' result)
    (bytes : ∀ b, d.window = .ref (.blk b) 0 → after.bytes b = h.bytes b)
    (words : after.words = h.words) (fields : BitsDiff d result) :
    ContentBoundary after r ds z' result input origin base [] := by
  have chains : ∀ top, HeapChains h d top → HeapChains after result top :=
    fun _ chain => bits_heap_chains chain bytes words fields
  obtain ⟨_, _, _, ledger, balance⟩ := boundary.symbols
  obtain ⟨_, _, _, pb, blocks⟩ := goodA.inv.blocks
  obtain ⟨buf, getB, _⟩ := blocks.ba
  have ledgerA : SymbolLedger buf result [] := empty_ledger_bits ledger fields
  obtain ⟨_, _, _, _, equal⟩ := fields
  have symbols : SymbolBoundary after ds result [] :=
    symbol_boundary_of_ledger goodA blocks.pbuf getB ledgerA (by rw [equal]; exact balance)
  obtain ⟨w, wa, win, get, view, form⟩ := boundary.data
  refine ⟨⟨⟨goodA, ?_, ?_, ?_, ?_, symbols, ?_⟩, ?_, ?_, ?_⟩, boundary.trace, ?_⟩
  · have startEq : result.strstart = d.strstart := by rw [equal]
    rw [startEq]
    exact chains d.strstart.toNat boundary.chains
  · rw [equal]; exact boundary.range
  · rw [equal]; exact boundary.history
  · rw [equal]; exact boundary.deferred
  · refine ⟨w, wa, ?_, (bytes w win).trans get, ?_, ?_⟩
    · rw [equal]; exact win
    · rw [equal]; exact view
    · rw [equal]; exact form
  · rw [equal]; exact boundary.insert_le
  · have startEq : result.strstart = d.strstart := by rw [equal]
    have insertEq : result.insert = d.insert := by rw [equal]
    rw [startEq, insertEq]
    exact chains (d.strstart.toNat - d.insert.toNat) boundary.frontier
  · rw [equal]; exact boundary.ready
  · rw [equal]; exact boundary.accounted

/-- The same caller-independent empty-block boundary survives real bit
output once its actual returned bit count and base cursor are established. -/
theorem empty_buffered_bits_transfer {h after : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z z' : ZStream} {d result : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (goodA : DGood after r ds z' result)
    (bytes : ∀ b, d.window = .ref (.blk b) 0 → after.bytes b = h.bytes b)
    (words : after.words = h.words) (fields : BitsDiff d result)
    (low : result.bi_valid.toInt < 8) (cursor : result.pending_out = result.pending_buf) :
    BufferedBoundary after r ds z' result input origin base [] config := by
  have contentA := empty_content_bits_transfer boundary.toContentBoundary goodA bytes words fields
  have frame := ConfigFrame.bits fields
  have chains := bits_heap_chains boundary.end_frontier bytes words fields
  obtain ⟨_, _, _, _, equal⟩ := fields
  refine ⟨contentA, Eq.trans frame boundary.configuration, ?_, low, ?_, ?_, fun _ => cursor⟩
  · rw [equal]; exact ⟨boundary.clear.bl, boundary.clear.opt, boundary.clear.fixed⟩
  · rw [equal]; exact boundary.strict
  · unfold EndFrontier at chains ⊢
    rw [equal] at chains ⊢
    exact chains

end Zlib.Deflate.Engine.Proofs
