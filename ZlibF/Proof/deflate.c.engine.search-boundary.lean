import ZlibF.Proof.«deflate.c.engine.short-search-frontier»

/-! # The initialized content boundary reaches every real search decision -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The phase after search and before the slow decision. Previous-match
history and current-search byte evidence have different positions here.
The three chain frontiers describe the same actual arrays. -/
structure SearchBoundary (h : Heap) (r : ZStreamRef) (ds : Nat) (z : ZStream) (d : DeflateState)
    (input : Nat → UInt8) (origin base : Nat) (xs : List Symbol) (w : Nat) (wa : Array UInt8) : Prop where
  good : DGood h r ds z d
  chains : HeapChains h d (d.strstart.toNat + 1)
  frontier : HeapChains h d (d.strstart.toNat + 1 - d.insert.toNat)
  end_frontier : HeapChains h d (min (d.strstart.toNat + 1) (fillEnd d - 2))
  range : fillEnd d ≤ d.window_size.toNat
  previous : PreviousHistory input origin d
  deferred : DeferredByte d
  symbols : SymbolBoundary h ds d xs
  insert_le : d.insert.toNat ≤ d.strstart.toNat
  ready : 3 ≤ d.lookahead.toNat → d.insert = 0
  window : d.window = .ref (.blk w) 0
  bytes : h.bytes w = some wa
  view : ∀ i, i < fillEnd d → bfn wa i = input (origin + i)
  length : d.match_length.toNat ≤ 258
  clipped : 3 ≤ d.match_length.toNat → d.match_length.toNat ≤ d.lookahead.toNat
  matching : 3 ≤ d.match_length.toNat → d.prev_length.toNat < d.match_length.toNat →
    GoodMatch wa d.strstart.toNat d.w_size.toNat d.match_start.toNat d.match_length.toNat
  primed : 3 ≤ d.lookahead.toNat →
    InsHForm d.hash_shift d.hash_mask (bfn wa) (d.strstart.toNat + 1) d.ins_h
  trace : Trace input base xs
  accounted : base + represented xs + pendingCredit d = origin + d.strstart.toNat

/-- The real search reaches this phase at every lookahead length. Its
input is the initialized content boundary plus the saved EOF frontier.
No successful search or matching-callee contract is an assumption. -/
theorem slow_search_initialized_boundary {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (room : 3 ≤ d.lookahead.toNat → d.strstart.toNat + 262 ≤ d.window_size.toNat) :
    ∃ w wa candidate after result,
      slowSearch (some (.tab ds)) h = .ok (candidate, after) ∧
      SearchBoundary after r ds z result input origin base xs w wa ∧
      SearchWorkFrame d result ∧ StreamBuffers after r ∧ ByteFrame h after (fun k => k = ds) := by
  obtain ⟨w, wa, win, get, view, _form⟩ := boundary.data
  obtain ⟨candidate, after, result, run, goodA, chainsA, winA, bytesA, previousA, deferredA,
      symbolsA, lengthA, clippedA, matchingA, formA, _slowFrame, frameA, storage⟩ :=
    slow_search_all_frame boundary win get room
  have startA : result.strstart = d.strstart := by rw [frameA]
  have lookA : result.lookahead = d.lookahead := by rw [frameA]
  have insertA : result.insert = d.insert := by rw [frameA]
  have endpoint : fillEnd result = fillEnd d := by rw [frameA]; rfl
  have frontierA := slow_search_pending_frontier boundary run goodA chainsA
  have endA := slow_search_end_frontier boundary.good frontier run goodA chainsA
  have owned := stream_owned_keys boundary.good goodA
    (by rw [frameA]) (by rw [frameA]) (by rw [frameA]) (by rw [frameA])
  have buffersA := stream_buffers_private_read boundary.good.live.hz goodA.live.hz buffers storage
    (fun k equal => (stream_owned_deflate boundary.good k).mpr (Or.inl equal)) owned (stream_accounting_zero z)
  refine ⟨w, wa, candidate, after, result, run, ?_, frameA, buffersA, storage⟩
  refine ⟨goodA, ?_, ?_, ?_, ?_, previousA, deferredA, symbolsA, ?_, ?_, winA, bytesA,
    ?_, lengthA, ?_, matchingA, ?_, boundary.trace, ?_⟩
  · simpa only [startA] using chainsA
  · simpa only [startA, insertA] using frontierA
  · simpa only [startA, endpoint] using endA
  · rw [frameA]; exact boundary.range
  · rw [insertA, startA]; exact boundary.insert_le
  · rw [frameA]; exact boundary.ready
  · rw [frameA]; exact view
  · intro large
    rw [lookA]
    exact clippedA large
  · intro three
    apply formA
    rw [lookA] at three
    exact three
  · rw [frameA]; exact boundary.accounted

end Zlib.Deflate.Engine.Proofs
