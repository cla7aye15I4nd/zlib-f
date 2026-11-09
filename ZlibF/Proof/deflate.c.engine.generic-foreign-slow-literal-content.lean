import ZlibF.Proof.«deflate.c.engine.generic-foreign-slow-literal-loop»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_slow_literal_full_flush_bounded_content {h : Heap} {r : ZStreamRef} {ds pb owner oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (chains : HeapChains h d (d.strstart.toNat + 1 - d.insert.toNat)) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384)
    (comparisonRoom : d.strstart.toNat + 262 ≤ d.window_size.toNat) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (lookahead : 1 ≤ d.lookahead.toNat)
    (previousByte : 1 ≤ d.strstart.toNat) (balance : BlockBalance d xs 1)
    (accounted : base + represented xs + 1 = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i))
    (literalBranch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) 
    (insert : d.insert.toNat ≤ d.strstart.toNat)
    (ready : 3 ≤ d.lookahead.toNat → d.insert = 0) (history : LazyHistory input origin (advanceOne d))
    (form : 3 ≤ d.lookahead.toNat → InsHForm d.hash_shift d.hash_mask (bfn window) (d.strstart.toNat + 1) d.ins_h) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState)
      (written : List UInt8) (remaining : List Bool) (kind : Nat) (body : List Bool),
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if z'.avail_out == 0 then { st with hash_head, bflush := true, ret := some need_more }
          else { st with hash_head, bflush := true }), after) ∧
      ContentBoundary after r ds z' result input origin
        (base + represented (xs ++ [emittedLiteral d window])) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      ConfigFrame d result ∧ result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧ result.strstart.toNat < 65536 ∧
      PendingBits h d (Zlib.Trees.Proofs.Out.outBits buf d) ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧ kind < 3 ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ++
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented (xs ++ [emittedLiteral d window]))) := by
  obtain ⟨produced, after, z', result, written, remaining, kind, body, run, goodA, buffersA, accountA, chainsA, winA, bytesA,
    startA, lookA, endpoint, _countA, clearA, symbolsA, frameA, accountedA, configA, lowA, phaseA, cursorA, smallA, pendingBefore, bytesAOut, pendingAfter, kindBound, wire, grammar⟩ :=
    default_foreign_slow_literal_full_flush_loop good trees buffers chains positive pointer cursor memory comparisonRoom pending bits ledger clear trace
      win get range lookahead previousByte balance accounted view literalBranch available full flush st hash_head
  have insertA : result.insert = d.insert := by rw [frameA]; rfl
  have availableA : result.match_available ≠ 0 := by rw [frameA]; exact available
  have shiftA : result.hash_shift = d.hash_shift := by rw [frameA]; rfl
  have maskA : result.hash_mask = d.hash_mask := by rw [frameA]; rfl
  have keyA : result.ins_h = d.ins_h := by rw [frameA]; rfl
  have sizeA : result.window_size = d.window_size := by rw [frameA]; rfl
  have logicalA : LazyHistory input origin result := by rw [frameA]; exact history
  have frontierAt : HeapChains after result (result.strstart.toNat - result.insert.toNat) := by
    simpa only [startA, insertA] using chainsA
  have chainsAt : HeapChains after result result.strstart.toNat :=
    heap_chains_raise frontierAt (Nat.sub_le _ _)
  refine ⟨produced, after, z', result, written, remaining, kind, body, run, ?_, buffersA, accountA, clearA, startA, lookA, endpoint, configA, lowA, phaseA, cursorA, smallA, pendingBefore, bytesAOut, pendingAfter, kindBound, wire, grammar⟩
  refine ⟨⟨⟨goodA, chainsAt, ?_, logicalA, ?_, symbolsA, ?_⟩, ?_, frontierAt, ?_⟩, Trace.empty, ?_⟩
  · rw [endpoint, sizeA]; exact range
  · intro _
    rw [startA]
    omega
  · refine ⟨w, window, winA, bytesA, ?_, ?_⟩
    · intro i bound
      rw [endpoint] at bound
      exact view i bound
    · intro enough
      rw [shiftA, maskA, startA, keyA]
      apply form
      rw [lookA] at enough
      omega
  · rw [insertA, startA]
    omega
  · intro enough
    rw [insertA]
    apply ready
    rw [lookA] at enough
    omega
  · simpa only [represented, pendingCredit, availableA, ite_false, Nat.add_zero] using accountedA

end Zlib.Deflate.Engine.Proofs
