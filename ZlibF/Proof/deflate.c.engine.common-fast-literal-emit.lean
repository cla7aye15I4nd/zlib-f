import ZlibF.Proof.«deflate.c.engine.common-fast-symbol-meaning»

/-! # Actual immediate literal tally restores fast content at every EOF length -/
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual fast literal branch reads, tallies and then consumes one byte. -/
def fastLiteralEmit (s : DeflateStatePtr) : M Bool := do
  let d ← ldDeflateState s
  let c ← index8 d.window d.strstart.toNat
  let full ← tally_lit s c
  wr s (fun d => {d with lookahead := d.lookahead - 1, strstart := d.strstart + 1})
  pure full

/-- Literal tally and one-byte advancement restore the initialized fast
content, including both saved insertion frontiers. The exact symbol and
its input meaning refer to the same actual execution, including a full
symbol buffer before the subsequent block flush. -/
theorem fast_literal_emit_search_boundary {h : Heap} {r : ZStreamRef} {ds w origin base : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa) (buffers : StreamBuffers h r)
    (previous : d.prev_length = 2) (noDeferred : d.match_available = 0)
    (literal : d.match_length.toNat ≤ 2) (positive : 1 ≤ d.lookahead.toNat)
    (strict : d.sym_next.toNat < d.sym_end.toNat) :
    ∃ after result,
      fastLiteralEmit (some (.tab ds)) h = .ok (d.sym_next + 3 == d.sym_end, after) ∧
      ContentBoundary after r ds z result input origin base (xs ++ [fastLiteralSymbol d wa]) ∧
      EndFrontier after result ∧ StreamBuffers after r ∧ SlowRecordFrame d result ∧
      result.match_length.toNat ≤ 2 ∧ result.match_available = 0 ∧ result.prev_length = 2 ∧
      result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat = d.sym_next.toNat + 3 ∧ result.sym_end = d.sym_end ∧
      ByteFrame h after (DeflateOwned ds d) := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := cut.symbols
  have space := literal_room cut.good.inv strict
  let c := bfn wa d.strstart.toNat
  let packed := literalBytes buf d c
  let dt := literalState d c
  let ht := setD (Zlib.Trees.Proofs.Out.setB h pb packed) ds dt
  let result := advanceOne dt
  let after := setD ht ds result
  have goodT : DGood ht r ds z dt := literal_good_after cut.good trees c space
  have chainsT : HeapChains ht dt (d.strstart.toNat + 1) :=
    pending_write_chains cut.good cut.chains trees.base.pbuf packed 0
  have pendingT : HeapChains ht dt (d.strstart.toNat + 1 - d.insert.toNat) :=
    pending_write_chains cut.good cut.frontier trees.base.pbuf packed 0
  have endT : HeapChains ht dt (min (d.strstart.toNat + 1) (fillEnd d - 2)) :=
    pending_write_chains cut.good cut.end_frontier trees.base.pbuf packed 0
  have counts := advance_one_counts goodT.inv cut.range positive
  change result.strstart.toNat = d.strstart.toNat + 1 ∧
    result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d at counts
  have goodA := (advance_one_good goodT chainsT cut.range positive).1
  have chainsA : HeapChains after result result.strstart.toNat := by
    rw [counts.1]
    exact (advance_one_good goodT chainsT cut.range positive).2.1
  have pendingA : HeapChains after result (result.strstart.toNat - result.insert.toNat) := by
    rw [counts.1]
    exact (advance_one_good goodT pendingT cut.range positive).2.1
  have endpoint : fillEnd result = fillEnd d := counts.2.2
  have endA : EndFrontier after result := by
    unfold EndFrontier
    rw [counts.1, endpoint]
    exact (advance_one_good goodT endT cut.range positive).2.1
  have getT : ht.bytes w = some wa := pending_window_frame cut.good cut.window trees.base.pbuf cut.bytes packed dt
  have getA : after.bytes w = some wa := getT
  have ledgerT : SymbolLedger packed dt (xs ++ [fastLiteralSymbol d wa]) := ledger_literal trees.base ledger space c
  have ledgerA : SymbolLedger packed result (xs ++ [fastLiteralSymbol d wa]) := ledgerT.keep rfl rfl rfl rfl
  have availableA : result.match_available = 0 := noDeferred
  have previousA : result.prev_length = 2 := previous
  have smallA : result.match_length.toNat ≤ 2 := literal
  have credit : deferredCredit d = 0 := by simp [deferredCredit, noDeferred]
  have balanceA : BlockBalance result (xs ++ [fastLiteralSymbol d wa]) (deferredCredit result) := by
    unfold BlockBalance at balance ⊢
    rw [credit] at balance
    simp only [deferredCredit, availableA, ite_true, represented_snoc,
      show (fastLiteralSymbol d wa).bytes = 1 from rfl]
    rw [counts.1]
    change ((d.strstart.toNat + 1 : Nat) : Int) - d.block_start.toInt = _
    omega
  have getPacked : after.bytes pb = some packed := by simp [after, ht]
  have symbolsA := symbol_boundary_of_ledger goodA trees.base.pbuf getPacked ledgerA balanceA
  have storage := (pending_state_byte_frame h ds pb d dt packed trees.base.pbuf).trans
    ((byte_frame_setD ht ds result).weaken (fun _ equal => Or.inl equal))
  have frame : SlowRecordFrame d result := rfl
  have owned := stream_owned_keys cut.good goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_private_read cut.good.live.hz goodA.live.hz buffers storage
    (fun k own => (stream_owned_deflate cut.good k).mpr own) owned (stream_accounting_zero z) (by rfl)
  have countA : result.sym_next.toNat = d.sym_next.toNat + 3 := literal_count trees.base space c
  have read : index8 d.window d.strstart.toNat h = .ok (c, h) := by
    have extent := window_extent cut.good cut.window cut.bytes
    have fit : d.strstart.toNat < wa.size := by have range := cut.range; unfold fillEnd at range; omega
    rw [cut.window]
    simpa [OkOn, fit, c, bfn] using index8_ok (off := 0) (i := d.strstart.toNat) cut.bytes (by omega)
  have tally : tally_lit (some (.tab ds)) c h = .ok (d.sym_next + 3 == d.sym_end, ht) :=
    tally_literal_run trees.base c space
  have write : wr (some (.tab ds)) (fun d => {d with lookahead := d.lookahead - 1, strstart := d.strstart + 1}) ht =
      .ok ((), after) := by simp [wrD_eq, goodT.live.hs, after, result, advanceOne]
  refine ⟨after, result, ?_, ?_, endA, buffersA, frame, smallA, availableA, previousA,
    counts.1, counts.2.1, endpoint, countA, rfl, storage⟩
  · unfold fastLiteralEmit
    simp only [bind_app, ldDeflateState_tab cut.good.live.hs, read, tally, write, pure_app]
  · refine ⟨⟨⟨goodA, chainsA, ?_, ?_, ?_, symbolsA, ?_⟩, ?_, pendingA, ?_⟩,
      fast_literal_trace cut noDeferred positive, ?_⟩
    · rw [endpoint]; exact cut.range
    · refine ⟨by omega, ?_⟩
      intro impossible
      omega
    · intro available
      exact False.elim (available availableA)
    · refine ⟨w, wa, cut.window, getA, ?_, ?_⟩
      · intro i fit
        rw [endpoint] at fit
        exact cut.view i fit
      · intro three
        change InsHForm d.hash_shift d.hash_mask (bfn wa) result.strstart.toNat d.ins_h
        rw [counts.1]
        apply cut.primed
        rw [counts.2.1] at three
        omega
    · have bound := cut.insert_le
      change d.insert.toNat ≤ result.strstart.toNat
      rw [counts.1]
      omega
    · intro three
      apply cut.ready
      rw [counts.2.1] at three
      omega
    · simp only [pendingCredit, availableA, ite_true, Nat.add_zero, represented_snoc,
        show (fastLiteralSymbol d wa).bytes = 1 from rfl]
      rw [counts.1]
      have account := cut.accounted
      simp only [pendingCredit, noDeferred, ite_true, Nat.add_zero] at account
      omega

end Zlib.Deflate.Engine.Proofs
