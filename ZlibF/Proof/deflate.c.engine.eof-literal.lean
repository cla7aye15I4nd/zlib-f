import ZlibF.Proof.«deflate.c.engine.eof-insert»

/-! # Settlement of the slow strategy's final deferred literal -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real EOF prefix emits the remaining deferred byte once and clears
its credit. A tally may fill the symbol buffer; the following final flush
accepts that state. No byte is consumed from the caller here. -/
theorem slow_eof_literal_content_frame {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (strict : d.sym_next.toNat < d.sym_end.toNat)
    (clear : BlockInit.BlockClear d) :
    ∃ after result ys,
      slowEofLiteral (some (.tab ds)) h = .ok ((), after) ∧
      ContentBoundary after r ds z result input origin base ys ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ result.match_available = 0 ∧ result.lookahead = 0 ∧
      result.strstart = d.strstart ∧ result.sym_next.toNat ≤ result.sym_end.toNat ∧
      BlockInit.BlockClear result ∧ ConfigFrame d result ∧ SlowRecordFrame d result ∧
      (ys = xs ∨ ∃ wa, ys = xs ++ [emittedLiteral d wa]) := by
  by_cases available : d.match_available = 0
  · refine ⟨h, d, xs, ?_, boundary, frontier, buffers, available, empty, rfl,
      Nat.le_of_lt strict, clear, rfl, rfl, Or.inl rfl⟩
    unfold slowEofLiteral
    simp only [bind_app, ldDeflateState_tab boundary.good.live.hs, available,
      bne_self_eq_false, Bool.false_eq_true, ite_false, pure_app]
  · obtain ⟨w, wa, win, get, view, form⟩ := boundary.data
    obtain ⟨b, buf, trees, ledger, balance⟩ := boundary.symbols
    let c := wa[d.strstart.toNat - 1]!
    let dt := literalState d c
    let packed := literalBytes buf d c
    let ht := setD (Zlib.Trees.Proofs.Out.setB h b packed) ds dt
    let result := { dt with match_available := 0 }
    let after := setD ht ds result
    let ys := xs ++ [emittedLiteral d wa]
    have room := literal_room boundary.good.inv strict
    have goodT : DGood ht r ds z dt := literal_good_after boundary.good trees c room
    have inv : DStInv ht ds result :=
      { goodT.inv with blocks := goodT.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
    have goodA : DGood after r ds z result := goodT.setD' (d' := result) rfl goodT.live.status inv (by trkeep)
    have chainsT : HeapChains ht dt d.strstart.toNat :=
      pending_write_chains boundary.good boundary.chains trees.base.pbuf packed c
    have frontierT : HeapChains ht dt (d.strstart.toNat - d.insert.toNat) :=
      pending_write_chains boundary.good boundary.frontier trees.base.pbuf packed c
    have endT : HeapChains ht dt (min d.strstart.toNat (fillEnd d - 2)) :=
      pending_write_chains boundary.good frontier trees.base.pbuf packed c
    have chainsA : HeapChains after result result.strstart.toNat :=
      (chainsT.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl).collapse rfl
    have frontierA : HeapChains after result (result.strstart.toNat - result.insert.toNat) :=
      (frontierT.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl).collapse rfl
    have endA : EndFrontier after result :=
      (endT.at.keep rfl rfl rfl rfl rfl rfl rfl rfl rfl).collapse rfl
    have getA : after.bytes w = some wa := pending_window_frame boundary.good win trees.base.pbuf get packed result
    have ledgerT : SymbolLedger packed dt ys := ledger_literal trees.base ledger room c
    have ledgerA : SymbolLedger packed result ys := ledgerT.keep rfl rfl rfl rfl
    have balance1 : BlockBalance d xs 1 := by
      simpa only [deferredCredit, available, ite_false] using balance
    have balanceT : BlockBalance dt ys 0 := by
      simpa only [dt, ys, c, emittedLiteral, show (1 : Int) - 1 = 0 from rfl] using balance_literal balance1 c
    have zeroFlag : result.match_available = 0 := rfl
    have balanceA : BlockBalance result ys (deferredCredit result) := by
      simpa only [deferredCredit, zeroFlag, ite_true] using (show BlockBalance result ys 0 from balanceT)
    have getPacked : after.bytes b = some packed := by simp [after, ht]
    have symbolsA := symbol_boundary_of_ledger goodA trees.base.pbuf getPacked ledgerA balanceA
    have historyA : LazyHistory input origin result := by
      refine ⟨boundary.history.1, ?_⟩
      intro large
      have remaining := (boundary.history.2 large).2.2.1
      rw [empty] at remaining
      change d.match_length.toNat ≤ 0 + 1 at remaining
      change 3 ≤ d.match_length.toNat at large
      omega
    have credit : pendingCredit d = 1 := by simp only [pendingCredit, available, ite_false]
    have oldAccount := boundary.accounted
    rw [credit] at oldAccount
    have meaning := literal_input_meaning boundary.deferred available view
    have position : base + represented xs = origin + d.strstart.toNat - 1 := by omega
    rw [← position] at meaning
    have traceA : Trace input base ys := boundary.trace.snoc meaning
    have accountedA : base + represented ys + pendingCredit result = origin + result.strstart.toNat := by
      simp only [ys, represented_snoc, show (emittedLiteral d wa).bytes = 1 from rfl,
        pendingCredit, zeroFlag, ite_true, Nat.add_zero]
      exact oldAccount
    have boundaryA : ContentBoundary after r ds z result input origin base ys := by
      refine ⟨⟨⟨goodA, chainsA, boundary.range, historyA, ?_, symbolsA, ?_⟩,
        boundary.insert_le, frontierA, ?_⟩, traceA, accountedA⟩
      · intro has; exact False.elim (has zeroFlag)
      · exact ⟨w, wa, win, getA, view, form⟩
      · intro enough
        change 3 ≤ d.lookahead.toNat at enough
        rw [empty] at enough
        change 3 ≤ 0 at enough
        omega
    have recordA : SlowRecordFrame d result := rfl
    have storage := (pending_state_byte_frame h ds b d dt packed trees.base.pbuf).trans
      ((byte_frame_setD ht ds result).weaken (fun _ equal => Or.inl equal :
        ∀ k, k = ds → DeflateOwned ds d k))
    have owned := stream_owned_keys boundary.good goodA rfl rfl rfl rfl
    have buffersA := stream_buffers_private_read boundary.good.live.hz goodA.live.hz buffers storage
      (fun k own => (stream_owned_deflate boundary.good k).mpr own) owned (stream_accounting_zero z)
    have count : result.sym_next.toNat ≤ result.sym_end.toNat := by
      have exactCount := literal_count trees.base room c
      change (d.sym_next + 3).toNat = d.sym_next.toNat + 3 at exactCount
      change (d.sym_next + 3).toNat ≤ d.sym_end.toNat
      rw [exactCount]
      exact room
    refine ⟨after, result, ys, ?_, boundaryA, endA, buffersA, zeroFlag, empty, rfl, count,
      clear.slow recordA, rfl, recordA, Or.inr ⟨wa, rfl⟩⟩
    obtain ⟨size, _⟩ := window_extent boundary.good win get
    have previousByte := boundary.deferred available
    have ranged := boundary.range
    have fit : d.strstart.toNat - 1 < wa.size := by dsimp only [fillEnd] at ranged; omega
    have read : index8 d.window (d.strstart - 1).toNat h = .ok (c, h) := by
      rw [win, u32_sub_one previousByte]
      simpa [OkOn, fit, c] using index8_ok (off := 0) (i := d.strstart.toNat - 1) get (by omega)
    have tally : tally_lit (some (.tab ds)) c h = .ok (d.sym_next + 3 == d.sym_end, ht) :=
      tally_literal_run trees.base c room
    have put : wr (some (.tab ds)) (fun d => { d with match_available := 0 }) ht = .ok ((), after) := by
      simp only [wrD_eq, goodT.live.hs]
      rfl
    unfold slowEofLiteral
    have has : (d.match_available != 0) = true := by simpa using available
    simp only [bind_app, ldDeflateState_tab boundary.good.live.hs, has, ite_true, read, tally]
    exact put

/-- The earlier content-only cutpoint follows from its stronger frame. -/
theorem slow_eof_literal_content {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (empty : d.lookahead = 0) (strict : d.sym_next.toNat < d.sym_end.toNat)
    (clear : BlockInit.BlockClear d) :
    ∃ after result ys,
      slowEofLiteral (some (.tab ds)) h = .ok ((), after) ∧
      ContentBoundary after r ds z result input origin base ys ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ result.match_available = 0 ∧ result.lookahead = 0 ∧
      result.strstart = d.strstart ∧ result.sym_next.toNat ≤ result.sym_end.toNat ∧
      BlockInit.BlockClear result ∧ ConfigFrame d result ∧
      (ys = xs ∨ ∃ wa, ys = xs ++ [emittedLiteral d wa]) := by
  obtain ⟨after, result, ys, run, boundaryA, frontierA, buffersA, flag, look, start, count,
      clearA, configA, _recordA, symbols⟩ :=
    slow_eof_literal_content_frame boundary frontier buffers empty strict clear
  exact ⟨after, result, ys, run, boundaryA, frontierA, buffersA, flag, look, start, count,
    clearA, configA, symbols⟩

end Zlib.Deflate.Engine.Proofs
