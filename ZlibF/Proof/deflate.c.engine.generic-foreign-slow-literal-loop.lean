import ZlibF.Proof.«deflate.c.engine.generic-foreign-private-arrays»
import ZlibF.Proof.«deflate.c.engine.input-snapshot-controls»
import ZlibF.Proof.«deflate.c.engine.short-literal-full-boundary»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual full deferred-literal decision with foreign-depth output: tally, flush,
publication and one-byte advance retain the source order, including short and zero output. -/
theorem default_foreign_slow_literal_full_flush_loop {h : Heap} {r : ZStreamRef} {ds pb owner oo w top origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (chains : HeapChains h d top) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (comparisonRoom : d.strstart.toNat + 262 ≤ d.window_size.toNat) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (lookahead : 1 ≤ d.lookahead.toNat)
    (previousByte : 1 ≤ d.strstart.toNat) (balance : BlockBalance d xs 1)
    (accounted : base + represented xs + 1 = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i))
    (literalBranch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (flush : Int32) (st : LoopS) (hash_head : UInt32) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState)
      (written : List UInt8) (remaining : List Bool) (kind : Nat) (body : List Bool),
      slowDecision (some (.tab ds)) flush st hash_head h =
        .ok ((if z'.avail_out == 0 then { st with hash_head, bflush := true, ret := some need_more }
          else { st with hash_head, bflush := true }), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      HeapChains after result top ∧ result.window = .ref (.blk w) 0 ∧ after.bytes w = some window ∧
      result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      result.sym_next = 0 ∧ BlockInit.BlockClear result ∧ SymbolBoundary after ds result [] ∧
      FlushWorkFrame { advanceOne d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      base + represented (xs ++ [emittedLiteral d window]) + 1 = origin + result.strstart.toNat ∧
      ConfigFrame d result ∧ result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧ result.strstart.toNat < 65536 ∧
      PendingBits h d (Zlib.Trees.Proofs.Out.outBits buf d) ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧ kind < 3 ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ++
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented (xs ++ [emittedLiteral d window]))) := by
  have windowMax : d.window_size.toNat ≤ 65536 := by
    have power := Nat.pow_le_pow_right (n := 2) (by decide) good.inv.wbits_hi
    rw [good.inv.wsz, good.inv.wsize]
    omega
  have startSmall : d.strstart.toNat < 65536 := by omega
  let c := window[d.strstart.toNat - 1]!
  let dt := literalState d c
  let packed := literalBytes buf d c
  let ht := setD (Zlib.Trees.Proofs.Out.setB h pb packed) ds dt
  have room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat := Nat.le_of_eq full
  have goodT : DGood ht r ds z dt := literal_good_after good trees c room
  have treesT : TreesInvAt ht ds dt pb packed := tally_literal_trees trees c room
  have tallyFrame := pending_state_byte_frame h ds pb d dt packed trees.base.pbuf
  have tallyOwned := stream_owned_keys good goodT rfl rfl rfl rfl
  have buffersT : StreamBuffers ht r := stream_buffers_private_read good.live.hz goodT.live.hz buffers
    tallyFrame (fun b owned => (stream_owned_deflate good b).mpr owned) tallyOwned (stream_accounting_zero z) rfl
  have chainsT : HeapChains ht dt top := pending_write_chains good chains trees.base.pbuf packed c
  have getT : ht.bytes w = some window := pending_window_frame good win trees.base.pbuf get packed dt
  have ledgerT : SymbolLedger packed dt (xs ++ [emittedLiteral d window]) := ledger_literal trees.base ledger room c
  have balanceT : BlockBalance dt (xs ++ [emittedLiteral d window]) 0 := by
    simpa only [dt, c, emittedLiteral, show (1 : Int) - 1 = 0 from rfl] using balance_literal balance c
  have sizeLiteral : (emittedLiteral d window).bytes = 1 := rfl
  have accountedT : base + represented (xs ++ [emittedLiteral d window]) = origin + dt.strstart.toNat := by
    rw [represented_snoc, sizeLiteral]
    exact accounted
  have meaning := literal_input_meaning (show DeferredByte d from fun _ => previousByte) available view
  have oldEnd : base + represented xs = origin + d.strstart.toNat - 1 := by omega
  rw [← oldEnd] at meaning
  have traceT := trace.snoc meaning
  have clearT : BlockInit.BlockClear dt := ⟨clear.bl, clear.opt, clear.fixed⟩
  have flag : (d.sym_next + 3 == d.sym_end) = true := by
    apply beq_iff_eq.mpr
    apply UInt32.toNat_inj.mp
    rw [← full]
    exact literal_count trees.base room c
  have tally : tally_lit (some (.tab ds)) c h = .ok (true, ht) := by
    simpa only [flag] using tally_literal_run trees.base c room
  obtain ⟨produced,emittedHeap,z',emitted,written,remaining,kind,body,padding,
    emitRun,goodE,buffersE,accountE,_sizesE,storageE,frame,lowE,_finalE,clearE,count,frequenciesE,
    _cursorE,phaseE,positionE,_bytesE,_pendingE,_bufferE,_kindE,_padBound,_padNone,_storedPad,_outputE,_grammarE⟩ :=
    default_flush_block_only_foreign_publish goodT treesT buffersT positive pointer cursor memory
      pending bits ledgerT clearT traceT win getT range balanceT accountedT view false
  have emitRun0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 ht = .ok ((), emittedHeap) := emitRun
  have phase : True ∧ emitted.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady emitted) :=
    ⟨trivial, lowE, phaseE⟩
  have rangeE : fillEnd emitted ≤ emitted.window_size.toNat := by rw [frame]; exact range
  have lookE : 1 ≤ emitted.lookahead.toNat := by rw [frame]; exact lookahead
  have startE : emitted.strstart = d.strstart := by rw [frame]; rfl
  have lookEq : emitted.lookahead = d.lookahead := by rw [frame]; rfl
  have chainsE := foreign_flush_frames_chains storageE goodT buffersT pointer treesT.base.pbuf frame chainsT
  obtain ⟨wc, p, q, wa, pa, qa, winC, prev, head, getC, getPrev, getHead, _chainC⟩ := chainsT
  change d.window = .ref (.blk wc) 0 at winC
  have windowEq : wc = w := by simpa only [win, Ptr.ref.injEq, BRef.blk.injEq, and_true] using winC.symm
  subst wc
  have arrayEq : wa = window := Option.some.inj (getC.symm.trans getT)
  subst wa
  have kept := storageE.foreign_private_arrays goodT buffersT pointer win getT prev getPrev head getHead treesT.base.pbuf
  let result := advanceOne emitted
  let after := setD emittedHeap ds result
  have counts := advance_one_counts goodE.inv rangeE lookE
  have advanced := advance_one_good goodE chainsE rangeE lookE
  have goodA : DGood after r ds z' result := advanced.1
  have write : wr (some (.tab ds)) advanceOne emittedHeap = .ok ((), after) := by
    simp only [wrD_eq, goodE.live.hs, after, result]
  have storageAdvance := (byte_frame_setD emittedHeap ds result).weaken (fun _ equal => Or.inl equal :
    ∀ b, b = ds → DeflateOwned ds emitted b)
  have ownedAdvance := stream_owned_keys goodE goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_private_read goodE.live.hz goodA.live.hz buffersE storageAdvance
    (fun b owned => (stream_owned_deflate goodE b).mpr owned) ownedAdvance (stream_accounting_zero z') rfl
  have cast : emitted.strstart.toUInt64.toInt64.toInt = (emitted.strstart.toNat : Int) := by
    have bound := emitted.strstart.toNat_lt
    rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
    · simp
    · simp; omega
  have creditA : deferredCredit result = 1 := by
    unfold deferredCredit
    have availableA : result.match_available ≠ 0 := by change emitted.match_available ≠ 0; rw [frame]; exact available
    exact if_neg availableA
  have balanceA : BlockBalance result [] (deferredCredit result) := by
    rw [creditA]
    unfold BlockBalance
    change ((advanceOne emitted).strstart.toNat : Int) - emitted.block_start.toInt = _
    rw [positionE, cast, counts.1]
    change (↑(emitted.strstart.toNat + 1) : Int) - ↑emitted.strstart.toNat = ↑(represented []) + 1
    simp only [represented, Int.natCast_add, Int.natCast_one, Int.natCast_zero, Int.zero_add]
    omega
  obtain ⟨stateA, blockA, bufA, treesA⟩ := goodA.trees
  have resultEq : stateA = result := Option.some.inj (treesA.base.dstate.symm.trans goodA.live.hs)
  subst stateA
  have ledgerA : SymbolLedger bufA result [] := empty_symbol_ledger count frequenciesE
  have frameD : FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } emitted :=
    (FlushWorkFrame.block_start (show FlushWorkFrame d dt from rfl) d.strstart.toUInt64.toInt64).trans frame
  have frameA : FlushWorkFrame { advanceOne d with block_start := d.strstart.toUInt64.toInt64 } result := by
    unfold FlushWorkFrame at frameD ⊢
    dsimp only [result, advanceOne]
    rw [frameD]
  have configA : ConfigFrame d result := by rw [frameA]; rfl
  have lowA : result.bi_valid.toInt < 8 := phase.2.1
  have phaseA : 0 < z'.avail_out.toNat → PublishReady result := phase.2.2
  have outputPrefix : Zlib.Trees.Proofs.Out.outBits packed dt = Zlib.Trees.Proofs.Out.outBits buf d := by
    simp [Zlib.Trees.Proofs.Out.outBits, Zlib.Trees.Proofs.Out.bytesBits, dt, literalState, pending]
  have paddingEmpty := _padNone rfl
  rw [paddingEmpty, List.append_nil, outputPrefix] at _outputE
  have bytesA : Bytes after z.next_out produced written :=
    caller_bytes_setD_depth goodE.live.hs rfl _bytesE
  have pendingA : PendingBits after result remaining := by
    obtain ⟨pendingBytes, pendingData, bitsEqual⟩ := _pendingE
    exact ⟨pendingBytes, caller_bytes_setD_depth goodE.live.hs rfl pendingData, bitsEqual⟩
  have smallA : result.strstart.toNat < 65536 := by
    change (advanceOne emitted).strstart.toNat < 65536
    rw [counts.1, startE]
    omega
  have output : zrd (some r) (·.avail_out) after = .ok (z'.avail_out, after) := by
    simp only [zrd_eq, goodA.live.hz]
  refine ⟨produced, after, z', result, written, remaining, kind, body, ?_, goodA, buffersA, accountE, advanced.2.1, ?_, kept.1,
    ?_, ?_, ?_, count, ⟨clearE.bl, clearE.opt, clearE.fixed⟩,
    ⟨blockA, bufA, treesA, ledgerA, balanceA⟩, frameA, ?_, configA, lowA, phaseA,
    _cursorE, smallA, pending_bits_base trees cursor, bytesA, pendingA, _kindE, _outputE, _grammarE⟩
  · obtain ⟨size, _⟩ := window_extent good win get
    have fit : d.strstart.toNat - 1 < window.size := by dsimp only [fillEnd] at range; omega
    have read : index8 d.window (d.strstart - 1).toNat h = .ok (c, h) := by
      rw [win, u32_sub_one previousByte]
      simpa [OkOn, fit, c] using index8_ok (off := 0) (i := d.strstart.toNat - 1) get (by omega)
    unfold slowDecision
    have hasLiteral : (d.match_available != 0) = true := by simpa using available
    simp only [bind_app, ldDeflateState_tab good.live.hs, literalBranch, Bool.false_eq_true, ite_false,
      hasLiteral, ite_true, read, tally, emitRun0]
    change (do
      wr (some (.tab ds)) advanceOne
      if (← zrd d.strm (·.avail_out)) == 0 then
        return { st with hash_head, bflush := true, ret := some need_more }
      return { st with hash_head, bflush := true }) emittedHeap = _
    rw [bind_app, write]
    simp only [good.live.back, bind_app, output]
    by_cases fullOut : (z'.avail_out == 0) = true <;> simp [fullOut]
  · change emitted.window = .ref (.blk w) 0
    rw [frame]; exact win
  · rw [counts.1, startE]
  · rw [counts.2.1, lookEq]
  · change (advanceOne emitted).strstart.toNat + (advanceOne emitted).lookahead.toNat = _
    rw [counts.2.2, startE, lookEq]
    rfl
  · rw [counts.1, startE]
    have account0 : base + represented (xs ++ [emittedLiteral d window]) = origin + d.strstart.toNat := accountedT
    omega

end Zlib.Deflate.Engine.Proofs
