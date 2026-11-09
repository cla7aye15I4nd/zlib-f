import ZlibF.Proof.«deflate.c.engine.flush-block-prefix»
import ZlibF.Proof.«deflate.c.engine.short-literal-full-boundary»

/-! # The real deferred-literal half-step retains its independently decoded block -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual full deferred-literal half-step repays its byte, executes
the computed block and publication, then advances. Its composable parser
prefix and next absolute bit-position residue survive that actual advance.
All short input lengths and output capacities are covered; stored alignment
is derived rather than assumed for a later continuation. -/
theorem slow_literal_full_search_block_prefix {h : Heap} {r : ZStreamRef} {ds w ob oo origin base offset : Nat}
    {z : ZStream} {d : DeflateState} {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt < 8) (clear : BlockInit.BlockClear d)
    (position : offset % 8 = d.bi_valid.toInt.toNat % 8)
    (flush : Int32) (st : LoopS) (candidate : UInt32) :
    ∃ produced after z' result before written remaining kind body,
      slowDecision (some (.tab ds)) flush st candidate h =
        .ok ((if z'.avail_out == 0 then { st with hash_head := candidate, bflush := true, ret := some need_more }
          else { st with hash_head := candidate, bflush := true }), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented (xs ++ [emittedLiteral d wa])) [] ∧
      EndFrontier after result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      written.length = produced ∧ BlockInit.BlockClear result ∧ result.strstart.toNat = d.strstart.toNat + 1 ∧
      result.lookahead.toNat = d.lookahead.toNat - 1 ∧ fillEnd result = fillEnd d ∧
      result.sym_next.toNat < result.sym_end.toNat ∧ ConfigFrame d result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      kind < 3 ∧ ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
      BlockPrefix [] offset (inputPrefix input base)
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body)
        (inputPrefix input (base + represented (xs ++ [emittedLiteral d wa]))) ∧
      (offset + 3 + body.length) % 8 = result.bi_valid.toInt.toNat % 8 := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := cut.symbols
  have balance1 : BlockBalance d xs 1 := by simpa only [deferredCredit, available, ite_false] using balance
  have accounted : base + represented xs + 1 = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_false] using cut.accounted
  let c := wa[d.strstart.toNat - 1]!
  let dt := literalState d c
  let packed := literalBytes buf d c
  let ht := setD (Zlib.Trees.Proofs.Out.setB h pb packed) ds dt
  have room : d.sym_next.toNat + 3 ≤ d.sym_end.toNat := Nat.le_of_eq full
  have goodT : DGood ht r ds z dt := literal_good_after cut.good trees c room
  have treesT : TreesInvAt ht ds dt pb packed := tally_literal_trees trees c room
  have tallyFrame := pending_state_byte_frame h ds pb d dt packed trees.base.pbuf
  have tallyOwned := stream_owned_keys cut.good goodT rfl rfl rfl rfl
  have buffersT : StreamBuffers ht r := stream_buffers_private_read cut.good.live.hz goodT.live.hz buffers
    tallyFrame (fun b owned => (stream_owned_deflate cut.good b).mpr owned) tallyOwned (stream_accounting_zero z) rfl
  have getT : ht.bytes w = some wa := pending_window_frame cut.good cut.window trees.base.pbuf cut.bytes packed dt
  have ledgerT : SymbolLedger packed dt (xs ++ [emittedLiteral d wa]) := ledger_literal trees.base ledger room c
  have balanceT : BlockBalance dt (xs ++ [emittedLiteral d wa]) 0 := by
    simpa only [dt, c, emittedLiteral, show (1 : Int) - 1 = 0 from rfl] using balance_literal balance1 c
  have accountedT : base + represented (xs ++ [emittedLiteral d wa]) = origin + dt.strstart.toNat := by
    rw [represented_snoc, show (emittedLiteral d wa).bytes = 1 from rfl]
    exact accounted
  have meaning := literal_input_meaning cut.deferred available cut.view
  have oldEnd : base + represented xs = origin + d.strstart.toNat - 1 := by omega
  rw [← oldEnd] at meaning
  have traceT := cut.trace.snoc meaning
  have clearT : BlockInit.BlockClear dt := ⟨clear.bl, clear.opt, clear.fixed⟩
  have flag : (d.sym_next + 3 == d.sym_end) = true := by
    apply beq_iff_eq.mpr
    apply UInt32.toNat_inj.mp
    rw [← full]
    exact literal_count trees.base room c
  have tally : tally_lit (some (.tab ds)) c h = .ok (true, ht) := by
    simpa only [flag] using tally_literal_run trees.base c room
  obtain ⟨produced, emittedHeap, ze, emitted, written, remaining, kind, body, padding,
    emitRun, goodE, _buffersE, accountE, _sizesE, _storageE, _clearE, _frequenciesE, _positionE,
    _lowE, bytesE, pendingE, _drainedE, _finalE, storedE, kindE, _padBound, padNone, _storedPad,
    outputE, grammarE⟩ :=
    flush_block_only_publish_aligned goodT treesT buffersT positive pointer cursor memory pending (by change d.bi_valid.toInt ≤ 7; omega)
      ledgerT clearT traceT cut.window getT cut.range balanceT accountedT cut.view false
  have emitRun0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 ht = .ok ((), emittedHeap) := emitRun
  let result := advanceOne emitted
  let after := setD emittedHeap ds result
  have write : wr (some (.tab ds)) advanceOne emittedHeap = .ok ((), after) := by
    simp only [wrD_eq, goodE.live.hs, after, result]
  have output : zrd (some r) (·.avail_out) after = .ok (ze.avail_out, after) := by
    simp only [zrd_eq, after, ZStreamRef.get_setD, goodE.live.hz]
  have realRun : slowDecision (some (.tab ds)) flush st candidate h =
      .ok ((if ze.avail_out == 0 then { st with hash_head := candidate, bflush := true, ret := some need_more }
        else { st with hash_head := candidate, bflush := true }), after) := by
    obtain ⟨size, _⟩ := window_extent cut.good cut.window cut.bytes
    have fit : d.strstart.toNat - 1 < wa.size := by have := cut.range; dsimp only [fillEnd] at this; omega
    have read : index8 d.window (d.strstart - 1).toNat h = .ok (c, h) := by
      rw [cut.window, u32_sub_one (cut.deferred available)]
      simpa [OkOn, fit, c] using index8_ok (off := 0) (i := d.strstart.toNat - 1) cut.bytes (by omega)
    unfold slowDecision
    have hasLiteral : (d.match_available != 0) = true := by simpa using available
    simp only [bind_app, ldDeflateState_tab cut.good.live.hs, branch, Bool.false_eq_true, ite_false,
      hasLiteral, ite_true, read, tally, emitRun0]
    change (do
      wr (some (.tab ds)) advanceOne
      if (← zrd d.strm (·.avail_out)) == 0 then
        return { st with hash_head := candidate, bflush := true, ret := some need_more }
      return { st with hash_head := candidate, bflush := true }) emittedHeap = _
    rw [bind_app, write]
    simp only [cut.good.live.back, bind_app, output]
    by_cases fullOut : (ze.avail_out == 0) = true <;> simp [fullOut]
  obtain ⟨_otherCount, other, otherZ, otherD, otherRun, stateA, endA, buffersA,
    _accountA, clearA, startA, lookA, endpoint, strictA, configA, lowA, phaseA⟩ :=
    slow_literal_full_search_boundary cut buffers lookahead branch available full positive pointer cursor memory pending
      (by omega) clear flush st candidate
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans realRun))).2
  rw [heaps] at stateA endA buffersA
  have streams : otherZ = ze := Option.some.inj (stateA.good.live.hz.symm.trans (by
    simpa only [after, ZStreamRef.get_setD] using goodE.live.hz))
  have states : otherD = result := Option.some.inj (stateA.good.live.hs.symm.trans (setD_dstates_same _ _ _))
  rw [streams, states] at stateA
  rw [states] at endA clearA startA lookA endpoint strictA configA lowA
  rw [streams, states] at phaseA
  have bytesA : Bytes after z.next_out produced written := by
    rcases bytesE with ⟨null, _zero, _empty⟩ | ⟨ref, off, array, ptr, get, bound, value⟩
    · rw [pointer] at null; cases null
    · rw [pointer] at ptr
      obtain ⟨rfl, rfl⟩ := Ptr.ref.inj ptr
      exact Or.inr ⟨.blk ob, oo, array, pointer, get, bound, value⟩
  have pendingA : PendingBits after result remaining := by
    obtain ⟨_w, _p, _q, b, blocks⟩ := goodE.inv.blocks
    obtain ⟨data, getB, sizeB⟩ := blocks.ba
    obtain ⟨po, position, bound⟩ := blocks.pout
    rw [pending_bits_cursor_value position getB pendingE]
    exact pending_bits_slice (d := result) position getB (by rw [sizeB, ← blocks.psize]; exact bound)
  have beforeEq : Zlib.Trees.Proofs.Out.outBits packed dt = Zlib.Trees.Proofs.Out.outBits buf d := by
    simp [Zlib.Trees.Proofs.Out.outBits, Zlib.Trees.Proofs.Out.bytesBits, dt, literalState, pending]
  rw [beforeEq, padNone rfl, List.append_nil] at outputE
  have beforeA := pending_bits_base trees cursor
  have beforeLength := pending_bits_exact_length beforeA
  have afterLength := pending_bits_exact_length pendingA
  rw [pending] at beforeLength
  simp only [UInt64.toNat_zero, Nat.mul_zero, Nat.zero_add] at beforeLength
  have outputLength := congrArg List.length outputE
  simp only [List.length_append, encoded_bytes_length, Zlib.Trees.Proofs.Out.natBits_length] at outputLength
  have nextPosition : (offset + 3 + body.length) % 8 = result.bi_valid.toInt.toNat % 8 := by
    omega
  have storedR : kind = 0 → result.bi_valid.toInt.toNat = 0 := storedE
  have prefixA : BlockPrefix [] offset (inputPrefix input base)
      (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body)
      (inputPrefix input (base + represented (xs ++ [emittedLiteral d wa]))) :=
    nonfinal_block_prefix (by omega) (fun stored => by rw [nextPosition, storedR stored]) grammarE
  exact ⟨produced, after, ze, result, Zlib.Trees.Proofs.Out.outBits buf d, written, remaining, kind, body,
    realRun, stateA, endA, buffersA, accountE, public_bytes_length bytesA, clearA,
    startA, lookA, endpoint, strictA, configA, lowA, phaseA, pending_bits_base trees cursor,
    bytesA, pendingA, kindE, outputE, prefixA, nextPosition⟩

end Zlib.Deflate.Engine.Proofs
