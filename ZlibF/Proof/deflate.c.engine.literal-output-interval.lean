import ZlibF.Proof.«deflate.c.engine.output-interval»
import ZlibF.Proof.«deflate.c.engine.literal-decision-full-storage»

/-! # Exact raw caller output intervals through actual strategy execution -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A full literal publication followed by input-position advance preserves the exact accounted output interval. -/
theorem slow_literal_full_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds w ob oo origin base produced : Nat} {z zr : ZStream} {d : DeflateState}
    {wa : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    {flush : Int32} {st next : LoopS} {candidate : UInt32}
    (cut : SearchBoundary h r ds z d input origin base xs w wa)
    (buffers : StreamBuffers h r) (lookahead : 1 ≤ d.lookahead.toNat)
    (branch : (d.prev_length ≥ MIN_MATCH_u && d.match_length ≤ d.prev_length) = false)
    (available : d.match_available ≠ 0) (full : d.sym_next.toNat + 3 = d.sym_end.toNat)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo)
    (memory : d.lit_bufsize.toNat = 16384) (ready : PublishReady d) (clear : BlockInit.BlockClear d)
    (run : slowDecision (some (.tab ds)) flush st candidate h = .ok (next, after))
    (live : r.get after = some zr) (account : StreamAccounting z zr 0 produced) :
    RawOutputInterval h after ob oo produced := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := cut.symbols
  have previousByte := cut.deferred available
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
  have bitsT : dt.bi_valid.toInt ≤ 7 := by
    change d.bi_valid.toInt ≤ 7
    have low := ready.2.2
    omega
  obtain ⟨amount, emittedHeap, z', emitted, _written, _remaining, _kind, _body, _padding,
      emitRun, goodE, _buffersE, accountE, _sizesE, storageE, _rest⟩ :=
    flush_block_only_publish goodT treesT buffersT positive pointer ready.2.1 memory ready.1
      bitsT ledgerT clearT traceT
      cut.window getT cut.range balanceT accountedT cut.view false
  have emitRun0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 ht = .ok ((), emittedHeap) := emitRun
  let finalD := advanceOne emitted
  let finalHeap := setD emittedHeap ds finalD
  have write : wr (some (.tab ds)) advanceOne emittedHeap = .ok ((), finalHeap) := by
    simp only [wrD_eq, goodE.live.hs, finalHeap, finalD]
  have output : zrd (some r) (·.avail_out) finalHeap = .ok (z'.avail_out, finalHeap) := by
    simp only [zrd_eq, finalHeap, ZStreamRef.get_setD, goodE.live.hz]
  have actualRun : slowDecision (some (.tab ds)) flush st candidate h =
      .ok ((if z'.avail_out == 0 then { st with hash_head := candidate, bflush := true, ret := some need_more }
        else { st with hash_head := candidate, bflush := true }), finalHeap) := by
    obtain ⟨size, _⟩ := window_extent cut.good cut.window cut.bytes
    have fit : d.strstart.toNat - 1 < wa.size := by have range := cut.range; dsimp only [fillEnd] at range; omega
    have read : index8 d.window (d.strstart - 1).toNat h = .ok (c, h) := by
      rw [cut.window, u32_sub_one previousByte]
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
    by_cases fullOut : (z'.avail_out == 0) = true <;> simp [fullOut]
  have eq := (Prod.mk.inj (Except.ok.inj (actualRun.symm.trans run))).2
  have finalLive : r.get finalHeap = some z' := by
    simpa only [finalHeap, ZStreamRef.get_setD] using goodE.live.hz
  rw [eq] at finalLive
  have sameZ : z' = zr := Option.some.inj (finalLive.symm.trans live)
  have count : amount = produced := (stream_accounting_counts_unique
    (by simpa only [sameZ] using accountE) account).2
  have tallyStorage : OutputStorage h ht r ds pb pb := output_bits_storage cut.good.live.hs trees.base.bytes
  have tallyEffect : RawOutputInterval h ht ob oo 0 :=
    .of_private_frame cut.good buffers pointer (tallyStorage.pending_private_frame trees.base.pbuf)
  have emitEffect := flush_macro_run_output_effect goodT treesT buffersT positive pointer ready.2.1 memory ready.1
    bitsT ledgerT clearT traceT cut.window getT cut.range balanceT accountedT cut.view false emitRun goodE.live.hz accountE
  have joinedEffect : RawOutputInterval h emittedHeap ob oo amount := by
    simpa only [Nat.zero_add] using tallyEffect.trans emitEffect
  have tailEffect : RawOutputInterval emittedHeap finalHeap ob (oo + amount) 0 := .of_same rfl
  rw [← eq, ← count]
  simpa only [Nat.add_zero] using joinedEffect.trans tailEffect

end Zlib.Deflate.Engine.Proofs
