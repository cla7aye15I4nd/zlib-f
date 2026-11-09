import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-content»
import ZlibF.Proof.«deflate.c.engine.finish-tail-encoding»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual final-block tail with foreign-depth output retains complete final wire and byte frame. -/
theorem default_foreign_finish_tail_final_content_encoding {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (wrap : d.wrap = 1) :
    ∃ produced after z' result before written remaining kind body padding,
      finish_tail (some (.tab ds)) Z_FINISH h =
        .ok ((if z'.avail_out == 0 then finish_started else finish_done), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt.toNat = 0 ∧ PendingBits h d before ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      kind < 3 ∧ padding.length < 8 ∧ (kind = 0 → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 1 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body ++ padding) ∧
      (∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs))) ∧
      result.bi_valid.toInt<8 ∧ (0<z'.avail_out.toNat → PublishReady result) ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨produced,after,z',result,before,written,remaining,kind,body,padding,
    run,stateA,_endA,buffersA,accountA,clearA,frameA,lowA,phaseA,_cursorA,pendingBefore,bytesA,pendingA,
    kindA,padBound,_padNone,storedPad,wire,grammar⟩ :=
    default_foreign_flush_macro_content_encoding boundary frontier buffers positive pointer cursor memory pending bits clear available true
  obtain ⟨pb,buf,trees,ledger,balance⟩ := boundary.symbols
  obtain ⟨w,window,win,get,view,_form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit,available,ite_true] using balance
  have accounted0 : base+represented xs=origin+d.strstart.toNat := by
    simpa only [pendingCredit,available,ite_true,Nat.add_zero] using boundary.accounted
  obtain ⟨amount,other,otherZ,otherD,_written,_remaining,_kind,_body,_padding,
    otherRun,otherGood,_otherBuffers,otherAccount,_sizes,_storage,_fields,_low,final,
    _clear,_count,_frequencies,_cursor,_phase,_position,_bytes,_pending,bufferFrame,_rest⟩ :=
    default_flush_block_only_foreign_publish boundary.good trees buffers positive pointer cursor memory pending bits
      ledger clear boundary.trace win get boundary.range balance0 accounted0 view true
  have heaps : other=after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heaps] at otherGood bufferFrame
  have streams : otherZ=z' := Option.some.inj (otherGood.live.hz.symm.trans stateA.good.live.hz)
  have states : otherD=result := Option.some.inj (otherGood.live.hs.symm.trans stateA.good.live.hs)
  rw [streams] at otherAccount
  have counts : amount=produced := (stream_accounting_counts_unique otherAccount accountA).2
  rw [counts] at bufferFrame
  have finalA : result.bi_valid.toInt.toNat=0 := by rw [← states];exact final rfl
  have run1 : FLUSH_BLOCK_ONLY (some (.tab ds)) 1 h=.ok ((),after) := run
  have wrapA : result.wrap=1 := by rw [frameA];exact wrap
  have macroRun : FLUSH_BLOCK (some (.tab ds)) 1 h=
      .ok ((if z'.avail_out==0 then some finish_started else none),after) := by
    unfold FLUSH_BLOCK
    simp only [bind_app,run1,ldDeflateState_tab stateA.good.live.hs,stateA.good.live.back,zrd_eq,stateA.good.live.hz]
    by_cases empty : (z'.avail_out==0)=true <;> simp [empty,pure_app,wrapA]
  refine ⟨produced,after,z',result,before,written,remaining,kind,body,padding,?_,stateA,buffersA,accountA,
    clearA,frameA,finalA,pendingBefore,bytesA,pendingA,kindA,padBound,storedPad,wire,grammar,lowA,phaseA,bufferFrame⟩
  unfold finish_tail
  simp only [beq_self_eq_true,ite_true,bind_app,macroRun]
  by_cases empty : (z'.avail_out==0)=true <;> simp [empty,pure_app]

end Zlib.Deflate.Engine.Proofs
