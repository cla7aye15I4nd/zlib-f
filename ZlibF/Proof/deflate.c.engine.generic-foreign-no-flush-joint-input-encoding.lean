import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-input-ledger»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-no-flush-ready-call»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-ordinary-physical»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-logical-checksum»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-loop-controls»
import ZlibF.Proof.«deflate.c.engine.buffered-boundary»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
set_option autoImplicit false

/-- The real prepared NO_FLUSH call terminates and jointly retains its independent
block history, exact final-heap output and Adler meaning for one shared returned input.
All caller capacities, including zero, are admitted through explicit publication readiness. -/
theorem default_foreign_deflate_slow_no_flush_joint_input_encoding {h : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig}
    {before completed : List Bool} {previous : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0<config.level.toInt) (pointer : z.next_out=.ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat=16384) (wrap : config.wrap=1) (publish : PublishReady d)
    (inputValid : z.avail_in≠0 → z.next_in≠.null)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (held : PendingBits h d before)
    (wirePrefix : ZlibF.Spec.bytesToBits previous ++ before=completed)
    (prefixMeaning : BlockPrefix [] 0 [] completed (inputPrefix input base))
    (checksum : z.adler=(ZlibF.Spec.adler32 (inputPrefix input (origin+fillEnd d))).toUInt64) :
    ∃ used after z' result extended nextOrigin base' ys written remaining encoded,
      deflate_slow (some (.tab ds)) Z_NO_FLUSH h=.ok (need_more,after) ∧
      BufferedBoundary after r ds z' result extended nextOrigin base' ys config ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i<origin+fillEnd d → extended i=input i) ∧
      nextOrigin+fillEnd result=origin+fillEnd d+used ∧ base≤base' ∧
      PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits (previous++written) ++ remaining=encoded ∧
      BlockPrefix [] 0 [] encoded (inputPrefix extended base') ∧
      encoded.length%8=result.bi_valid.toInt.toNat%8 ∧
      z'.adler=(ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin+fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin+fillEnd result)=inputPrefix input (origin+fillEnd d)++actualInput.take used := by
  obtain ⟨_used,_produced,after,_z',_result,_base',_ys,_extended,_nextOrigin,call,_rest⟩ :=
    default_foreign_deflate_slow_no_flush_ready boundary frontier buffers positive pointer memory wrap publish inputValid
  have loopExists : ∃ final, cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h=.ok (final,after) := by
    have source:=call
    rw [deflate_slow_eof_tail_source] at source
    cases loop : cwhile forever (deflate_slow_body (some (.tab ds)) Z_NO_FLUSH) {} h with
    | error fault => simp only [bind_app,loop] at source;cases source
    | ok pair =>
      obtain ⟨final,middle⟩:=pair
      have returned:=default_foreign_slow_no_flush_ready_loop_run_control boundary frontier buffers positive pointer memory wrap publish inputValid loop
      simp only [bind_app,loop,returned,pure_app] at source
      have heaps : middle=after := (Prod.mk.inj (Except.ok.inj source)).2
      exact ⟨final,by simp only [heaps]⟩
  obtain ⟨final,loop⟩:=loopExists
  have position : completed.length%8=d.bi_valid.toInt.toNat%8 := by
    have count:=congrArg List.length wirePrefix
    have pendingLength:=pending_bits_exact_length held
    simp only [List.length_append,encoded_bytes_length] at count
    omega
  obtain ⟨used,z',result,extended,nextOrigin,base',ys,beforeL,written,remaining,blockBits,
    stateA,endA,buffersA,accountA,agreesA,endpointA,baseA,pendingBefore,bytesA,pendingA,
    wireA,prefixA,positionA,checksumA,inputLedgerA⟩ :=
    default_foreign_slow_loop_run_block_prefix_input (offset:=completed.length) boundary frontier buffers positive pointer memory wrap publish inputValid snapshot checksum position loop
  have controls:=default_foreign_slow_loop_run_controls boundary frontier buffers positive pointer memory wrap publish inputValid loop stateA.good.live.hs
  have beforeEq : beforeL=before :=
    (pending_bits_zero_value publish.1 pendingBefore).trans (pending_bits_zero_value publish.1 held).symm
  rw [beforeEq] at wireA
  have wire : ZlibF.Spec.bytesToBits (previous++written) ++ remaining=completed++blockBits := by
    simp only [ZlibF.Spec.bytesToBits,List.flatMap_append,List.append_assoc] at wireA wirePrefix ⊢
    rw [wireA,← List.append_assoc,wirePrefix]
  have stepMeaning : BlockPrefix [] (0+completed.length) (inputPrefix input base) blockBits (inputPrefix extended base') := by
    simpa only [Nat.zero_add] using prefixA
  exact ⟨used,after,z',result,extended,nextOrigin,base',ys,written,remaining,completed++blockBits,
    call,stateA.buffered endA controls.empty_cursor,buffersA,accountA,bytesA,agreesA,endpointA,baseA,
    pendingA,wire,block_prefix_append prefixMeaning stepMeaning,
    by simpa only [List.length_append] using positionA,checksumA,inputLedgerA⟩

end Zlib.Deflate.Engine.Proofs
