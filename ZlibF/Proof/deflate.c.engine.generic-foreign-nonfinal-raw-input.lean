import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-stream-input»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-nonfinal-call»
import ZlibF.Proof.«deflate.c.engine.nonfinal-raw-input»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete actual nonzero non-FINISH strategy advances RawPrefix
and Adler for the same consumed original caller input, including EOF and
short-output returns. This is the representation used by actual default
histories. Public marker emission and entry guards are separate. -/
theorem default_foreign_deflate_slow_nonfinal_ready_raw_prefix_input {h : Heap} {r : ZStreamRef}
    {ds owner oo origin base : Nat} {z : ZStream} {d : DeflateState}
    {xs : List Symbol} {input : Nat → UInt8} {config : EngineConfig} {published : List UInt8}
    (boundary : StrategyBoundary h r ds z d input origin base xs config)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r)
    (positive : 0 < config.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo)
    (memory : config.memory.toNat = 16384) (wrap : config.wrap = 1)
    (publish : PublishReady d) (inputValid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    (flush : Int32) (nonzero : flush ≠ Z_NO_FLUSH) (nonfinal : flush ≠ Z_FINISH)
    {actualInput : List UInt8} (snapshot : Bytes h z.next_in z.avail_in.toNat actualInput)
    (checksum : z.adler = (ZlibF.Spec.adler32 (inputPrefix input (origin + fillEnd d))).toUInt64)
    (encoding : RawPrefix h d input base published) :
    ∃ used rc after z' result extended nextOrigin base' ys written,
      deflate_slow (some (.tab ds)) flush h = .ok (rc, after) ∧
      StrategyBoundary after r ds z' result extended nextOrigin base' ys config ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' used written.length ∧
      Bytes after z.next_out written.length written ∧
      (∀ i, i < origin + fillEnd d → extended i = input i) ∧
      nextOrigin + fillEnd result = origin + fillEnd d + used ∧ base ≤ base' ∧
      RawPrefix after result extended base' (published ++ written) ∧
      z'.adler = (ZlibF.Spec.adler32 (inputPrefix extended (nextOrigin + fillEnd result))).toUInt64 ∧
      inputPrefix extended (nextOrigin + fillEnd result) =
        inputPrefix input (origin + fillEnd d) ++ actualInput.take used ∧
      ((rc = need_more ∧ z'.avail_out = 0) ∨
       (rc = block_done ∧ z'.avail_in = 0 ∧ result.lookahead = 0 ∧ result.sym_next = 0)) ∧
      Shape h after ∧ BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,written.length⟩] ∧
      StrategyControls d result ∧ (rc=block_done → PublishReady result ∧ result.match_available=0) := by
  obtain ⟨before, completed, held, wire, meaning⟩ := encoding
  obtain ⟨used, rc, after, z', result, extended, nextOrigin, base', ys, written,
      remaining, encoded, run, stateA, endA, buffersA, accountA, bytesA,
      agreesA, endpointA, baseA, pendingA, wireA, meaningA, _positionA, checksumA, inputLedgerA, returnsA,shapeA,preciseA⟩ :=
    default_foreign_deflate_slow_nonfinal_ready_stream_input boundary frontier buffers positive pointer memory wrap publish inputValid
      flush nonzero nonfinal snapshot checksum held wire meaning
  obtain ⟨_used,_produced,otherRet,otherHeap,_otherZ,otherD,_base,_ys,_input,_origin,
      tested,stateOther,_endOther,_buffersOther,_accountOther,_agrees,_endpoint,_baseLe,_classification,controls,doneReady⟩ :=
    default_foreign_deflate_slow_positive_nonfinal_ready boundary frontier buffers positive pointer memory wrap publish inputValid
      flush nonzero nonfinal
  obtain ⟨retEq,heapEq⟩ := Prod.mk.inj (Except.ok.inj (tested.symm.trans run))
  subst otherRet otherHeap
  have states : otherD=result := Option.some.inj (stateOther.good.live.hs.symm.trans stateA.good.live.hs)
  rw [states] at controls doneReady
  exact ⟨used, rc, after, z', result, extended, nextOrigin, base', ys, written,
    run, stateA, endA, buffersA, accountA, bytesA, agreesA, endpointA, baseA,
    ⟨remaining, encoded, pendingA, wireA, meaningA⟩, checksumA, inputLedgerA, returnsA,shapeA,preciseA,controls,doneReady⟩

end Zlib.Deflate.Engine.Proofs
