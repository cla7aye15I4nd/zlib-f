import ZlibF.Proof.«deflate.c.engine.generic-foreign-header-buffered-joint-next»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-caller-input-frame»
import ZlibF.Proof.«deflate.c.engine.public-first-finish-one-encoding»
import ZlibF.Proof.«deflate.c.engine.valid-initial-entry»

/-! # The actual first one-byte PARTIAL call establishes header-pending encoding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The actual first one-byte output call publishes exactly the first
wrapper byte and retains exactly the second header byte. No raw input is
consumed. The initialized buffered boundary and explicit HeaderPending
phase are conclusions about that same public execution. -/
theorem public_foreign_first_partial_one_byte_encoding_adler {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {input : Nat → UInt8} {config : EngineConfig}
    (initial : EngineStart h r ds z d) (level : d.level = 6)
    (boundary : BufferedBoundary h r ds z d input 0 0 [] config) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (one : z.avail_out = 1)
    (valid : z.avail_in ≠ 0 → z.next_in ≠ .null)
    :
    ∃ after z' result,
      deflate (some r) Z_PARTIAL_FLUSH h = .ok (Z_OK, after) ∧
      BufferedBoundary after r ds z' result input 0 0 [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 1 ∧ Bytes after z.next_out 1 [120] ∧
      z'.avail_out = 0 ∧ result.status = BUSY_STATE ∧ result.last_flush = -1 ∧
      HeaderPending after result [120] ∧
      z'.adler = (ZlibF.Spec.adler32 (ZlibF.Math.DeflateSymbols.inputPrefix input (0 + fillEnd result))).toUInt64 := by
  have entry := public_default_valid_initial_entry initial
    (by rw [pointer];intro impossible;cases impossible)
    (by rw [one];decide) valid Z_PARTIAL_FLUSH (by decide) (by decide)
  obtain ⟨oldD,pb,buf,trees⟩ := initial.good.trees
  have sameD : oldD=d := Option.some.inj (trees.base.dstate.symm.trans initial.good.live.hs)
  subst oldD
  have boundary0:=last_flush_buffered_boundary boundary Z_PARTIAL_FLUSH
  have buffers0:=last_flush_buffers initial.good buffers Z_PARTIAL_FLUSH
  have trees0:=last_flush_trees trees Z_PARTIAL_FLUSH
  obtain ⟨produced,after,z',result,written,remaining,headerRun,stateA,_goodA,buffersA,accountA,
      _sizes,amount,count,statusA,bitsA,lastA,fieldsA,bytesA,pendingA,wireA,adlerA,_inA,_outA,_allocA,_nextA,_preciseA⟩ :=
    foreign_zlib_header_buffered_joint_next boundary0 trees0 buffers0 pointer initial.status initial.wrap initial.strategy
      initial.windowBits initial.start initial.pending initial.pendingOut (by rw [initial.bits];decide)
      (publicDataTail (some r) (some (.tab ds)) Z_PARTIAL_FLUSH)
  have amountOne : produced=1 := by
    rw [one] at amount
    change produced=min 2 1 at amount
    exact amount.trans (by decide)
  rw [amountOne] at accountA count bytesA
  have queued : result.pending≠0 := by
    intro zero
    rw [zero] at count
    change 0+1=2 at count
    omega
  have actual : deflate (some r) Z_PARTIAL_FLUSH h=.ok (Z_OK,after) := entry.trans (by simpa only [bne_iff_ne.mpr queued,ite_true] using headerRun)
  have outZero : z'.avail_out=0 := UInt32.toNat_inj.mp (by
    have balance:=accountA.2.2.2.1
    rw [one] at balance
    change z'.avail_out.toNat+1=1 at balance
    change z'.avail_out.toNat=0
    omega)
  have last : result.last_flush = -1 := by simpa only [bne_iff_ne.mpr queued,ite_true] using lastA
  have startA : result.strstart=0 := by rw [fieldsA];exact initial.start
  have lookA : result.lookahead=0 := by rw [fieldsA];exact initial.lookahead
  have bitsZero : result.bi_valid.toInt.toNat=0 := by rw [bitsA];rfl
  have originalPending:=pendingA
  obtain ⟨tailBytes,_tailData,remainingEq⟩ := originalPending
  have remainingBits : remaining=ZlibF.Spec.bytesToBits tailBytes := by
    simpa only [bitsA,Int.toNat_zero,List.range_zero,List.map_nil,List.append_nil] using remainingEq
  have header : levelHeaderPrefix d.level=[120,156] := by rw [level];decide
  have whole : written++tailBytes=[120,156] := by
    apply ZlibF.Math.DeflateEncoding.encoded_bytes_injective
    rw [remainingBits] at wireA
    simpa only [header,ZlibF.Spec.bytesToBits,List.flatMap_append] using wireA
  have length : written.length=1 := public_bytes_length bytesA
  have cut := congrArg (List.take written.length) whole
  rw [List.take_left,length] at cut
  have writtenEq : written=[120] := by simpa only [List.take_succ_cons,List.take_zero] using cut
  have headerPending : HeaderPending after result [120] :=
    ⟨tailBytes,remainingBits ▸ pendingA,by simpa only [writtenEq] using whole,bitsZero,startA,lookA⟩
  have checksum : z'.adler=(ZlibF.Spec.adler32 (ZlibF.Math.DeflateSymbols.inputPrefix input (0+fillEnd result))).toUInt64 := by
    simpa only [show (ZlibF.Spec.adler32 []).toUInt64=(1:UInt64) from by decide,fillEnd,startA,lookA,UInt32.toNat_zero,Nat.add_zero,ZlibF.Math.DeflateSymbols.inputPrefix,List.range_zero,List.map_nil] using adlerA
  rw [writtenEq] at bytesA
  exact ⟨after,z',result,actual,stateA,buffersA,accountA,bytesA,outZero,statusA,last,headerPending,checksum⟩

end Zlib.Deflate.Engine.Proofs
