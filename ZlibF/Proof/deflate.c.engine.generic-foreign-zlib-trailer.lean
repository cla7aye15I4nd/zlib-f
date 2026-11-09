import ZlibF.Proof.«deflate.c.engine.generic-wrapper-transfer»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-scalars»
import ZlibF.Proof.«deflate.c.engine.trailer-encoding»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The real zlib trailer writes, foreign pending copy and one-time wrapper
store share one execution and exact public output region. All capacities,
including zero and partial trailers, are admitted by this internal writer. -/
theorem foreign_zlib_trailer_publish_encoding {h : Heap} {r : ZStreamRef} {ds pb owner oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (wrap : d.wrap = 1)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) (bits : d.bi_valid.toInt = 0) :
    ∃ produced after z' result written remaining,
      publicFinishTail (some r) (some (.tab ds)) Z_FINISH h =
        .ok ((if result.pending != 0 then Z_OK else Z_STREAM_END), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ produced = min 4 z.avail_out.toNat ∧ result.pending.toNat + produced = 4 ∧
      result.wrap = -1 ∧ result.bi_valid.toInt = 0 ∧
      result = {d with pending := result.pending, pending_out := result.pending_out, wrap := -1} ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = ZlibF.Spec.bytesToBits (ZlibF.Spec.be32 z.adler.toNat) ∧
      z'.adler = z.adler ∧ z'.total_in = z.total_in ∧ z'.total_out = z.total_out + UInt64.ofNat produced ∧
      after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] ∧
      ∃ tailBytes, Bytes after result.pending_out result.pending.toNat tailBytes ∧
        written ++ tailBytes = ZlibF.Spec.be32 z.adler.toNat ∧
        (result.pending = 0 → written = ZlibF.Spec.be32 z.adler.toNat) := by
  let next := zlibTrailerBuffer buf z.adler
  let emitted : DeflateState := {d with pending := 4}
  let ready := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds emitted
  obtain ⟨write,goodE,treesE,buffersE,sizesE,storageE,values⟩ :=
    zlib_trailer_write (ob := pb) good trees buffers pending cursor
  obtain ⟨produced,middle,z',result,written,remaining,flush,goodM,buffersM,account,sizesM,
      amount,left,fields,bytesM,pendingM,outputM,frameM⟩ :=
    flush_pending_low_foreign_caller_bits_frame goodE treesE buffersE
      (by change d.bi_valid.toInt < 8; omega) cursor pointer
  obtain ⟨adlerM,inputM,outputCountM,allocM,frontierM⟩ :=
    flush_pending_low_foreign_run_scalar_effects goodE buffersE pointer
      (by change d.bi_valid.toInt < 8; omega) flush goodM.live.hz account
  have wrapM : result.wrap = 1 := by rw [fields]; exact wrap
  have bitsM : result.bi_valid.toInt = 0 := by rw [fields]; exact bits
  let final := setD middle ds {result with wrap := -1}
  have goodF := trailer_wrap_good goodM wrapM
  have sizesF := block_record_sizes (result := {result with wrap := -1}) goodM.live.hs rfl
  have buffersF := stream_buffers_sizes goodM.live.hz goodF.live.hz buffersM sizesF
    (stream_owned_keys goodM goodF rfl rfl rfl rfl) (stream_accounting_zero z')
  have bytesF := generic_wrapper_setD_bytes (result := {result with wrap := -1}) goodM.live.hs rfl bytesM
  have pendingF := generic_wrapper_setD_pending_bits (result := {result with wrap := -1})
    goodM.live.hs rfl rfl rfl rfl rfl pendingM
  have fieldsF : {result with wrap := -1} =
      {d with pending := result.pending, pending_out := result.pending_out, wrap := -1} := by rw [fields]
  have size : next.size = buf.size := by simp [next,zlibTrailerBuffer]
  have room : 4 ≤ next.size := by have extent := trees.base.size; have lo := trees.base.lit_lo; omega
  have word : Zlib.Trees.Proofs.Out.outBits next emitted =
      ZlibF.Spec.bytesToBits (ZlibF.Spec.be32 z.adler.toNat) := by
    unfold Zlib.Trees.Proofs.Out.outBits
    change Zlib.Trees.Proofs.Out.bytesBits next 4 ++
      Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat = _
    rw [bytes_bits_format next 4 room]
    change ZlibF.Spec.bytesToBits (next.toList.take 4) ++
      Zlib.Trees.Proofs.Out.natBits d.bi_buf.toNat d.bi_valid.toInt.toNat = _
    rw [values,zlib_trailer_word,bits]
    rfl
  have run : publicFinishTail (some r) (some (.tab ds)) Z_FINISH h =
      .ok ((if result.pending != 0 then Z_OK else Z_STREAM_END),final) := by
    have getW : rd (some (.tab ds)) (·.wrap) h = .ok (1,h) := by simp only [rdD_eq,good.live.hs,wrap]
    have getWM : rd (some (.tab ds)) (·.wrap) middle = .ok (1,middle) := by simp only [rdD_eq,goodM.live.hs,wrapM]
    have negative : ineg (1 : Int32) = pure (-1) := by rfl
    unfold publicFinishTail
    simp only [bind_app,pure_app,show (Z_FINISH != Z_FINISH) = false from rfl,
      Bool.false_eq_true,ite_false,getW,show ¬ (1 : Int32) ≤ 0 from by decide,
      show ((1 : Int32) == 2) = false from rfl,write,flush,getWM,
      show (1 : Int32) > 0 from by decide,ite_true,negative,wrD_eq,goodM.live.hs]
    simp only [bind_app,pure_app,rdD_eq,setD_dstates_same]
    rfl
  have wire := outputM.trans word
  have privateFrame := storageE.pending_private_frame trees.base.pbuf
  have frameM' : BufferFrame ready middle (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
    refine ⟨full_frame_weaken frameM.1 ?_,frameM.2⟩
    intro b changed
    exact changed.elim Or.inl (fun same => Or.inr (Or.inl same))
  have initialFrame : BufferFrame h middle (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
    rw [pointer] at frameM' ⊢
    exact generic_wrapper_foreign_private_prefix privateFrame
      (generic_zlib_trailer_ready_foreign_view good.live.hs) frameM'
  obtain ⟨beforeForeign,beforeGet,_beforeBound,different,_old,_notRoot⟩ := caller_foreign_output good buffers pointer
  have pointerM : z'.next_out = .ref (.dstate_depth owner) (oo + produced) := by
    rw [account.2.2.2.2.2.1,pointer]
    rfl
  obtain ⟨middleForeign,middleGet,_middleBound,_different,_oldM,_rootM⟩ := caller_foreign_output goodM buffersM pointerM
  have frameF : BufferFrame h final (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
    rw [pointer] at initialFrame ⊢
    exact generic_wrapper_foreign_setD_frame goodM.live.hs beforeGet middleGet different (Or.inr (Or.inl rfl)) rfl initialFrame
  obtain ⟨tailBytes,tailData,tailEq⟩ := pendingF
  have remainingEq : remaining = ZlibF.Spec.bytesToBits tailBytes := by
    simpa only [bitsM,Int.toNat_zero,List.range_zero,List.map_nil,List.append_nil] using tailEq
  have splitBytes : written ++ tailBytes = ZlibF.Spec.be32 z.adler.toNat := by
    apply ZlibF.Math.DeflateEncoding.encoded_bytes_injective
    simpa only [ZlibF.Spec.bytesToBits,List.flatMap_append,remainingEq] using wire
  have completed : result.pending = 0 → written = ZlibF.Spec.be32 z.adler.toNat := by
    intro empty
    have length := caller_bytes_length tailData
    have nil : tailBytes = [] := List.eq_nil_iff_length_eq_zero.mpr (by simpa only [empty,UInt64.toNat_zero] using length)
    simpa only [nil,List.append_nil] using splitBytes
  refine ⟨produced,final,z',{result with wrap := -1},written,remaining,run,goodF,buffersF,account,
    (sizesE.trans sizesM).trans sizesF,amount,left,rfl,bitsM,fieldsF,bytesF,?_,wire,adlerM,inputM,outputCountM,
    ?_,?_,frameF,tailBytes,tailData,splitBytes,completed⟩
  · exact ⟨tailBytes,tailData,tailEq⟩
  · simpa only [final,setD_nalloc] using allocM.trans storageE.nalloc
  · simpa only [final,setD_nextBlk] using frontierM.trans storageE.nextBlk

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.foreign_zlib_trailer_publish_encoding
