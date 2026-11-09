import ZlibF.Proof.«deflate.c.engine.generic-foreign-sync-marker»
import ZlibF.Proof.«deflate.c.engine.marker-raw-prefix»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
open Zlib.Trees.Proofs.Out (TreesInvAt outBits natBits)
set_option autoImplicit false

/-- The same real SYNC marker publication extends independent cumulative raw meaning,
retaining checksum, exact input endpoint, counters and its complete caller byte frame. -/
theorem foreign_sync_marker_joint_raw_prefix {h : Heap} {r : ZStreamRef} {ds pb owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (publish : PublishReady d)
    (encoding : RawPrefix h d input base published) :
    ∃ produced after z' result written,
      (do Zlib.Trees.«_tr_stored_block» (some (.tab ds)) .null 0 0;flush_pending (some r)) h=.ok ((),after) ∧
      BufferedBoundary after r ds z' result input origin base [] config ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ Bytes after z.next_out produced written ∧
      RawPrefix after result input base (published++written) ∧ ConfigFrame d result ∧
      result.status=d.status ∧ result.last_flush=d.last_flush ∧ (0<z'.avail_out.toNat → PublishReady result) ∧
      z'.adler=z.adler ∧ fillEnd result=fillEnd d ∧ result.match_available=d.match_available ∧
      z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb owner ∧
      BufferFrame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b) [⟨z.next_out,produced⟩] := by
  obtain ⟨before,encoded,held,wire,meaning⟩ := encoding
  have initial := pending_bits_base trees publish.2.1
  have beforeEq : outBits buf d=before :=
    (pending_bits_zero_value publish.1 initial).trans (pending_bits_zero_value publish.1 held).symm
  obtain ⟨produced,after,z',result,written,remaining,run,stateA,buffersA,accountA,sizes,storage,
      configA,statusA,lastA,readyA,bytesA,pendingA,wireA,adlerA,inputA,outputA,endpointA,availableA,precise⟩ :=
    foreign_empty_sync_publish boundary buffers trees pointer publish
  rw [beforeEq] at wireA
  have position : encoded.length%8=d.bi_valid.toInt.toNat%8 := by
    have count:=congrArg List.length wire
    have pendingLength:=pending_bits_exact_length held
    rw [publish.1] at pendingLength
    simp only [List.length_append,encoded_bytes_length] at count
    simp only [UInt64.toNat_zero,Nat.mul_zero,Nat.zero_add] at pendingLength
    omega
  let marker := Zlib.Trees.Proofs.Out.storedHeaderBits d 0 false
  have markerPrefix : BlockPrefix [] (0+encoded.length) (inputPrefix input base) marker (inputPrefix input base) := by
    simpa only [marker,Nat.zero_add] using stored_header_zero_block_prefix d position (inputPrefix input base)
  have allWire : ZlibF.Spec.bytesToBits (published++written)++remaining=encoded++marker := by
    calc
      _ = ZlibF.Spec.bytesToBits published++(ZlibF.Spec.bytesToBits written++remaining) := by
        simp only [ZlibF.Spec.bytesToBits,List.flatMap_append,List.append_assoc]
      _ = ZlibF.Spec.bytesToBits published++(before++marker) := by rw [wireA]
      _ = (ZlibF.Spec.bytesToBits published++before)++marker := (List.append_assoc _ _ _).symm
      _ = encoded++marker := by rw [wire]
  exact ⟨produced,after,z',result,written,run,stateA,buffersA,accountA,bytesA,
    ⟨remaining,encoded++marker,pendingA,allWire,block_prefix_append meaning markerPrefix⟩,
    configA,statusA,lastA,readyA,adlerA,endpointA,availableA,inputA,outputA,sizes,storage,precise⟩

end Zlib.Deflate.Engine.Proofs
