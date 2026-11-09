import ZlibF.Proof.«deflate.c.engine.generic-foreign-partial-publication»
import ZlibF.Proof.«deflate.c.engine.marker-raw-prefix»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols ZlibF.Math.DeflateEncoding
open Zlib.Trees.Proofs.Out (TreesInvAt outBits natBits)
set_option autoImplicit false

/-- The same real PARTIAL marker publication extends independent cumulative raw meaning,
retaining checksum, exact input endpoint, counters and its complete caller byte frame. -/
theorem empty_foreign_partial_publish_raw_prefix {h : Heap} {r : ZStreamRef} {ds pb owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    {published : List UInt8}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (buffers : StreamBuffers h r) (trees : TreesInvAt h ds d pb buf)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (publish : PublishReady d)
    (encoding : RawPrefix h d input base published) :
    ∃ produced after z' result written,
      (do Zlib.Trees.«_tr_align» (some (.tab ds));flush_pending (some r)) h=.ok ((),after) ∧
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
    empty_foreign_partial_publish boundary buffers trees pointer publish
  rw [beforeEq] at wireA
  let marker := natBits 2 3++(natBits 0 7++[])
  have markerPrefix : BlockPrefix [] (0+encoded.length) (inputPrefix input base) marker (inputPrefix input base) := by
    simpa only [marker,List.append_nil,Nat.zero_add] using partial_marker_block_prefix encoded.length (inputPrefix input base)
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
