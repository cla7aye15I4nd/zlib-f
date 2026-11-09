import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-contract»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The public caller-buffer relation supplies the foreign object, capacity and private separation. -/
theorem caller_foreign_output {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) :
    ∃ foreign, h.dstates owner = some foreign ∧ oo + z.avail_out.toNat ≤ foreign.depth.size ∧
      owner ≠ ds ∧ owner < h.nextBlk ∧ ¬ StreamRoot r owner := by
  obtain ⟨z0,hz0,input,output,separate⟩ := buffers
  have same : z0 = z := Option.some.inj (hz0.symm.trans good.live.hz)
  subst z0
  rw [pointer] at output
  have different := foreign_depth_owner_not_private good output
  rcases output with impossible | ⟨⟨xs,data⟩,writable,outside⟩
  · cases impossible
  · rcases data with ⟨impossible,_,_⟩ | ⟨ref,off,array,ptr,get,bound,value⟩
    · cases impossible
    · obtain ⟨sameRef,sameOff⟩ := Ptr.ref.inj ptr
      subst ref off
      cases state : h.dstates owner with
      | none => simp [Space.get,state] at get
      | some foreign =>
        have equal : array = foreign.depth := Option.some.inj (get.symm.trans (BRef.get_dstate_depth state))
        refine ⟨foreign,rfl,by simpa only [equal] using bound,different,
          foreign_depth_owner_before_frontier good.fresh state,?_⟩
        exact caller_byte_root_not_stream (off := oo) good get rfl

/-- Publicly legal foreign-depth output has an actual publication producer.
All separation, bounds and ownership facts follow from StreamBuffers. The only phase
requirements are the explicit low-bit, pending-base publishing representation. -/
theorem flush_pending_low_foreign_caller_bits_frame {h : Heap} {r : ZStreamRef} {ds pb owner oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (low : d.bi_valid.toInt < 8) (cursor : d.pending_out = d.pending_buf)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) :
    ∃ produced after z' result written remaining,
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧ result.pending.toNat + produced = d.pending.toNat ∧
      result = { d with pending := result.pending, pending_out := result.pending_out } ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ∧
      BufferFrame h after (fun x => StreamRoot r x ∨ x = ds) [⟨z.next_out,produced⟩] := by
  obtain ⟨foreign,get,bound,different,_,_⟩ := caller_foreign_output good buffers pointer
  obtain ⟨produced,after,z',result,written,remaining,run,goodA,account,sizes,count,pendingCount,fields,bytes,pending,bits,frame⟩ :=
    flush_pending_low_foreign_bits_frame good trees low cursor pointer get different bound
  have owned : ∀ b, StreamOwned after r b ↔ StreamOwned h r b := by
    intro b
    rw [stream_owned_deflate goodA,stream_owned_deflate good,fields]
    rfl
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned account
  exact ⟨produced,after,z',result,written,remaining,run,goodA,buffersA,account,sizes,count,pendingCount,fields,bytes,pending,bits,frame⟩

end Zlib.Deflate.Engine.Proofs
