import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-cursor»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-storage»
import ZlibF.Proof.«deflate.c.engine.pending-resume»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual lossless foreign-depth publication at an advanced pending cursor; all capacities. -/
theorem flush_pending_resume_foreign_bits {h : Heap} {r : ZStreamRef} {ds owner oo : Nat}
    {z : ZStream} {d : DeflateState} {before : List Bool}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (low : d.bi_valid.toInt < 8)
    (pending : PendingBits h d before) :
    ∃ pb produced after z' result written remaining,
      d.pending_buf = .ref (.blk pb) 0 ∧
      flush_pending (some r) h = .ok ((), after) ∧ DGood after r ds z' result ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 produced ∧ ByteSizes h after ∧ OutputStorage h after r ds pb owner ∧
      produced = min d.pending.toNat z.avail_out.toNat ∧ result.pending.toNat + produced = d.pending.toNat ∧
      result.bi_valid.toInt < 8 ∧
      result = { d with pending := result.pending, pending_out := result.pending_out } ∧
      (0 < produced → result.pending.toNat = 0 → result.pending_out = result.pending_buf) ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ∧
      BufferFrame h after (fun x => StreamRoot r x ∨ x=ds) [⟨z.next_out,produced⟩] := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨po, cursor, bound⟩ := blocks.pout
  have sourceBound : po + d.pending.toNat ≤ buf.size := by rw [size, ← blocks.psize]; exact bound
  obtain ⟨foreign,outGet,outBound,different,_,_⟩ := caller_foreign_output good buffers pointer
  let n := pendingLen d.pending z.avail_out
  have count : n.toNat = min d.pending.toNat z.avail_out.toNat := pendingLen_value _ _
  by_cases empty : n = 0
  · have run := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low empty
    refine ⟨pb, 0, h, z, d, [], before, blocks.pbuf, run, good, buffers, stream_accounting_zero z,
      ⟨fun _ _ read => ⟨_, read, rfl⟩, fun _ => rfl⟩, OutputStorage.refl h r ds pb owner,
      ?_, by omega, low, rfl, (by omega), ?_, pending, rfl, ?_⟩
    · rw [empty] at count
      exact count
    · exact Or.inr ⟨.dstate_depth owner, oo, foreign.depth, pointer, BRef.get_dstate_depth outGet, by omega, by simp⟩
    · have frame0 := foreign_depth_copy_buffer_frame (off := oo) (sourceOff := po) (n := 0) outGet buf (by omega)
      have self : setD h owner {foreign with depth := copyRange foreign.depth buf oo po 0}=h := by
        change setD h owner foreign=h
        exact setD_self outGet
      rw [self] at frame0
      refine ⟨?_,by simpa only [pointer] using frame0.2⟩
      exact full_frame_weaken (by simpa only [pointer] using frame0.1) (fun _ impossible => False.elim (by simpa using impossible))
  · have run := flush_pending_low_foreign good.live.hz good.live.zst good.live.hs low pointer cursor
      outGet get (Ne.symm different) outBound sourceBound empty
    obtain ⟨written, remaining, bytes, pendingA, bits⟩ :=
      foreign_pending_copy_cursor_bits (r := r) (ds := ds) blocks.pbuf cursor get sourceBound pending pointer different outBound
    have goodA := foreign_pending_copy_good (pending := buf) (oo := oo) good blocks.pbuf cursor outGet (Ne.symm different)
    have sizes := foreign_pending_copy_sizes (r := r) (z := z) (pb := pb) (po := po) (pending := buf) (oo := oo) n good.live.hs outGet (Ne.symm different)
    have account := foreign_pending_copy_accounting (d := d) pointer
    have fields : pendingState d (.ref (.blk pb) (po + n.toNat)) n =
        { d with
          pending := (pendingState d (.ref (.blk pb) (po + n.toNat)) n).pending,
          pending_out := (pendingState d (.ref (.blk pb) (po + n.toNat)) n).pending_out } := rfl
    have owned : ∀ b, StreamOwned (foreignPendingCopyHeap h r ds pb po owner oo z d buf foreign n) r b ↔ StreamOwned h r b := by
      intro b
      rw [stream_owned_deflate goodA, stream_owned_deflate good]
      rfl
    have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned account
    refine ⟨pb, n.toNat, foreignPendingCopyHeap h r ds pb po owner oo z d buf foreign n,
      pendingStream z (.ref (.dstate_depth owner) (oo + n.toNat)) n,
      pendingState d (.ref (.blk pb) (po + n.toNat)) n, written, remaining,
      blocks.pbuf, run, goodA, buffersA, account, sizes, foreign_pending_copy_storage n good.live.hz good.live.hs outGet (Ne.symm different),
      count, (pending_copy_counts _ _).1, low, fields, ?_, bytes, pendingA, bits, ?_⟩
    · intro _positive zero
      have eq : d.pending - n.toUInt64 = 0 := UInt64.toNat_inj.mp zero
      simp only [pendingState, eq, BEq.rfl, ite_true]
    · simpa only [pointer] using foreign_pending_copy_buffer_frame (pb := pb) (po := po) (z := z) (d := d) n outGet different (by omega)



end Zlib.Deflate.Engine.Proofs
