import ZlibF.Proof.«deflate.c.universal-call-header»
import ZlibF.Proof.«deflate.c.universal-call-stages»
import ZlibF.Proof.«deflate.c.life.reset»
import ZlibF.Proof.«deflate.c.engine.pending-checksum»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-scalars»

/-!
# deflate.c: the zlib header stage of one `deflate` call

Batch C (`call_frame`, `deflate_header_trailer`). For every level, strategy, window size and
memory level, with or without a preset dictionary and with any held bits: the stage writes the
two header bytes (and the dictionary identifier), resets the checksum, enters `BUSY_STATE` and
flushes. With output room it delivers at least one byte.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- `flush_pending` keeps the stream checksum, for either kind of output view. -/
theorem flush_pending_adler {h after : Heap} {r : ZStreamRef} {ds pb ob produced : Nat}
    {z z' : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : (∃ oo, z.next_out = .ref (.blk ob) oo) ∨ (∃ oo, z.next_out = .ref (.dstate_depth ob) oo))
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) : z'.adler = z.adler := by
  rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
  · exact flush_pending_run_adler good trees buffers ptr cursor room run live account
  · obtain ⟨next, prepared, _bitRun, goodP, treesP, _bits, low, size, fields, _pending, _valid, sameRun⟩ :=
      flush_pending_prepare good trees cursor room
    have buffersP := output_bits_buffers good buffers cursor trees.base.bytes size fields treesP
    exact (flush_pending_low_foreign_run_scalar_effects goodP buffersP ptr low (sameRun.symm.trans run)
      live account).1

/-- **The end of the zlib header stage.** With header bytes pending and output room, the flush
delivers at least one byte; the stage returns `Z_OK` if bytes are left, else it continues. -/
theorem init_tail {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (pending : 1 ≤ d.pending.toNat) (avail : z.avail_out ≠ 0) (out : z.next_out ≠ .null) (k : M Int32) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      DGood after r ds z' d' ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      1 ≤ produced ∧ z'.adler = 1 ∧
      d' = { d with
        status := BUSY_STATE, pending := d'.pending, pending_out := d'.pending_out,
        bi_buf := d'.bi_buf, bi_valid := d'.bi_valid, bi_used := d'.bi_used } ∧
      initTail (some r) (some (.tab ds)) k h =
        (if d'.pending ≠ 0 then .ok (Z_OK, setD after ds { d' with last_flush := -1 }) else k after) := by
  let z1 : ZStream := { z with adler := 1 }
  let d1 : DeflateState := { d with status := BUSY_STATE }
  obtain ⟨good1, trees1, buffers1, _sizes1, account1⟩ :=
    adler_status_engine good trees buffers 1 BUSY_STATE (by simp [GoodStatus])
  change DGood (setD (r.put h z1) ds d1) r ds z1 d1 at good1
  obtain ⟨ob, pointer⟩ := Block.output_pointer_cases good1 buffers1 (show z1.next_out ≠ .null from out)
  have pointerK := pointer
  have published : ∃ (produced : Nat) (after : Heap) (z' : ZStream) (d' : DeflateState),
      flush_pending (some r) (setD (r.put h z1) ds d1) = .ok ((), after) ∧ DGood after r ds z' d' ∧
      StreamBuffers after r ∧ StreamAccounting z1 z' 0 produced ∧
      produced = min (d1.pending.toNat + d1.bi_valid.toInt.toNat / 8) z1.avail_out.toNat ∧
      d' = { d1 with
        pending := d'.pending, pending_out := d'.pending_out, bi_buf := d'.bi_buf,
        bi_valid := d'.bi_valid, bi_used := d'.bi_used } := by
    rcases pointer with ⟨oo, ptr⟩ | ⟨oo, ptr⟩
    · obtain ⟨produced, after, z', d', _w, _rem, run, goodA, buffersA, account, _s, _st, copied, _left,
        _low, _valid, fields, _b, _p, _o⟩ := flush_pending_raw_bits good1 trees1 buffers1 ptr cursor room
      exact ⟨produced, after, z', d', run, goodA, buffersA, account, copied, fields⟩
    · obtain ⟨produced, after, z', d', _w, _rem, run, goodA, buffersA, account, _s, _st, copied, _left,
        _low, _valid, fields, _b, _p, _o, _bf⟩ := flush_pending_foreign_bits_frame good1 trees1 buffers1 ptr cursor room
      exact ⟨produced, after, z', d', run, goodA, buffersA, account, copied, fields⟩
  obtain ⟨produced, after, z', d', run, goodA, buffersA, account, copied, fields⟩ := published
  have availPos : 1 ≤ z.avail_out.toNat := by
    have : z.avail_out.toNat ≠ 0 := fun e => avail (UInt32.toNat_inj.mp (by simpa using e))
    omega
  have one : 1 ≤ produced := by
    rw [copied]
    change 1 ≤ min (d.pending.toNat + _) z.avail_out.toNat
    omega
  have accountT : StreamAccounting z z' 0 produced := by
    simpa only [Nat.zero_add] using stream_accounting_trans account1 account
  have adler : z'.adler = 1 :=
    flush_pending_adler good1 trees1 buffers1 pointerK cursor room run goodA.live.hz account
  refine ⟨produced, after, z', d', goodA, buffersA, accountT, one, adler, ?_, ?_⟩
  · rw [fields]
  · unfold initTail
    simp only [bind_app, adler32_null, pure_app, zwr_eq, good.live.hz, wrD_eq, ZStreamRef.put_dstates,
      good.live.hs]
    simp only [z1, d1] at run
    rw [run]
    by_cases zero : d'.pending = 0
    · simp [rdD_eq, goodA.live.hs, zero]
    · simp [rdD_eq, goodA.live.hs, zero, wrD_eq]

end Zlib.Deflate.Universal.Call
