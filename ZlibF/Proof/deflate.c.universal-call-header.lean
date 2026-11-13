import ZlibF.Proof.«deflate.c.universal-call-entry»
import ZlibF.Proof.«deflate.c.engine.macros»
import ZlibF.Proof.«deflate.c.engine.stream-control»

/-!
# deflate.c: the header stages of one `deflate` call

Batch C of the deflate skeleton (`call_frame`, `deflate_header_trailer`). The header stages write
bytes into `pending_buf` with the `deflate.c` `put_byte`, then publish them with `flush_pending`.
Every lemma here holds for every level, strategy, window size, memory level and held bit count.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- **One header byte.** `put_byte` stores the byte at `pending_buf[pending]` and keeps the engine
invariants, the caller buffers, every other byte object and the held bits. -/
theorem header_byte {h : Heap} {r : ZStreamRef} {ds pb ob : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : d.pending.toNat < buf.size) (c : UInt8) :
    let next := buf.set! d.pending.toNat c
    let result : DeflateState := { d with pending := d.pending + 1 }
    let after := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
    put_byte (some (.tab ds)) c h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      result.pending.toNat = d.pending.toNat + 1 ∧ next.size = buf.size ∧
      result.pending_out = result.pending_buf := by
  intro next result after
  have small := trees.base.pending_small
  have pending : result.pending.toNat = d.pending.toNat + 1 :=
    Zlib.Trees.Proofs.Out.toNat_add_one_u64 small
  have size : next.size = buf.size := by simp only [next, Array.size_set!]
  have run : put_byte (some (.tab ds)) c h = .ok ((), after) := by
    have step := put_byte_ok (sr := ds) (b := pb) (off := 0) (a := buf) c trees.base.dstate
      trees.base.pbuf trees.base.bytes trees.base.rw (by omega)
    rw [step]
    simp only [Nat.zero_add]
    rfl
  have treesA : TreesInvAt after ds result pb next :=
    ⟨trees.base.step next size result trees.base.wf rfl rfl rfl rfl rfl
      (by change result.pending.toNat ≤ d.pending_buf_size.toNat
          rw [pending, trees.base.psize]; exact room),
      trees.run.ldyn, trees.run.lstat, trees.run.ddyn, trees.run.dstat, trees.run.bldyn, trees.run.blstat,
      trees.run.bi_lo, trees.run.bi_hi, trees.run.bi_buf, trees.run.sym_next_le, trees.run.sym_next_mod⟩
  have diff : BitsDiff d result := ⟨d.pending + 1, d.bi_buf, d.bi_valid, d.bi_used, rfl⟩
  exact ⟨run, output_bits_good good cursor trees.base.bytes size diff treesA,
    treesA, output_bits_buffers good buffers cursor trees.base.bytes size diff treesA,
    output_bits_sizes good trees.base.bytes size diff,
    output_bits_storage good.live.hs trees.base.bytes, pending, size, cursor⟩

theorem stream_accounting_adler (z : ZStream) (v : UInt64) :
    StreamAccounting z { z with adler := v } 0 0 := by
  refine ⟨by omega, by omega, by simp, by simp, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · cases z.next_in <;> rfl
  · cases z.next_out <;> rfl

/-- **A checksum and status update.** `strm->adler = v; s->status = st;` for a status that
`deflateStateCheck` accepts keeps the engine invariants and the caller buffers. -/
theorem adler_status_engine {h : Heap} {r : ZStreamRef} {ds pb : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (v : UInt64) (st : Int32) (status : GoodStatus st) :
    let z' : ZStream := { z with adler := v }
    let result : DeflateState := { d with status := st }
    let after := setD (r.put h z') ds result
    DGood after r ds z' result ∧ TreesInvAt after ds result pb buf ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ StreamAccounting z z' 0 0 := by
  intro z' result after
  have inv : DStInv h ds result :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA : DGood after r ds z' result :=
    good.setZD rfl good.live.zalloc good.live.zfree rfl status inv (by trkeep)
  have treesA : TreesInvAt after ds result pb buf := by
    refine trees_at_buffer goodA trees.base.pbuf ?_
    change (setD (r.put h z') ds result).bytes pb = some buf
    simpa only [setD, ZStreamRef.put_bytes] using trees.base.bytes
  have sizes : ByteSizes h after :=
    (stream_control_sizes h r z').trans
      (block_record_sizes (d := d) (result := result) (by simpa only [ZStreamRef.put_dstates] using good.live.hs) rfl)
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  have account := stream_accounting_adler z v
  exact ⟨goodA, treesA, stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned account,
    sizes, account⟩

/-- `header_byte` with the heap and the buffer abstracted. -/
theorem header_byte' {h : Heap} {r : ZStreamRef} {ds pb ob : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : d.pending.toNat < buf.size) (c : UInt8) :
    ∃ after next, put_byte (some (.tab ds)) c h = .ok ((), after) ∧
      DGood after r ds z { d with pending := d.pending + 1 } ∧
      TreesInvAt after ds { d with pending := d.pending + 1 } pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      (d.pending + 1).toNat = d.pending.toNat + 1 ∧ next.size = buf.size := by
  obtain ⟨run, goodA, treesA, buffersA, sizes, storage, count, size, _⟩ :=
    header_byte (ob := ob) good trees buffers cursor room c
  exact ⟨_, _, run, goodA, treesA, buffersA, sizes, storage, count, size⟩

/-- **Two header bytes**, most significant first (`putShortMSB`). -/
theorem header_short {h : Heap} {r : ZStreamRef} {ds pb ob : Nat} {z : ZStream} {d : DeflateState}
    {buf : Array UInt8} (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (cursor : d.pending_out = d.pending_buf)
    (room : d.pending.toNat + 2 ≤ buf.size) (v : UInt32) :
    ∃ after next, putShortMSB (some (.tab ds)) v h = .ok ((), after) ∧
      DGood after r ds z { d with pending := d.pending + 2 } ∧
      TreesInvAt after ds { d with pending := d.pending + 2 } pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      (d.pending + 2).toNat = d.pending.toNat + 2 ∧ next.size = buf.size := by
  obtain ⟨mid, next1, run1, good1, trees1, buffers1, sizes1, storage1, count1, size1⟩ :=
    header_byte' (ob := ob) good trees buffers cursor (by omega) (v >>> 8).toUInt8
  obtain ⟨after, next2, run2, good2, trees2, buffers2, sizes2, storage2, count2, size2⟩ :=
    header_byte' (ob := ob) good1 trees1 buffers1 cursor
      (by change (d.pending + 1).toNat < next1.size; omega) (v &&& 0xff).toUInt8
  have small := trees.base.pending_small
  have two : d.pending + 1 + 1 = d.pending + 2 := by
    apply UInt64.toNat_inj.mp
    have small1 : (d.pending + 1).toNat < 2 ^ 20 := trees1.base.pending_small
    rw [Zlib.Trees.Proofs.Out.toNat_add_one_u64 small1, count1,
      Zlib.Trees.Proofs.Out.toNat_add_two_u64 small]
  have count : (d.pending + 2).toNat = d.pending.toNat + 2 := Zlib.Trees.Proofs.Out.toNat_add_two_u64 small
  change DGood after r ds z { d with pending := d.pending + 1 + 1 } at good2
  change TreesInvAt after ds { d with pending := d.pending + 1 + 1 } pb next2 at trees2
  rw [two] at good2 trees2
  refine ⟨after, next2, ?_, good2, trees2, buffers2, sizes1.trans sizes2, storage1.trans storage2,
    count, size2.trans size1⟩
  unfold putShortMSB
  rw [bind_app, run1]
  exact run2

end Zlib.Deflate.Universal.Call
