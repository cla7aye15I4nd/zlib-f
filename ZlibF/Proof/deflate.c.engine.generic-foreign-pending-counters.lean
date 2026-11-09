import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-scalars»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-complete-pending»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- Actual complete pending publication has exact wrapping counters for legal foreign output.
Bit preparation leaves the stream unchanged before the proved low-bit source copy. -/
theorem default_foreign_flush_pending_run_counter_effects {h after : Heap} {r : ZStreamRef}
    {ds pb owner oo produced : Nat} {z z' : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) oo) (cursor : d.pending_out=d.pending_buf)
    (room : 8*d.pending.toNat+d.bi_valid.toInt.toNat≤8*buf.size)
    (run : flush_pending (some r) h=.ok ((),after)) (live : r.get after=some z')
    (account : StreamAccounting z z' 0 produced) :
    z'.total_in=z.total_in ∧ z'.total_out=z.total_out+UInt64.ofNat produced := by
  obtain ⟨next,prepared,_bitRun,goodP,treesP,_bits,low,size,diff,_pending,_valid,sameRun⟩ :=
    flush_pending_prepare good trees cursor room
  have buffersP := output_bits_buffers good buffers cursor trees.base.bytes size diff treesP
  have scalar := flush_pending_low_foreign_run_scalar_effects goodP buffersP pointer low
    (sameRun.symm.trans run) live account
  exact ⟨scalar.2.1,scalar.2.2.1⟩

end Zlib.Deflate.Engine.Proofs
