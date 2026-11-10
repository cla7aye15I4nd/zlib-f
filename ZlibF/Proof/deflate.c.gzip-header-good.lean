import ZlibF.Proof.«deflate.c.gzip-header-contract»

namespace Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- Header-ready representation follows from initialized owned storage.
No new allocation, output capacity, callee contract or gzip-loop invariant is assumed. -/
theorem gzip_header_ready_good {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (cursor : d.pending_out = d.pending_buf) :
    DGood (gzipHeaderReady h r ds pb z d buf) r ds {z with adler := 0} (gzipHeaderState d) := by
  let hb := {h with bytes := upd h.bytes pb (some (gzipHeaderBytes buf))}
  have size : (gzipHeaderBytes buf).size = buf.size := gzip_header_bytes_size buf
  have goodB : DGood hb r ds z d := good.bytes_set pb (gzipHeaderBytes buf) buf trees.base.bytes size
  obtain ⟨w,p,q,b,blocks⟩ := goodB.inv.blocks
  have room : 10 ≤ d.pending_buf_size.toNat := by
    rw [trees.base.psize]
    have lower := trees.base.lit_lo
    have extent := trees.base.size
    omega
  have blocksA : DBlocks hb (gzipHeaderState d) w p q b :=
    {blocks with pout := ⟨0,by change d.pending_out = .ref (.blk b) 0; rw [cursor]; exact blocks.pbuf,
      by change 0 + 10 ≤ d.pending_buf_size.toNat; omega⟩}
  have inv : DStInv hb ds (gzipHeaderState d) :=
    {goodB.inv with blocks := ⟨w,p,q,b,blocksA⟩}
  have constructed := goodB.setZD (z' := {z with adler := 0}) (d' := gzipHeaderState d)
    rfl good.live.zalloc good.live.zfree rfl (by simp [GoodStatus,gzipHeaderState]) inv (by trkeep)
  simpa only [gzipHeaderReady,hb,stream_put_bytes,ZStreamRef.put_bytes] using constructed

end Zlib.Deflate.Engine.Proofs.DefaultGzipProofs
