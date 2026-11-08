import ZlibF.Proof.«deflate.c.engine.counter-effects»
import ZlibF.Proof.«deflate.c.engine.pending-block-output»

/-! # Complete actual pending publication preserves the checksum -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A complete actual low-bit pending run retains the checksum at
zero, partial and complete raw output capacity, including advanced cursors. -/
theorem flush_pending_low_run_adler {h after : Heap} {r : ZStreamRef} {ds ob oo produced : Nat}
    {z z' : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (low : d.bi_valid.toInt < 8)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) :
    z'.adler = z.adler := by
  by_cases zero : pendingLen d.pending z.avail_out = 0
  · have run0 := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low zero
    have heaps : h = after := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    have streams : z = z' := by
      have get := live
      rw [← heaps] at get
      exact Option.some.inj (good.live.hz.symm.trans get)
    rw [← streams]
  · obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
    obtain ⟨buf, get, size⟩ := blocks.ba
    obtain ⟨po, cursor, bound⟩ := blocks.pout
    have sourceBound : po + d.pending.toNat ≤ buf.size := by rw [size, ← blocks.psize]; exact bound
    obtain ⟨output, outGet, writable, outBound, outside⟩ := caller_raw_output good buffers pointer
    have separate : ob ≠ pb := by
      intro same
      subst ob
      exact outside (Or.inr (Or.inr (Or.inr (Or.inr blocks.pbuf))))
    let n := pendingLen d.pending z.avail_out
    let expected := pendingCopyHeap h r ds pb po ob oo z d buf output n
    have run0 : flush_pending (some r) h = .ok ((), expected) :=
      flush_pending_low_raw good.live.hz good.live.zst good.live.hs low pointer cursor outGet get writable
        separate outBound sourceBound zero
    have good0 := pending_copy_good (pending := buf) (oo := oo) good blocks.pbuf cursor outGet
    have heaps : expected = after := (Prod.mk.inj (Except.ok.inj (run0.symm.trans run))).2
    have streams : pendingStream z (.ref (.blk ob) (oo + n.toNat)) n = z' := by
      have get0 := good0.live.hz
      change r.get expected = some _ at get0
      rw [heaps] at get0
      exact Option.some.inj (get0.symm.trans live)
    rw [← streams]
    rfl

/-- Bit preparation retains the stream. The complete pending call therefore
retains the checksum through verified low-bit publication. -/
theorem flush_pending_run_adler {h after : Heap} {r : ZStreamRef} {ds pb ob oo produced : Nat}
    {z z' : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (pointer : z.next_out = .ref (.blk ob) oo)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (run : flush_pending (some r) h = .ok ((), after)) (live : r.get after = some z')
    (account : StreamAccounting z z' 0 produced) :
    z'.adler = z.adler := by
  obtain ⟨next, prepared, _bitRun, goodP, treesP, _bits, low, size, fields, _pending, _valid, sameRun⟩ :=
    flush_pending_prepare good trees cursor room
  have buffersP := output_bits_buffers good buffers cursor trees.base.bytes size fields treesP
  exact flush_pending_low_run_adler goodP buffersP pointer low (sameRun.symm.trans run) live account

end Zlib.Deflate.Engine.Proofs
