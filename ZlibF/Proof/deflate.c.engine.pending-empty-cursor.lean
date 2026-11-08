import ZlibF.Proof.«deflate.c.engine.pending-buffered»

/-! # Actual pending copies retain the empty-cursor phase -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- An actual low-bit pending run retains the empty-cursor phase without
requiring the logical content boundary. -/
theorem low_pending_run_empty_cursor {h after : Heap} {r : ZStreamRef} {ds ob oo : Nat}
    {z : ZStream} {d result : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (low : d.bi_valid.toInt < 8)
    (cursor : d.pending = 0 → d.pending_out = d.pending_buf)
    (run : flush_pending (some r) h = .ok ((), after)) (live : after.dstates ds = some result) :
    result.pending = 0 → result.pending_out = result.pending_buf := by
  obtain ⟨w, p, q, pb, blocks⟩ := good.inv.blocks
  obtain ⟨buf, get, size⟩ := blocks.ba
  obtain ⟨po, source, bound⟩ := blocks.pout
  have pending := pending_bits_slice source get (by rw [size, ← blocks.psize]; exact bound)
  obtain ⟨_pb, produced, other, z', otherD, _written, _remaining, _base, otherRun, otherGood, _buffersA,
      _account, _sizes, _storage, amount, _left, _low, _fields, reset, _bytes, _pendingA, _bits⟩ :=
    flush_pending_resume_raw_bits good buffers pointer low pending
  have otherCursor : otherD.pending = 0 → otherD.pending_out = otherD.pending_buf := by
    intro empty
    by_cases moved : 0 < produced
    · exact reset moved (by rw [empty]; rfl)
    · have noCopy : pendingLen d.pending z.avail_out = 0 := by
        apply UInt32.toNat_inj.mp
        change (pendingLen d.pending z.avail_out).toNat = 0
        rw [pendingLen_value, ← amount]
        omega
      have zeroRun := flush_pending_low_zero good.live.hz good.live.zst good.live.hs low noCopy
      have heaps : h = other := (Prod.mk.inj (Except.ok.inj (zeroRun.symm.trans otherRun))).2
      have states : d = otherD := by
        have hs := otherGood.live.hs
        rw [← heaps] at hs
        exact Option.some.inj (good.live.hs.symm.trans hs)
      rw [← states] at empty ⊢
      exact cursor empty
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  rw [heaps] at otherGood
  have states : otherD = result := Option.some.inj (otherGood.live.hs.symm.trans live)
  rw [← states]
  exact otherCursor

/-- The actual complete-byte bit flush followed by pending copying
establishes the empty-cursor phase at every raw output capacity. -/
theorem raw_pending_run_empty_cursor {h after : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d result : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size)
    (run : flush_pending (some r) h = .ok ((), after)) (live : after.dstates ds = some result) :
    result.pending = 0 → result.pending_out = result.pending_buf := by
  obtain ⟨next, prepared, _bitRun, goodP, treesP, _bitStream, low, size, diff, _count, _valid, sameRun⟩ :=
    flush_pending_prepare good trees cursor room
  have buffersP := output_bits_buffers good buffers cursor trees.base.bytes size diff treesP
  have cursorP : prepared.pending_out = prepared.pending_buf := by
    obtain ⟨_, _, _, _, fields⟩ := diff
    rw [fields]
    exact cursor
  exact low_pending_run_empty_cursor goodP buffersP pointer low (fun _ => cursorP) (sameRun.symm.trans run) live

end Zlib.Deflate.Engine.Proofs
