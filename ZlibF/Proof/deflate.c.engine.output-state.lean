import ZlibF.Proof.«deflate.c.engine.pending-output»
import ZlibF.Proof.«deflate.c.engine.caller-frame»

/-! # Bit-output updates preserve the initialized compressor representation

The pending cursor is at the buffer base while new bytes are published.
TreesInvAt is a representation fact on that same concrete updated heap.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- Changing only output bits/bytes retains DGood when the real tree
invariant holds on the updated heap. The base cursor gives the pending
extent; no bit-writer contract is an assumption. -/
theorem output_bits_good {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d result : DeflateState} {buf next : Array UInt8}
    (good : DGood h r ds z d) (cursor : d.pending_out = d.pending_buf)
    (get : h.bytes pb = some buf) (size : next.size = buf.size) (fields : BitsDiff d result)
    (trees : TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) ds result pb next) :
    DGood (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) r ds z result := by
  obtain ⟨pending, word, valid, used, rfl⟩ := fields
  let result := { d with pending := pending, bi_buf := word, bi_valid := valid, bi_used := used }
  let copied := Zlib.Trees.Proofs.Out.setB h pb next
  have goodB : DGood copied r ds z d := good.bytes_set pb next buf get size
  obtain ⟨w, p, q, b, blocks⟩ := goodB.inv.blocks
  have bound : pending.toNat ≤ d.pending_buf_size.toNat := trees.base.pending_le
  have blocksA : DBlocks copied result w p q b :=
    { blocks with pout := ⟨0, by simpa [result, cursor] using blocks.pbuf,
        by simpa [result] using bound⟩ }
  have inv : DStInv copied ds result :=
    { goodB.inv with
      wf := trees.base.wf
      bits := ⟨trees.run.bi_lo, trees.run.bi_hi, trees.run.bi_buf⟩
      blocks := ⟨w, p, q, b, blocksA⟩ }
  have shape := shape_setD goodB.live.hs result
  refine ⟨?_, DStInv.congr (h := copied) (h' := setD copied ds result) rfl rfl rfl rfl inv,
    shape.uniq goodB.uniq, shape.fresh rfl goodB.fresh, ⟨result, pb, next, trees⟩⟩
  exact ⟨by simpa only [ZStreamRef.get_setD] using goodB.live.hz, by simp [result], good.live.zst,
    good.live.back, good.live.status, good.live.zalloc, good.live.zfree⟩

/-- `local void flush_pending(z_streamp strm)` (bit prefix).
The actual complete-byte flush produces a low-bit state on the same heap
that the remaining pending-copy code uses. Its output bit stream is
unchanged and its new byte count is exact. All 0..16 bit counts are covered.
The cursor-base and bit-room premises describe the publishing phase. -/
theorem flush_pending_prepare {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) :
    ∃ next result,
      Zlib.Trees.bi_flush (some (.tab ds)) h =
        .ok ((), setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) ∧
      DGood (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) r ds z result ∧
      TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) ds result pb next ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ∧
      result.bi_valid.toInt < 8 ∧ next.size = buf.size ∧ BitsDiff d result ∧
      result.pending.toNat = d.pending.toNat + d.bi_valid.toInt.toNat / 8 ∧
      result.bi_valid.toInt.toNat = d.bi_valid.toInt.toNat % 8 ∧
      flush_pending (some r) h = flush_pending (some r) (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) := by
  obtain ⟨next, result, run, treeA, bits, low, size, _frame, _lower, _upper, pending, word, valid, fields⟩ :=
    Zlib.Trees.Proofs.Out.bi_flush_spec trees room
  have diff : BitsDiff d result := by
    rw [fields]
    exact ⟨pending, word, valid, d.bi_used, rfl⟩
  have goodA := output_bits_good good cursor trees.base.bytes size diff treeA
  have length := congrArg List.length bits
  simp only [Zlib.Trees.Proofs.Out.outBits_length] at length
  have lower := treeA.run.bi_lo
  refine ⟨next, result, run, goodA, treeA, bits, low, size, diff, by omega, by omega, ?_⟩
  have second := Zlib.Trees.Proofs.Out.bi_flush_low goodA.live.hs low
  have getZ : r.get (Zlib.Trees.Proofs.Out.setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result) = some z := goodA.live.hz
  have loadZ := ldZStream_ok getZ
  have loadD := ldDeflateState_tab treeA.base.dstate
  unfold flush_pending
  simp only [bind_app, zrd_eq, good.live.hz, goodA.live.hz, good.live.zst, castDeflateState,
    Zlib.Trees.Proofs.Out.tr_flush_bits_eq, run, second, loadZ, loadD, ldZStream_ok goodA.live.hz, ldDeflateState_tab goodA.live.hs]
  rfl

end Zlib.Deflate.Engine.Proofs
