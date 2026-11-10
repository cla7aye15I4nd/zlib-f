import ZlibF.Proof.«trees.c.stored-copy»

/-! # The complete actual stored-block writer emits its concrete source bytes -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees
set_option autoImplicit false

/-- `void ZLIB_INTERNAL _tr_stored_block(deflate_state *s, charf *buf, ulg stored_len, int last)`.
The complete translated writer emits the actual tag, padding, two length
words and selected source bytes. Both final flags and zero length are
covered. The caller must connect these source bytes to its input history
and derive the pending-room premise from actual block selection. -/
theorem stored_block_emit {h : Heap} {id b sourceBlock offset : Nat} {d : DeflateState}
    {buf source : Array UInt8}
    (trees : TreesInvAt h id d b buf) (get : h.bytes sourceBlock = some source)
    (separate : b ≠ sourceBlock) (bits : d.bi_valid.toInt ≤ 7)
    (length : UInt64) (input : offset + length.toNat ≤ source.size)
    (room : d.pending.toNat + length.toNat + 6 ≤ buf.size) (last : Bool) :
    ∃ next result,
      «_tr_stored_block» (some (.tab id)) (.ref (.blk sourceBlock) offset) length (if last then 1 else 0) h =
        .ok ((), setD (setB h b next) id result) ∧
      TreesInvAt (setD (setB h b next) id result) id result b next ∧
      outBits next result = outBits buf d ++
        (storedHeaderBits d length last ++ sourceByteBits source offset length.toNat) ∧
      next.size = buf.size ∧ result.bi_valid.toInt = 0 ∧
      result.pending.toNat ≤ d.pending.toNat + length.toNat + 6 ∧ BitsDiff d result := by
  obtain ⟨headerBuf, header, headerRun, treesH, outputH, sizeH, alignedH, pendingH, diffH⟩ :=
    stored_block_header_emit trees bits (by omega) length last
  have getH : (setD (setB h b headerBuf) id header).bytes sourceBlock = some source := by
    simpa only [setD, setB, upd_ne _ _ _ _ (Ne.symm separate)] using get
  have roomH : header.pending.toNat + length.toNat ≤ headerBuf.size := by rw [sizeH]; omega
  obtain ⟨copyRun, treesA, outputA, pendingA, sizeA, diffA⟩ :=
    stored_block_copy_bits treesH getH separate length alignedH input roomH
  dsimp only at copyRun treesA outputA pendingA sizeA diffA
  simp only [setB_setD, setB_setB, setD_setD] at copyRun treesA
  refine ⟨_, _, ?_, treesA, ?_, sizeA.trans sizeH, alignedH, ?_, diffH.trans diffA⟩
  · rw [stored_block_source, bind_app, headerRun]
    exact copyRun
  · rw [outputA, outputH, List.append_assoc]
  · rw [pendingA]
    omega

end Zlib.Trees.Proofs.Out
