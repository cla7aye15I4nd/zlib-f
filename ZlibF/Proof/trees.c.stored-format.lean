import ZlibF.Proof.«trees.c.stored-block»
import ZlibF.Math.DeflateStoredBlock

/-! # The actual stored writer produces independently decoded block bytes -/

namespace Zlib.Trees.Proofs.Out
open C Zlib.Trees ZlibF.Spec
set_option autoImplicit false

def sourceBytes (source : Array UInt8) (offset count : Nat) : List UInt8 :=
  (List.range count).map (fun i => source[offset + i]!)

theorem sourceBytes_length (source : Array UInt8) (offset count : Nat) :
    (sourceBytes source offset count).length = count := by simp [sourceBytes]

theorem sourceByteBits_encode (source : Array UInt8) (offset count : Nat) :
    sourceByteBits source offset count = bytesToBits (sourceBytes source offset count) := by
  simp only [sourceByteBits, sourceBytes, bytesToBits, List.flatMap_map]
  rfl

/-- Both real UInt16 conversions agree with LEN and its independent
sixteen-bit complement once the actual selection establishes a small block. -/
theorem stored_output_wire (d : DeflateState) (source : Array UInt8) (offset : Nat)
    (length : UInt64) (last : Bool) (small : length.toNat < 65536) :
    storedHeaderBits d length last ++ sourceByteBits source offset length.toNat =
      storedTag last ++ storedBodyBits ((8 - (d.bi_valid.toInt.toNat + 3) % 8) % 8)
        (sourceBytes source offset length.toNat) := by
  have words := stored_length_words length small
  simp only [storedHeaderBits, storedTag, storedBodyBits, sourceBytes_length,
    words.1, words.2, sourceByteBits_encode, List.append_assoc]

/-- The complete actual stored writer's output satisfies the independent
stored-body rule for every aligned suffix. The source bytes are the real
heap slice copied by memcpy. Window/input history and full flush choice
must still supply this internal entry's explicit source and room facts. -/
theorem stored_block_format {h : Heap} {id b sourceBlock offset : Nat} {d : DeflateState}
    {buf source : Array UInt8}
    (trees : TreesInvAt h id d b buf) (get : h.bytes sourceBlock = some source)
    (separate : b ≠ sourceBlock) (bits : d.bi_valid.toInt ≤ 7)
    (length : UInt64) (small : length.toNat < 65536) (input : offset + length.toNat ≤ source.size)
    (room : d.pending.toNat + length.toNat + 6 ≤ buf.size) (last : Bool) :
    ∃ next result,
      «_tr_stored_block» (some (.tab id)) (.ref (.blk sourceBlock) offset) length (if last then 1 else 0) h =
        .ok ((), setD (setB h b next) id result) ∧
      TreesInvAt (setD (setB h b next) id result) id result b next ∧
      outBits next result = outBits buf d ++ (storedTag last ++
        storedBodyBits ((8 - (d.bi_valid.toInt.toNat + 3) % 8) % 8) (sourceBytes source offset length.toNat)) ∧
      next.size = buf.size ∧ result.bi_valid.toInt = 0 ∧
      result.pending.toNat ≤ d.pending.toNat + length.toNat + 6 ∧ BitsDiff d result ∧
      ∀ (history : List UInt8) (suffix : List Bool), suffix.length % 8 = 0 →
        Body [] 0 history
          (storedBodyBits ((8 - (d.bi_valid.toInt.toNat + 3) % 8) % 8)
            (sourceBytes source offset length.toNat) ++ suffix) suffix
          (history ++ sourceBytes source offset length.toNat) := by
  obtain ⟨next, result, run, treesA, output, size, aligned, pending, diff⟩ :=
    stored_block_emit trees get separate bits length input room last
  rw [stored_output_wire d source offset length last small] at output
  refine ⟨next, result, run, treesA, output, size, aligned, pending, diff, ?_⟩
  intro history suffix suffixAligned
  exact stored_body_grammar history (sourceBytes source offset length.toNat) _ suffix
    (by rw [sourceBytes_length]; exact small) (Nat.mod_lt _ (by decide +kernel)) suffixAligned

end Zlib.Trees.Proofs.Out
