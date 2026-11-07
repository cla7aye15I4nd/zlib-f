import ZlibF.Proof.«deflate.c.engine.block-reset»

/-! # Actual final-bit alignment preserves the engine and empty ledger -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false

/-- An empty symbol ledger has no unread-byte constraint. Bit-only state
updates retain its real leaf frequencies even if the output bytes change. -/
theorem empty_ledger_bits {buf next : Array UInt8} {d result : DeflateState}
    (ledger : SymbolLedger buf d []) (fields : BitsDiff d result) : SymbolLedger next result [] := by
  obtain ⟨_, _, _, _, equal⟩ := fields
  rw [equal]
  refine ⟨ledger.count, ledger.valid, ?_, ledger.literal, ledger.distance⟩
  intro i s selected
  simp at selected

/-- `local void bi_windup(deflate_state *s)`.
The actual byte/word/zero branches append precisely the terminal alignment
bits and clear the bit buffer. The returned heap retains DGood, caller
ranges, object identities and the full frame. Output room is an internal
data premise, supplied by the complete payload bound in block composition. -/
theorem windup_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat ≤ 8 * buf.size) :
    ∃ next result,
      let after := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
      Zlib.Trees.bi_windup (some (.tab ds)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BitsDiff d result ∧
      next.size = buf.size ∧ result.pending.toNat ≤ d.pending.toNat + 2 ∧
      result.bi_valid.toInt = 0 ∧ result.bi_buf = 0 ∧ result.pending_out = result.pending_buf ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        List.replicate ((8 - d.bi_valid.toInt.toNat % 8) % 8) false := by
  obtain ⟨next, result, run, treesA, output, validZero, wordZero, _used, size,
    _frame, _lower, upper, p, u, fields⟩ := Zlib.Trees.Proofs.Out.bi_windup_spec trees room
  have diff : BitsDiff d result := by rw [fields]; exact ⟨p, 0, 0, u, rfl⟩
  have goodA := output_bits_good good cursor trees.base.bytes size diff treesA
  have buffersA := output_bits_buffers good buffers cursor trees.base.bytes size diff treesA
  have sizes := output_bits_sizes good trees.base.bytes size diff
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := next)
    good.live.hs trees.base.bytes
  have cursorA : result.pending_out = result.pending_buf := by rw [fields]; exact cursor
  exact ⟨next, result, run, goodA, treesA, buffersA, sizes, storage, diff,
    size, upper, validZero, wordZero, cursorA, output⟩

end Zlib.Deflate.Engine.Proofs
