import ZlibF.Proof.«deflate.c.engine.fixed-format»

/-! # Actual block reset restores the empty symbol ledger without losing output -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt InitialFrequencies ibRec)
set_option autoImplicit false

/-- Exact record effects of selected fixed emission, reset and alignment.
Window, hash chains, match history, input cursors and configuration fields
are retained. The reset counters are established, not assumed. -/
def BlockOutputFrame (before after : DeflateState) : Prop :=
  after = { before with
    dyn_ltree := after.dyn_ltree, dyn_dtree := after.dyn_dtree, bl_tree := after.bl_tree,
    pending := after.pending, pending_out := after.pending_out,
    bi_buf := after.bi_buf, bi_valid := after.bi_valid, bi_used := after.bi_used,
    opt_len := 0, static_len := 0, «matches» := 0, sym_next := 0 }

theorem BlockOutputFrame.output {before middle : DeflateState} (frame : BlockOutputFrame before middle)
    (pending : UInt64) (cursor : BPtr) (word : UInt16) (valid used : Int32) :
    BlockOutputFrame before { middle with
      pending := pending, pending_out := cursor, bi_buf := word, bi_valid := valid, bi_used := used } := by
  unfold BlockOutputFrame at frame ⊢
  rw [frame]

theorem BlockOutputFrame.bits {before middle after : DeflateState} (frame : BlockOutputFrame before middle)
    (fields : Zlib.Trees.Proofs.Out.BitsDiff middle after) : BlockOutputFrame before after := by
  obtain ⟨p, a, v, u, equal⟩ := fields
  rw [equal]
  exact frame.output p middle.pending_out a v u

/-- A state-record update that retains depth keeps every public byte view.
This relation concerns the exact update heap, not a called-function contract. -/
theorem block_record_sizes {h : Heap} {ds : Nat} {d result : DeflateState}
    (state : h.dstates ds = some d) (depth : result.depth = d.depth) :
    ByteSizes h (setD h ds result) := by
  refine ⟨?_, ?_⟩
  · intro ref a get
    exact ⟨a, (byte_view_setD_depth state depth ref).trans get, rfl⟩
  · intro ref
    cases ref <;> rfl

/-- `local void init_block(deflate_state *s)`.
The real loops and end-marker store restore the actual empty symbol
ledger. The output bit stream, pending cursor/count and bit buffer are
unchanged. The same heap retains DGood, caller ranges and the complete
allocation/frame facts. No reset contract is a premise. -/
theorem init_block_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) :
    ∃ a1 a2 a3 result,
      Zlib.Trees.init_block (some (.tab ds)) h = .ok ((), setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧
      result = ibRec d a1 a2 a3 ∧ SymbolLedger buf result [] ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d := by
  obtain ⟨a1, a2, a3, result, run, treesA, fields, _size1, _size2, _size3,
    zeros, endMarker, distances, _bl, _len1, _len2, _len3⟩ :=
    Zlib.Trees.Proofs.Out.init_block_spec0 trees.base trees.run.to0
  have inv : DStInv h ds result := by
    rw [fields]
    refine { good.inv with
      wf := by simpa only [fields] using treesA.base.wf
      blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      sym := ?_ }
    exact ⟨good.inv.sym.1, good.inv.sym.2.1, by simp [ibRec], by simp [ibRec]⟩
  have shape := shape_setD good.live.hs result
  have goodA : DGood (setD h ds result) r ds z result := by
    refine ⟨?_, DStInv.congr (h := h) (h' := setD h ds result) rfl rfl rfl rfl inv,
      shape.uniq good.uniq, shape.fresh rfl good.fresh, ⟨result, pb, buf, treesA⟩⟩
    refine ⟨by simpa only [ZStreamRef.get_setD] using good.live.hz, by simp, good.live.zst,
      ?_, ?_, good.live.zalloc, good.live.zfree⟩
    · rw [fields]
      exact good.live.back
    · rw [fields]
      exact good.live.status
  have sizes := block_record_sizes good.live.hs (show result.depth = d.depth by rw [fields]; rfl)
  have owned : ∀ b, StreamOwned (setD h ds result) r b ↔ StreamOwned h r b := by
    intro b
    rw [stream_owned_deflate goodA, stream_owned_deflate good, fields]
    rfl
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z)
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := buf)
    good.live.hs trees.base.bytes
  rw [Zlib.Trees.Proofs.Out.setB_self trees.base.bytes] at storage
  have frequencies : InitialFrequencies a1 a2 := by
    constructor
    · intro n bound
      by_cases last : n = 256
      · subst n
        simp only [endMarker, ite_true]
        rfl
      · rw [zeros n bound last]
        simp [last]
    · intro n bound
      rw [distances n bound]
      rfl
  have ledger : SymbolLedger buf result [] := by
    rw [fields]
    exact empty_symbol_ledger rfl frequencies
  refine ⟨a1, a2, a3, result, run, goodA, treesA, buffersA, sizes, storage, fields, ledger, ?_⟩
  rw [fields]
  rfl

end Zlib.Deflate.Engine.Proofs
