import ZlibF.Proof.«deflate.c.engine.stored-block»
import ZlibF.Proof.«deflate.c.engine.bl-tree»
import ZlibF.Proof.«deflate.c.engine.block-reset»

/-!
# trees.c: the stored branch of a block flush, for every memLevel

Batch C of the deflate skeleton (`docs/progress.md`, Core proof skeletons). The stored branch
of `_tr_flush_block` writes the stored header, copies `stored_len` source bytes into
`pending_buf`, resets the block (`init_block`) and, for the last block, aligns the output
(`bi_windup`). Nothing here depends on `lit_bufsize`: the caller supplies the room, which the
block selection derives for every memLevel (`selected_stored_room`).
-/

namespace Zlib.Deflate.Universal.Block
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff)
set_option autoImplicit false


/-- The fields a block flush may change: the trees and their work arrays, the costs, the symbol
count, the pending output and the bit buffer. Everything else of the record (window, hash
chains, match state, positions, parameters) is unchanged. -/
def FlushFrame (before after : DeflateState) : Prop :=
  after = { before with
    dyn_ltree := after.dyn_ltree, dyn_dtree := after.dyn_dtree, bl_tree := after.bl_tree,
    l_desc := after.l_desc, d_desc := after.d_desc, bl_desc := after.bl_desc,
    bl_count := after.bl_count, heap := after.heap, heap_len := after.heap_len,
    heap_max := after.heap_max, depth := after.depth,
    opt_len := after.opt_len, static_len := after.static_len, «matches» := after.«matches»,
    sym_next := after.sym_next, pending := after.pending, pending_out := after.pending_out,
    bi_buf := after.bi_buf, bi_valid := after.bi_valid, bi_used := after.bi_used }

theorem FlushFrame.refl (d : DeflateState) : FlushFrame d d := by
  unfold FlushFrame
  rfl

theorem FlushFrame.trans {a b c : DeflateState} (first : FlushFrame a b) (second : FlushFrame b c) :
    FlushFrame a c := by
  unfold FlushFrame at first second ⊢
  rw [second, first]

theorem FlushFrame.of_bits {a b : DeflateState} (diff : BitsDiff a b) : FlushFrame a b := by
  obtain ⟨p, w, v, u, rfl⟩ := diff
  unfold FlushFrame
  rfl

theorem FlushFrame.of_reset {a b : DeflateState} {a1 a2 a3 : Array CtData}
    (reset : b = Zlib.Trees.Proofs.Out.ibRec a a1 a2 a3) : FlushFrame a b := by
  subst reset
  unfold FlushFrame
  rfl

theorem FlushFrame.of_preparation {a b : DeflateState} (frame : TreePreparationFrame a b) : FlushFrame a b := by
  unfold TreePreparationFrame at frame
  rw [frame]
  unfold FlushFrame
  rfl

theorem FlushFrame.of_output {a b : DeflateState} (frame : BlockOutputFrame a b) : FlushFrame a b := by
  unfold BlockOutputFrame at frame
  rw [frame]
  unfold FlushFrame
  rfl

/-- The stored branch and the common tail of `_tr_flush_block`, from a drained entry
(`pending = 0`, at most seven held bits), for any readable source slice outside `pending_buf`
and any room the caller derives. Afterwards the block is empty and cleared, the output is
byte aligned, and the pending cursor is at the start of `pending_buf`. -/
theorem stored_block_safe {h : Heap} {r : ZStreamRef} {ds pb ob src off : Nat}
    {z : ZStream} {d : DeflateState} {buf source : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (get : h.bytes src = some source) (separate : pb ≠ src)
    (len : UInt64) (input : off + len.toNat ≤ source.size)
    (room : len.toNat + 6 ≤ buf.size) (last : Bool) :
    ∃ after result next,
      (do Zlib.Trees.«_tr_stored_block» (some (.tab ds)) (.ref (.blk src) off) len (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      SymbolLedger next result [] ∧ BlockInit.BlockClear result ∧
      next.size = buf.size ∧ result.pending.toNat ≤ len.toNat + 6 ∧
      result.pending_out = result.pending_buf ∧ result.bi_valid.toInt = 0 ∧ FlushFrame d result := by
  obtain ⟨next, emitted, run, treesE, _output, sizeE, alignedE, roomE, diff⟩ :=
    Zlib.Trees.Proofs.Out.stored_block_emit trees get separate bits len input
      (by rw [pending]; change 0 + len.toNat + 6 ≤ buf.size; omega) last
  change Zlib.Trees.«_tr_stored_block» (some (.tab ds)) (.ref (.blk src) off) len (if last then 1 else 0) h =
    .ok ((), setD (Zlib.Trees.Proofs.Out.setB h pb next) ds emitted) at run
  change TreesInvAt (setD (Zlib.Trees.Proofs.Out.setB h pb next) ds emitted) ds emitted pb next at treesE
  have goodE := output_bits_good good cursor trees.base.bytes sizeE diff treesE
  have buffersE := output_bits_buffers good buffers cursor trees.base.bytes sizeE diff treesE
  have sizesE := output_bits_sizes good trees.base.bytes sizeE diff
  have storageE := output_bits_storage (r := r) (ob := ob) (result := emitted) (next := next)
    good.live.hs trees.base.bytes
  have cursorE : emitted.pending_out = emitted.pending_buf := by
    obtain ⟨_, _, _, _, fields⟩ := diff
    rw [fields]
    exact cursor
  have pendingE : emitted.pending.toNat ≤ len.toNat + 6 := by
    rw [pending] at roomE
    change emitted.pending.toNat ≤ 0 + len.toNat + 6 at roomE
    omega
  obtain ⟨reset, resetRun, goodR, treesR, buffersR, sizesR, storageR, ledgerR, clearR, _resetBits⟩ :=
    init_block_clear_engine (ob := ob) goodE treesE buffersE
  obtain ⟨_a1, _a2, _a3, reset2, resetRun2, _good2, _trees2, _buffers2, _sizes2, _storage2,
    resetFields, _ledger2, _output2⟩ := init_block_engine (ob := ob) goodE treesE buffersE
  have same : reset2 = reset := Zlib.Trees.Proofs.same_record_of_runs resetRun2 resetRun
  rw [same] at resetFields
  have alignedR : reset.bi_valid.toInt = 0 := by rw [resetFields]; exact alignedE
  have frameR : FlushFrame d reset := (FlushFrame.of_bits diff).trans (FlushFrame.of_reset resetFields)
  have pendingR : reset.pending.toNat ≤ len.toNat + 6 := by rw [resetFields]; exact pendingE
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursorE
  have physical : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * next.size := by
    rw [alignedR, sizeE]
    simp only [Int.toNat_zero, Nat.add_zero]
    omega
  have sizes := sizesE.trans sizesR
  have storage := storageE.trans storageR
  cases last with
  | false =>
    change Zlib.Trees.«_tr_stored_block» (some (.tab ds)) (.ref (.blk src) off) len 0 h = .ok ((), _) at run
    refine ⟨_, reset, next, ?_, goodR, treesR, buffersR, sizes, storage,
      ledgerR, clearR, sizeE, pendingR, cursorR, alignedR, frameR⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, run, resetRun, show ((0 : Int32) != 0) = false from rfl,
      Bool.false_eq_true, ite_false, pure_app]
  | true =>
    change Zlib.Trees.«_tr_stored_block» (some (.tab ds)) (.ref (.blk src) off) len 1 h = .ok ((), _) at run
    obtain ⟨final, result, windRun, goodA, treesA, buffersA, sizesA, storageA, diffA,
      sizeA, _pendingA, zeroA, _wordA, cursorA, outputA⟩ :=
      windup_engine (ob := ob) goodR treesR buffersR cursorR physical
    have unchanged : Zlib.Trees.Proofs.Out.outBits final result =
        Zlib.Trees.Proofs.Out.outBits next reset := by
      simpa only [alignedR, Int.toNat_zero, Nat.zero_mod, Nat.sub_zero,
        show 8 % 8 = 0 from rfl, List.replicate_zero, List.append_nil] using outputA
    have count := congrArg List.length unchanged
    simp only [Zlib.Trees.Proofs.Out.outBits_length, zeroA, alignedR, Int.toNat_zero, Nat.add_zero] at count
    have bound : result.pending.toNat ≤ len.toNat + 6 := by omega
    refine ⟨_, result, final, ?_, goodA, treesA, buffersA, sizes.trans sizesA, storage.trans storageA,
      empty_ledger_bits ledgerR diffA, clearR.bits diffA, sizeA.trans sizeE, bound, cursorA, zeroA,
      frameR.trans (FlushFrame.of_bits diffA)⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, run, resetRun, show ((1 : Int32) != 0) = true from rfl, ite_true, windRun]

end Zlib.Deflate.Universal.Block
