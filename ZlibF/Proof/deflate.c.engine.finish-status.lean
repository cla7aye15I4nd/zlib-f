import ZlibF.Proof.«deflate.c.engine.public-strategy-source»

/-! # Actual public transition to the finishing state -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The public finishing-status store preserves the representation. -/
theorem finish_status_good {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) :
    DGood (setD h ds { d with status := FINISH_STATE }) r ds z { d with status := FINISH_STATE } := by
  have inv : DStInv h ds { d with status := FINISH_STATE } :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  exact good.setD' rfl (by simp [GoodStatus]) inv (by trkeep)

/-- The same actual store preserves the tree representation. -/
theorem finish_status_trees {h : Heap} {ds pb : Nat} {d : DeflateState} {buf : Array UInt8}
    (trees : TreesInvAt h ds d pb buf) :
    TreesInvAt (setD h ds { d with status := FINISH_STATE }) ds { d with status := FINISH_STATE } pb buf := by
  refine ⟨⟨by simp, trees.base.wf, trees.base.static, trees.base.pbuf,
    trees.base.bytes, trees.base.rw, trees.base.size, trees.base.psize,
    trees.base.sym, trees.base.lit_lo, trees.base.lit_hi, trees.base.sym_end, trees.base.pending_le⟩,
    ⟨trees.run.ldyn, trees.run.lstat, trees.run.ddyn, trees.run.dstat, trees.run.bldyn, trees.run.blstat,
      trees.run.bi_lo, trees.run.bi_hi, trees.run.bi_buf, trees.run.sym_next_le, trees.run.sym_next_mod⟩⟩

/-- The status store leaves the caller ranges and stream ownership valid. -/
theorem finish_status_buffers {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (buffers : StreamBuffers h r) :
    StreamBuffers (setD h ds { d with status := FINISH_STATE }) r := by
  have goodA := finish_status_good good
  have sizes := block_record_sizes (result := { d with status := FINISH_STATE }) good.live.hs rfl
  exact stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes
    (stream_owned_keys good goodA rfl rfl rfl rfl) (stream_accounting_zero z)

/-- The actual need_more branch records output exhaustion and returns OK. -/
theorem public_strategy_need_more {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hs : h.dstates ds = some d) (empty : z.avail_out = 0) :
    publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH need_more h =
      .ok (Z_OK, setD h ds { d with last_flush := -1 }) := by
  unfold publicStrategyReturn
  simp only [bind_app, pure_app, zrd_eq, hz, empty, BEq.rfl, Bool.false_or, Bool.true_or,
    show (need_more == finish_started) = false from rfl,
    show (need_more == finish_done) = false from rfl,
    Bool.false_eq_true, ite_false, ite_true, wrD_eq, hs]

/-- A started final block records FINISH_STATE before returning for
exhausted output, including a final block still queued for publication. -/
theorem public_strategy_finish_started {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hs : h.dstates ds = some d) (empty : z.avail_out = 0) :
    publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH finish_started h =
      .ok (Z_OK, setD (setD h ds { d with status := FINISH_STATE }) ds
        { d with status := FINISH_STATE, last_flush := -1 }) := by
  unfold publicStrategyReturn
  simp only [bind_app, pure_app, zrd_eq, hz, ZStreamRef.get_setD, empty, BEq.rfl,
    Bool.true_or, Bool.or_true, ite_true, wrD_eq, hs, setD_dstates_same]

/-- A completed final block records FINISH_STATE, then executes the
actual public trailer statements without another strategy call. -/
theorem public_strategy_finish_done {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hs : h.dstates ds = some d) :
    publicStrategyReturn (some r) (some (.tab ds)) Z_FINISH finish_done h =
      publicFinishTail (some r) (some (.tab ds)) Z_FINISH
        (setD h ds { d with status := FINISH_STATE }) := by
  unfold publicStrategyReturn
  simp only [bind_app, pure_app, BEq.rfl,
    show (finish_done == finish_started) = false from rfl,
    show (finish_done == need_more) = false from rfl,
    show (finish_done == block_done) = false from rfl,
    Bool.true_or, Bool.or_true, Bool.false_or, Bool.false_eq_true, ite_false, ite_true,
    wrD_eq, hs]

end Zlib.Deflate.Engine.Proofs
