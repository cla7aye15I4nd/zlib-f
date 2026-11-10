import ZlibF.Proof.«deflate.c.engine.tree-build»

/-! # Complete BL construction preserves the actual compressor heap -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs (TK BTBuildFrame BLInput BLCodeResult SourceGuards blScannedState)
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

set_option maxHeartbeats 1500000 in
/-- The two sentinel scans, actual BL builder and unsigned header-cost
update retain the engine representation. Their exact record effects and
the checked final tree representation supply every changed field. -/
theorem bl_tree_frame_good {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d scanned built result : DeflateState} {buf : Array UInt8}
    {B : Array CtData} {cost : UInt64}
    (good : DGood h r ds z d) (scans : scanned = blScannedState d B)
    (frame : BTBuildFrame .bl .bl scanned built) (finish : result = { built with opt_len := cost })
    (trees : TreesInvAt (setD h ds result) ds result pb buf) :
    DGood (setD h ds result) r ds z result := by
  have inv : DStInv h ds result := by
    obtain ⟨T, H, D, counts, hl, hm, mc, O, S, fields, _sizes⟩ := frame
    rw [finish, fields, scans] at trees ⊢
    exact { good.inv with wf := trees.base.wf
                          blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have shape := shape_setD good.live.hs result
  have back : result.strm = d.strm := by
    obtain ⟨T, H, D, counts, hl, hm, mc, O, S, fields, _sizes⟩ := frame
    rw [finish, fields, scans]
    rfl
  have status : result.status = d.status := by
    obtain ⟨T, H, D, counts, hl, hm, mc, O, S, fields, _sizes⟩ := frame
    rw [finish, fields, scans]
    rfl
  exact ⟨⟨by simpa only [ZStreamRef.get_setD] using good.live.hz, by simp, good.live.zst,
      back.trans good.live.back, status ▸ good.live.status, good.live.zalloc, good.live.zfree⟩,
    DStInv.congr (h := h) (h' := setD h ds result) rfl rfl rfl rfl inv,
    shape.uniq good.uniq, shape.fresh rfl good.fresh, ⟨result, pb, buf, trees⟩⟩

set_option maxHeartbeats 1500000 in
/-- `local int build_bl_tree(deflate_state *s)`.
The real scans, BL constructor, descending search and unsigned cost store
execute on the same engine heap. BLInput is supplied by actual source-tree
construction below. The returned representation, buffers, allocation ledger,
exact record frame, guards and independently decodable BL codes are retained.
The generic index is 2..18; the format minimum requires actual frequency history.
-/
theorem build_bl_tree_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (input : BLInput d) :
    ∃ (mb : Int32) (scanned built result : DeflateState) (B : Array CtData),
      Zlib.Trees.build_bl_tree (some (.tab ds)) h = .ok (mb, setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧
      scanned = blScannedState d B ∧
      (∀ k, B[k]!.fc = d.bl_tree[k]!.fc + UInt16.ofNat (Zlib.Trees.Proofs.blScanCount d k)) ∧
      BTBuildFrame .bl .bl scanned built ∧
      result = { built with opt_len := (built.opt_len + Zlib.Trees.Proofs.blHeaderCost
        (Zlib.Trees.Proofs.Math.blMaxIdx (Zlib.Trees.Proofs.blUsed built) 18)) } ∧
      mb.toInt = Zlib.Trees.Proofs.Math.blMaxIdx (Zlib.Trees.Proofs.blUsed built) 18 ∧
      2 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧ SourceGuards result ∧ BLCodeResult scanned result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d := by
  obtain ⟨mb, scanned, built, result, B, run, scans, frequencies, frame, finish,
    index, lower, upper, _tail, treesA, output, codes⟩ :=
    Zlib.Trees.Proofs.build_bl_tree_checked trees input
  have goodA := bl_tree_frame_good good scans frame finish treesA
  have depth : result.depth.size = d.depth.size := by
    obtain ⟨T, H, D, counts, hl, hm, mc, O, S, fields, _t, _h, depth, _b⟩ := frame
    rw [finish, fields]
    simpa only [scans, blScannedState] using depth
  have sizes := tree_record_sizes good.live.hs depth
  have owned : ∀ b, StreamOwned (setD h ds result) r b ↔ StreamOwned h r b := by
    intro b
    rw [stream_owned_deflate goodA, stream_owned_deflate good]
    obtain ⟨T, H, D, counts, hl, hm, mc, O, S, fields, _sizes⟩ := frame
    rw [finish, fields, scans]
    rfl
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z)
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := buf)
    good.live.hs trees.base.bytes
  rw [Zlib.Trees.Proofs.Out.setB_self trees.base.bytes] at storage
  obtain ⟨mb2, other, run2, guards⟩ := Zlib.Trees.Proofs.build_bl_tree_source_guards trees input
  have same : result = other := Zlib.Trees.Proofs.same_record_of_runs run run2
  exact ⟨mb, scanned, built, result, B, run, goodA, treesA, buffersA, sizes, storage,
    scans, frequencies, frame, finish, index, lower, upper, same ▸ guards, codes, output⟩

set_option maxHeartbeats 1500000 in
/-- The actual literal, distance and BL constructors compose without an
assumed BLInput or callee contract. The two source-tree scans and the final
cost store are included. Output and all caller ownership remain intact. -/
theorem all_trees_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) :
    ∃ (mb : Int32) (literal ready scanned built result : DeflateState) (B : Array CtData),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds))
          Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb, setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ BLInput ready ∧
      BTBuildFrame .lit .lit d literal ∧ BTBuildFrame .dist .dist literal ready ∧
      scanned = blScannedState ready B ∧ BTBuildFrame .bl .bl scanned built ∧
      result = { built with opt_len := (built.opt_len + Zlib.Trees.Proofs.blHeaderCost
        (Zlib.Trees.Proofs.Math.blMaxIdx (Zlib.Trees.Proofs.blUsed built) 18)) } ∧
      2 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧ SourceGuards result ∧ BLCodeResult scanned result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d := by
  obtain ⟨literal, ready, prepare, goodR, treesR, buffersR, sizesR, storageR, input, frameL, frameD, outputR⟩ :=
    source_trees_engine (ob := ob) good trees buffers
  obtain ⟨mb, scanned, built, result, B, run, goodA, treesA, buffersA, sizesA, storageA,
    scans, _frequencies, frame, finish, _index, lower, upper, guards, codes, output⟩ :=
    build_bl_tree_engine (ob := ob) goodR treesR buffersR input
  have complete : (do
        Zlib.Trees.Proofs.blPrepare (some (.tab ds))
        Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb, setD h ds result) := by
    rw [bind_app, prepare]
    simpa only [setD_setD] using run
  have sizes := sizesR.trans sizesA
  have storage := storageR.trans storageA
  simp only [setD_setD] at goodA treesA buffersA sizes storage
  exact ⟨mb, literal, ready, scanned, built, result, B, complete, goodA, treesA, buffersA,
    sizes, storage, input, frameL, frameD, scans, frame, finish, lower, upper, guards, codes,
    output.trans outputR⟩

/-- Exact state-record fields that preparation can change. Window, hash
chains, match history, positions, configuration, symbols and output state
are retained. Code arrays and constructor work arrays are explicit. -/
def TreePreparationFrame (before after : DeflateState) : Prop :=
  after = { before with
    dyn_ltree := after.dyn_ltree, dyn_dtree := after.dyn_dtree, bl_tree := after.bl_tree,
    l_desc := after.l_desc, d_desc := after.d_desc, bl_desc := after.bl_desc,
    bl_count := after.bl_count, heap := after.heap, heap_len := after.heap_len,
    heap_max := after.heap_max, depth := after.depth,
    opt_len := after.opt_len, static_len := after.static_len }

/-- Construction footprints compose without expanding every work array. -/
theorem TreePreparationFrame.trans {a b c : DeflateState}
    (first : TreePreparationFrame a b) (second : TreePreparationFrame b c) : TreePreparationFrame a c := by
  unfold TreePreparationFrame at first second ⊢
  rw [second, first]

/-- One actual constructor is contained in the complete preparation footprint. -/
theorem TreePreparationFrame.build {d result : DeflateState} {tk : TK}
    (frame : BTBuildFrame tk tk d result) : TreePreparationFrame d result := by
  obtain ⟨T, H, D, B, hl, hm, mc, O, S, fields, _sizes⟩ := frame
  unfold TreePreparationFrame
  rw [fields]
  cases tk <;> rfl

set_option maxHeartbeats 1500000 in
/-- Actual constructor and sentinel frames jointly retain every engine
field outside tree preparation. The cost update is included. -/
theorem all_tree_frames {d literal ready scanned built result : DeflateState}
    {B : Array CtData} {cost : UInt64}
    (literalFrame : BTBuildFrame .lit .lit d literal)
    (distanceFrame : BTBuildFrame .dist .dist literal ready)
    (scans : scanned = blScannedState ready B)
    (blFrame : BTBuildFrame .bl .bl scanned built)
    (finish : result = { built with opt_len := cost }) : TreePreparationFrame d result := by
  have scanFrame : TreePreparationFrame ready scanned := by
    rw [scans]
    rfl
  have costFrame : TreePreparationFrame built result := by
    rw [finish]
    rfl
  exact ((TreePreparationFrame.build literalFrame).trans
    (TreePreparationFrame.build distanceFrame)).trans
      (scanFrame.trans ((TreePreparationFrame.build blFrame).trans costFrame))

end Zlib.Deflate.Engine.Proofs
