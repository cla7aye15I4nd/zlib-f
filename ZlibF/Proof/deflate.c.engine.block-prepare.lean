import ZlibF.Proof.«deflate.c.engine.bl-tree»
import ZlibF.Proof.«trees.c.detect»
import ZlibF.Proof.«trees.c.flush-source»

/-! # The actual block-preparation prefix on the compressor heap -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The actual hint test and conditional stream-field store. -/
def blockDataType (s : DeflateStatePtr) : M Unit := do
  let strm := (← Zlib.Trees.rd s).strm
  if (← ldZStream strm).data_type == Z_UNKNOWN then
    let t ← Zlib.Trees.detect_data_type s
    stZStream strm { (← ldZStream strm) with data_type := t }

/-- The exact three constructors, after the actual data-type hint statements. -/
def blockPrepare (s : DeflateStatePtr) : M Int32 := do
  blockDataType s
  Zlib.Trees.Proofs.blPrepare s
  Zlib.Trees.build_bl_tree s

/-- Updating only the public hint retains the initialized engine,
caller buffers, accounting and exact allocation/object frame. -/
theorem data_type_stream_facts {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) (kind : Int32) :
    let z' := { z with data_type := kind }
    DGood (r.put h z') r ds z' d ∧ TreesInvAt (r.put h z') ds d pb buf ∧
    StreamBuffers (r.put h z') r ∧ StreamAccounting z z' 0 0 ∧ ByteSizes h (r.put h z') ∧
    OutputStorage h (r.put h z') r ds pb ob := by
  let z' := { z with data_type := kind }
  have goodA := good.setZD (z' := z') (d' := d) rfl good.live.zalloc good.live.zfree
    rfl good.live.status good.inv (by trkeep)
  rw [setD_self (by simpa using good.live.hs)] at goodA
  have treesA : TreesInvAt (r.put h z') ds d pb buf := by
    refine ⟨⟨by simpa using trees.base.dstate, trees.base.wf, ?_, trees.base.pbuf,
      ?_, ?_, trees.base.size, trees.base.psize, trees.base.sym, trees.base.lit_lo,
      trees.base.lit_hi, trees.base.sym_end, trees.base.pending_le⟩, trees.run⟩
    · simpa using trees.base.static
    · simpa using trees.base.bytes
    · simpa using trees.base.rw
  have sizes : ByteSizes h (r.put h z') := by
    refine ⟨?_, ?_⟩
    · intro ref a get
      exact ⟨a, (byte_get_stream_put h r z' ref).trans get, rfl⟩
    · intro ref
      cases ref <;> simp [Space.ro]
  have account : StreamAccounting z z' 0 0 := stream_accounting_zero z
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned account
  have storage : OutputStorage h (r.put h z') r ds pb ob := by
    refine ⟨shape_put good.live.hz z', by simp, by simp, ?_⟩
    obtain ⟨static, alloc, garbage, next, nalloc, slots⟩ := DefaultInit.frame_put r z' good.fresh
    exact ⟨static, alloc, garbage, next, nalloc,
      fun x live outside => slots x live (fun root => outside (Or.inl root))⟩
  exact ⟨goodA, treesA, buffersA, account, sizes, storage⟩

/-- Actual data-type detection and its conditional public-field store.
Known hints are retained. Unknown hints are replaced by BINARY or TEXT.
The detector's heap safety is used as a proved execution result. -/
theorem block_data_type_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) :
    ∃ z', blockDataType (some (.tab ds)) h = .ok ((), r.put h z') ∧
      DGood (r.put h z') r ds z' d ∧ TreesInvAt (r.put h z') ds d pb buf ∧
      StreamBuffers (r.put h z') r ∧ StreamAccounting z z' 0 0 ∧
      ByteSizes h (r.put h z') ∧ OutputStorage h (r.put h z') r ds pb ob ∧
      z' = { z with data_type := z'.data_type } ∧
      (z.data_type = Z_UNKNOWN → z'.data_type = Z_BINARY ∨ z'.data_type = Z_TEXT) ∧
      (z.data_type ≠ Z_UNKNOWN → z' = z) := by
  by_cases unknown : z.data_type = Z_UNKNOWN
  · obtain ⟨kind, detector, allowed⟩ := Zlib.Trees.Proofs.detect_data_type_safe good.live.hs
      (by have wf := trees.base.wf.1; omega)
    obtain ⟨goodA, treesA, buffersA, account, sizes, storage⟩ :=
      data_type_stream_facts (ob := ob) good trees buffers kind
    refine ⟨{ z with data_type := kind }, ?_, goodA, treesA, buffersA, account, sizes, storage,
      rfl, fun _ => allowed, fun no => (no unknown).elim⟩
    unfold blockDataType
    simp only [bind_app, pure_app, Zlib.Trees.Proofs.Out.rd_run good.live.hs,
      good.live.back, ldZStream_ok good.live.hz, unknown, BEq.rfl, ite_true, detector]
    exact stZStream_ok good.live.hz (by cases r <;> rfl)
  · obtain ⟨goodA, treesA, buffersA, account, sizes, storage⟩ :=
      data_type_stream_facts (ob := ob) good trees buffers z.data_type
    refine ⟨z, ?_, goodA, treesA, buffersA, account, sizes, storage,
      rfl, fun yes => (unknown yes).elim, fun _ => rfl⟩
    unfold blockDataType
    simp only [bind_app, pure_app, Zlib.Trees.Proofs.Out.rd_run good.live.hs,
      good.live.back, ldZStream_ok good.live.hz, show (z.data_type == Z_UNKNOWN) = false from beq_eq_false_iff_ne.mpr unknown,
      Bool.false_eq_true, ite_false, ZStreamRef.put_self good.live.hz]

/-- The complete actual positive-level preparation prefix includes unknown
hint detection, both source trees, both scans, the BL tree, search and cost
store. All caller ranges, ownership and output bits are retained. -/
theorem block_prepare_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) :
    ∃ (mb : Int32) (z' : ZStream) (result : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds result) ∧
      DGood (setD (r.put h z') ds result) r ds z' result ∧
      TreesInvAt (setD (r.put h z') ds result) ds result pb buf ∧
      StreamBuffers (setD (r.put h z') ds result) r ∧ StreamAccounting z z' 0 0 ∧
      ByteSizes h (setD (r.put h z') ds result) ∧ OutputStorage h (setD (r.put h z') ds result) r ds pb ob ∧
      2 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧ Zlib.Trees.Proofs.SourceGuards result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d ∧
      z' = { z with data_type := z'.data_type } := by
  obtain ⟨z', hint, goodZ, treesZ, buffersZ, account, sizesZ, storageZ, fieldsZ, _unknown, _known⟩ :=
    block_data_type_engine (ob := ob) good trees buffers
  obtain ⟨mb, literal, ready, scanned, built, result, B, run, goodA, treesA, buffersA,
    sizesA, storageA, _input, _frameL, _frameD, _scans, _frame, _finish, lower, upper, guards, _codes, output⟩ :=
    all_trees_engine (ob := ob) goodZ treesZ buffersZ
  refine ⟨mb, z', result, ?_, goodA, treesA, buffersA, account,
    sizesZ.trans sizesA, storageZ.trans storageA, lower, upper, guards, output, fieldsZ⟩
  unfold blockPrepare
  rw [bind_app, hint]
  exact run

/-- The complete preparation result also exposes every retained engine
field, so stronger reachable-state invariants can be transported. -/
theorem block_prepare_engine_frame {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) :
    ∃ (mb : Int32) (z' : ZStream) (result : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds result) ∧
      DGood (setD (r.put h z') ds result) r ds z' result ∧
      TreesInvAt (setD (r.put h z') ds result) ds result pb buf ∧
      StreamBuffers (setD (r.put h z') ds result) r ∧ StreamAccounting z z' 0 0 ∧
      ByteSizes h (setD (r.put h z') ds result) ∧ OutputStorage h (setD (r.put h z') ds result) r ds pb ob ∧
      2 ≤ mb.toInt ∧ mb.toInt ≤ 18 ∧ Zlib.Trees.Proofs.SourceGuards result ∧
      TreePreparationFrame d result ∧ Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d ∧
      z' = { z with data_type := z'.data_type } := by
  obtain ⟨z', hint, goodZ, treesZ, buffersZ, account, sizesZ, storageZ, fieldsZ, _unknown, _known⟩ :=
    block_data_type_engine (ob := ob) good trees buffers
  obtain ⟨mb, literal, ready, scanned, built, result, B, run, goodA, treesA, buffersA,
    sizesA, storageA, _input, frameL, frameD, scans, frame, finish, lower, upper, guards, _codes, output⟩ :=
    all_trees_engine (ob := ob) goodZ treesZ buffersZ
  have fields := all_tree_frames frameL frameD scans frame finish
  refine ⟨mb, z', result, ?_, goodA, treesA, buffersA, account,
    sizesZ.trans sizesA, storageZ.trans storageA, lower, upper, guards, fields, output, fieldsZ⟩
  unfold blockPrepare
  rw [bind_app, hint]
  exact run

section source
open Zlib.Trees Zlib.Trees.Proofs Out

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- `void ZLIB_INTERNAL _tr_flush_block(deflate_state *s, charf *buf, ulg stored_len, int last)`.
The complete source uses exactly the checked block-preparation prefix.
All byte-cost computations and stored/fixed/dynamic selection remain in
place. This is source equality, not a branch-selection assumption. -/
theorem flush_block_prepare_source (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) :
    «_tr_flush_block» s buf stored_len last = (do
  -- int max_blindex = 0;
  let mut max_blindex : Int32 := 0
  let mut opt_lenb : UInt64 := 0
  let mut static_lenb : UInt64 := 0
  if (← Zlib.Trees.rd s).level.toInt > 0 then
    max_blindex ← blockPrepare s
    -- opt_lenb = (s->opt_len + 3 + 7) >> 3; static_lenb = (s->static_len + 3 + 7) >> 3;
    opt_lenb := ((← Zlib.Trees.rd s).opt_len + 3 + 7) >>> 3
    static_lenb := ((← Zlib.Trees.rd s).static_len + 3 + 7) >>> 3
    -- if (static_lenb <= opt_lenb || s->strategy == Z_FIXED) opt_lenb = static_lenb;
    if static_lenb ≤ opt_lenb ∨ (← Zlib.Trees.rd s).strategy == Z_FIXED then opt_lenb := static_lenb
  else
    -- opt_lenb = static_lenb = stored_len + 5;
    opt_lenb := stored_len + 5
    static_lenb := stored_len + 5
  if stored_len + 4 ≤ opt_lenb ∧ buf != .null then
    «_tr_stored_block» s buf stored_len last
  else if static_lenb == opt_lenb then
    fixedBlockPayload s last
  else
    send_bits s (← Zlib.Trees.iadd (DYN_TREES <<< 1) last) 3
    send_all_trees s (← Zlib.Trees.iadd (← Zlib.Trees.rd s).l_desc.max_code 1) (← Zlib.Trees.iadd (← Zlib.Trees.rd s).d_desc.max_code 1)
      (← Zlib.Trees.iadd max_blindex 1)
    compress_block s (← pLtree s) (← pDtree s)
  flushBlockTail s last) := by
  rw [Zlib.Trees.Proofs.flush_block_source]
  unfold blockPrepare blockDataType Zlib.Trees.Proofs.blPrepare
  simp only [M_bind_assoc, M_pure_bind, Zlib.Trees.Proofs.merge_ite_bind]

end source

end Zlib.Deflate.Engine.Proofs
