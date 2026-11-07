import ZlibF.Proof.«deflate.c.engine.block-prepare»
import ZlibF.Proof.«deflate.c.engine.dynamic-block»

/-! # Actual positive-level flush dispatch to constructed dynamic coding -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Whole-function equality retains actual preparation and cost selection
while naming the already checked dynamic-header fragment. -/
theorem flush_block_dynamic_prepare_source (s : DeflateStatePtr) (buf : BPtr) (stored_len : UInt64) (last : Int32) :
    Zlib.Trees.«_tr_flush_block» s buf stored_len last = (do
  let mut max_blindex : Int32 := 0
  let mut opt_lenb : UInt64 := 0
  let mut static_lenb : UInt64 := 0
  if (← Zlib.Trees.rd s).level.toInt > 0 then
    max_blindex ← blockPrepare s
    opt_lenb := ((← Zlib.Trees.rd s).opt_len + 3 + 7) >>> 3
    static_lenb := ((← Zlib.Trees.rd s).static_len + 3 + 7) >>> 3
    if static_lenb ≤ opt_lenb ∨ (← Zlib.Trees.rd s).strategy == Z_FIXED then opt_lenb := static_lenb
  else
    opt_lenb := stored_len + 5
    static_lenb := stored_len + 5
  if stored_len + 4 ≤ opt_lenb ∧ buf != .null then
    Zlib.Trees.«_tr_stored_block» s buf stored_len last
  else if static_lenb == opt_lenb then
    Zlib.Trees.Proofs.fixedBlockPayload s last
  else
    Zlib.Trees.Proofs.dynamicBlockHeader s last max_blindex
    Zlib.Trees.compress_block s (← Zlib.Trees.pLtree s) (← Zlib.Trees.pDtree s)
  Zlib.Trees.Proofs.flushBlockTail s last) := by
  rw [Zlib.Trees.Proofs.flush_block_dynamic_header_source]
  unfold blockPrepare blockDataType Zlib.Trees.Proofs.blPrepare
  simp only [M_bind_assoc, M_pure_bind, Zlib.Trees.Proofs.merge_ite_bind]

/-- If the actual rounded costs choose neither stored nor fixed coding,
the full translated flush reaches its original dynamic header/payload and
common tail on the computed prepared heap. -/
theorem flush_dynamic_dispatch {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d prepared : DeflateState} {mb : Int32}
    (good : DGood h r ds z d) (positive : 0 < d.level.toInt)
    (run : blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared))
    (after : DGood (setD (r.put h z') ds prepared) r ds z' prepared)
    (source : BPtr) (stored : UInt64) (last : Int32)
    (prefer : ¬ (((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∨
      (prepared.strategy == Z_FIXED) = true))
    (avoid : ¬ (stored + (4 : UInt64) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∧ source != .null))
    (dynamic : ((prepared.static_len + 3 + 7) >>> 3) ≠ ((prepared.opt_len + 3 + 7) >>> 3)) :
    Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored last h =
      (do Zlib.Trees.Proofs.dynamicBlockHeader (some (.tab ds)) last mb
          Zlib.Trees.compress_block (some (.tab ds)) (← Zlib.Trees.pLtree (some (.tab ds)))
            (← Zlib.Trees.pDtree (some (.tab ds)))
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) last) (setD (r.put h z') ds prepared) := by
  rw [flush_block_dynamic_prepare_source]
  simp only [bind_app, pure_app, Zlib.Trees.Proofs.Out.rd_run good.live.hs,
    positive, ite_true, run, Zlib.Trees.Proofs.Out.rd_run after.live.hs,
    prefer, ite_false, avoid, show ((((prepared.static_len + 3 + 7) >>> 3) ==
      ((prepared.opt_len + 3 + 7) >>> 3))) = false from beq_eq_false_iff_ne.mpr dynamic,
    Bool.false_eq_true]

/-- `void ZLIB_INTERNAL _tr_flush_block(deflate_state *s, charf *buf, ulg stored_len, int last)`.
Actual hint detection, all constructors, rounded-cost tests, the dynamic
writer and the common reset/final-alignment tail compose on one heap.
Independent payload meaning and all room bounds derive from the original
real ledger and cleared-block data. The result is conditional only on the
actual returned costs selecting this source branch. -/
theorem flush_dynamic_prepared {h : Heap} {r : ZStreamRef} {ds pb ob base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (source : BPtr) (stored : UInt64) (last : Bool) :
    ∃ (mb : Int32) (z' : ZStream) (prepared : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) ∧
      TreePreparationFrame d prepared ∧
      (¬ (((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∨
          (prepared.strategy == Z_FIXED) = true) →
        ¬ (stored + (4 : UInt64) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∧ source != .null) →
        ((prepared.static_len + 3 + 7) >>> 3) ≠ ((prepared.opt_len + 3 + 7) >>> 3) →
        ∃ after result next body padding,
          Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored (if last then 1 else 0) h = .ok ((), after) ∧
          DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
          StreamAccounting z z' 0 0 ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
          SymbolLedger next result [] ∧ BlockInit.BlockClear result ∧
          next.size = 65536 ∧ result.pending.toNat ≤ 63488 ∧ result.pending_out = result.pending_buf ∧
          (last = true → result.bi_valid.toInt = 0 ∧ result.bi_buf = 0) ∧
          padding.length < 8 ∧ (last = false → padding = []) ∧
          Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
            (Zlib.Trees.Proofs.dynamicTag last ++ body ++ padding) ∧
          ∀ suffix, ZlibF.Spec.Body [] 2 (inputPrefix input base) (body ++ suffix) suffix
            (inputPrefix input (base + represented xs))) := by
  obtain ⟨z', hint, goodZ, treesZ, buffersZ, account, sizesZ, storageZ, _fieldsZ, _unknown, _known⟩ :=
    block_data_type_engine (ob := ob) good trees buffers
  obtain ⟨mb, literal, ready, scanned, built, prepared, B, allRun, goodP, _treesP, _buffersP,
    _sizesP, _storageP, _input, frameL, frameD, scans, blFrame, finish, _lower, _upper, _guards, _codes, _output⟩ :=
    all_trees_engine (ob := ob) goodZ treesZ buffersZ
  have prepare : blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) := by
    unfold blockPrepare
    rw [bind_app, hint]
    exact allRun
  refine ⟨mb, z', prepared, prepare, all_tree_frames frameL frameD scans blFrame finish, ?_⟩
  intro prefer avoid dynamic
  obtain ⟨after, result, next, body, padding, emitRun, goodA, treesA, buffersA, sizesA, storageA,
    ledgerA, clearA, size, bound, cursorA, _room, final, padBound, padNone, output, grammar⟩ :=
    dynamic_prepared_block_ready (ob := ob) goodZ treesZ buffersZ cursor memory pending bits ledger clear trace last
  unfold dynamicPreparedPayload at emitRun
  have joined : ((do
      Zlib.Trees.Proofs.blPrepare (some (.tab ds))
      Zlib.Trees.build_bl_tree (some (.tab ds))) >>= fun idx => do
        Zlib.Trees.Proofs.dynamicBlockHeader (some (.tab ds)) (if last then 1 else 0) idx
        Zlib.Trees.compress_block (some (.tab ds)) (← Zlib.Trees.pLtree (some (.tab ds)))
          (← Zlib.Trees.pDtree (some (.tab ds)))
        Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0))
      (r.put h z') = .ok ((), after) := by
    simpa only [M_bind_assoc] using emitRun
  rw [bind_app, allRun] at joined
  have sourceRun := flush_dynamic_dispatch good positive prepare goodP source stored (if last then 1 else 0)
    prefer avoid dynamic
  exact ⟨after, result, next, body, padding, sourceRun.trans joined, goodA, treesA, buffersA,
    account, sizesZ.trans sizesA, storageZ.trans storageA, ledgerA, clearA, size, bound, cursorA,
    final, padBound, padNone, output, grammar⟩

end Zlib.Deflate.Engine.Proofs
