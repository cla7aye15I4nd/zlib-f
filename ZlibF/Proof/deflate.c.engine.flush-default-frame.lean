import ZlibF.Proof.«deflate.c.engine.flush-frame»

/-! # Every real default-memory flush choice preserves the input-history fields -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateSelection (byteCost selectedCost)
set_option autoImplicit false

/-- The actual unrestricted flush has the exact record footprint needed
to retain window/hash/input history through all computed encoding choices.
Called-function frames below are established by their actual executions. -/
theorem flush_default_frame_execution {h : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) :
    ∃ (z' : ZStream) (after : Heap) (result : DeflateState) (next : Array UInt8),
      Zlib.Trees.«_tr_flush_block» (some (.tab ds)) (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      FlushWorkFrame d result := by
  obtain ⟨z', hint, goodZ, treesZ, buffersZ, _account, _sizesZ, _storageZ, _fieldsZ, _unknown, _known⟩ :=
    block_data_type_engine (ob := ob) good trees buffers
  obtain ⟨mb, prepared, allRun, goodP, treesP, buffersP, _sizesP, _storageP, fields, _cost, budget⟩ :=
    all_trees_static_budget_engine (ob := ob) goodZ treesZ buffersZ ledger clear
  have prepare : blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) := by
    unfold blockPrepare
    rw [bind_app, hint]
    exact allRun
  have record := fields
  unfold TreePreparationFrame at record
  have cursorP : prepared.pending_out = prepared.pending_buf := by rw [record]; exact cursor
  have memoryP : prepared.lit_bufsize.toNat = 16384 := by rw [record]; exact memory
  have pendingP : prepared.pending = 0 := by rw [record]; exact pending
  have bitsP : prepared.bi_valid.toInt ≤ 7 := by rw [record]; exact bits
  have countP : prepared.sym_next.toNat = 3 * xs.length := by rw [record]; exact ledger.count
  have packedP : PackedSymbols buf prepared.lit_bufsize.toNat xs := by rw [record]; exact ledger.packed
  by_cases chooseStored : (UInt64.ofNat (represented xs)) + (4 : UInt64) ≤
      selectedCost (byteCost prepared.opt_len) (byteCost prepared.static_len) (prepared.strategy == Z_FIXED) ∧
      defaultStoredSource d w != .null
  · have nonnegative : 0 ≤ d.block_start.toInt := by
      by_cases yes : 0 ≤ d.block_start.toInt
      · exact yes
      · have impossible := chooseStored.2
        simp only [defaultStoredSource, yes, ite_false, bne_self_eq_false, Bool.false_eq_true] at impossible
    have source : defaultStoredSource d w = .ref (.blk w) d.block_start.toInt.toNat := if_pos nonnegative
    have end_ := trees.base.sym_end
    have symbols := ledger.count
    have countBound : xs.length ≤ 16383 := by have := trees.run.sym_next_le; omega
    have byteBound := represented_le ledger.valid
    have natural : (UInt64.ofNat (represented xs)).toNat = represented xs := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    have room := ZlibF.Math.DeflateSelection.stored_default_room countBound budget
      (stored := UInt64.ofNat (represented xs)) (by rw [natural]; omega) chooseStored.1
    rw [natural] at room
    obtain ⟨after, result, next, run, goodA, treesA, buffersA, frameA⟩ :=
      stored_block_frame_execution (ob := ob) goodP treesP buffersP cursorP memoryP pendingP bitsP
        (by rw [record]; exact win) (by simpa only [setD_bytes, ZStreamRef.put_bytes] using get)
        (by rw [record]; exact range) (by rw [record]; exact nonnegative)
        (by rw [record]; exact balance) (by rw [record]; exact accounted)
        (by rw [record]; exact view) room last
    have blockPosition : prepared.block_start = d.block_start := by rw [record]
    rw [blockPosition] at run
    have dispatch := flush_stored_dispatch good positive prepare goodP
      (.ref (.blk w) d.block_start.toInt.toNat) (by intro no; cases no)
      (UInt64.ofNat (represented xs)) (if last then 1 else 0) chooseStored.1
    refine ⟨z', after, result, next, ?_, goodA, treesA, buffersA, (FlushWorkFrame.prepare fields).trans frameA⟩
    rw [source]
    exact dispatch.trans run
  · by_cases chooseFixed : byteCost prepared.static_len ≤ byteCost prepared.opt_len ∨
        (prepared.strategy == Z_FIXED) = true
    · have avoid : ¬ ((UInt64.ofNat (represented xs)) + (4 : UInt64) ≤ byteCost prepared.static_len ∧
          defaultStoredSource d w != .null) := by
        simpa only [selectedCost, chooseFixed, ite_true] using chooseStored
      obtain ⟨after, result, next, body, padding, run, goodA, treesA, buffersA, _sizesA, _storageA,
        _ledgerA, frameA, _size, _bound, _nonfinal, _cursorA, _room, _final, _padBound, _padNone, _output, _grammar⟩ :=
        fixed_block_ready_frame (ob := ob) goodP treesP buffersP cursorP memoryP pendingP bitsP
          countP packedP ledger.valid trace last
      have dispatch := flush_fixed_selected_dispatch good positive prepare goodP (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) chooseFixed avoid
      exact ⟨z', after, result, next, dispatch.trans run, goodA, treesA, buffersA,
        (FlushWorkFrame.prepare fields).trans (FlushWorkFrame.block frameA)⟩
    · have avoid : ¬ ((UInt64.ofNat (represented xs)) + (4 : UInt64) ≤ byteCost prepared.opt_len ∧
          defaultStoredSource d w != .null) := by
        simpa only [selectedCost, chooseFixed, ite_false] using chooseStored
      have different : byteCost prepared.static_len ≠ byteCost prepared.opt_len := by
        intro equal
        apply chooseFixed
        left
        rw [equal]
        exact Nat.le_refl _
      obtain ⟨after, result, next, emitRun, goodA, treesA, buffersA, frameA⟩ :=
        dynamic_block_frame_execution (ob := ob) goodZ treesZ buffersZ cursor memory pending bits ledger clear last
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
      have dispatch := flush_dynamic_dispatch good positive prepare goodP (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) chooseFixed avoid different
      exact ⟨z', after, result, next, dispatch.trans joined, goodA, treesA, buffersA, frameA⟩

/-- Determinism transfers the independently proved actual frame to any
already established successful flush run and its live returned record. -/
theorem flush_default_run_frame {h after : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d result : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool)
    (run : Zlib.Trees.«_tr_flush_block» (some (.tab ds)) (defaultStoredSource d w)
      (UInt64.ofNat (represented xs)) (if last then 1 else 0) h = .ok ((), after))
    (live : after.dstates ds = some result) : FlushWorkFrame d result := by
  obtain ⟨z', frameHeap, frameState, next, frameRun, frameGood, _trees, _buffers, frame⟩ :=
    flush_default_frame_execution (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  have sameHeap : frameHeap = after := (Prod.mk.inj (Except.ok.inj (frameRun.symm.trans run))).2
  rw [sameHeap] at frameGood
  have sameState : frameState = result := Option.some.inj (frameGood.live.hs.symm.trans live)
  rw [← sameState]
  exact frame

end Zlib.Deflate.Engine.Proofs
