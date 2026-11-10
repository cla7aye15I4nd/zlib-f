import ZlibF.Proof.«deflate.c.engine.flush-default»

/-! # Actual block selection retains its stored-branch alignment -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt natBits)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateSelection (byteCost selectedCost)
set_option autoImplicit false

/-- The complete actual three-way block dispatch retains the stored branch's
zero held-bit count on the same returned state as its independent grammar.
Both final flags and every actual cost choice are admitted. This sibling
keeps the existing flush theorem and all public specifications unchanged;
it supplies the byte-boundary fact needed to compose subsequent blocks. -/
theorem flush_default_ready_aligned {h : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) :
    ∃ (z' : ZStream) (after : Heap) (result : DeflateState) (next : Array UInt8)
      (kind : Nat) (body padding : List Bool),
      Zlib.Trees.«_tr_flush_block» (some (.tab ds)) (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      SymbolLedger next result [] ∧ BlockInit.BlockClear result ∧
      next.size = 65536 ∧ result.pending.toNat ≤ 63488 ∧ result.pending_out = result.pending_buf ∧
      (last = true → result.bi_valid.toInt = 0) ∧ (kind = 0 → result.bi_valid.toInt = 0) ∧ kind < 3 ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧ (kind = 0 → padding = []) ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (natBits (if last then 1 else 0) 1 ++ natBits kind 2 ++ body ++ padding) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  obtain ⟨z', hint, goodZ, treesZ, buffersZ, account, sizesZ, storageZ, _fieldsZ, _unknown, _known⟩ :=
    block_data_type_engine (ob := ob) good trees buffers
  obtain ⟨mb, prepared, allRun, goodP, treesP, buffersP, sizesP, storageP, fields, _cost, budget⟩ :=
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
  have outputP : Zlib.Trees.Proofs.Out.outBits buf prepared = Zlib.Trees.Proofs.Out.outBits buf d := by rw [record]; rfl
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
    obtain ⟨after, result, next, body, run, goodA, treesA, buffersA, sizesA, storageA,
      ledgerA, clearA, size, bound, cursorA, aligned, output, grammar⟩ :=
      stored_block_ready (ob := ob) goodP treesP buffersP cursorP memoryP pendingP bitsP
        (by rw [record]; exact win) (by simpa only [setD_bytes, ZStreamRef.put_bytes] using get)
        (by rw [record]; exact range) (by rw [record]; exact nonnegative)
        (by rw [record]; exact balance) (by rw [record]; exact accounted)
        (by rw [record]; exact view) room last
    have blockPosition : prepared.block_start = d.block_start := by rw [record]
    rw [blockPosition] at run
    have dispatch := flush_stored_dispatch good positive prepare goodP
      (.ref (.blk w) d.block_start.toInt.toNat) (by intro no; cases no)
      (UInt64.ofNat (represented xs)) (if last then 1 else 0) chooseStored.1
    rw [outputP] at output
    refine ⟨z', after, result, next, 0, body, [], ?_, goodA, treesA, buffersA, account,
      sizesZ.trans (sizesP.trans sizesA), storageZ.trans (storageP.trans storageA), ledgerA, clearA,
      size, bound, cursorA, (by intro _; exact aligned), (by intro _; exact aligned), by decide +kernel, by decide +kernel,
      by simp, (by intro _; rfl), ?_, ?_⟩
    · rw [source]
      exact dispatch.trans run
    · simpa only [Zlib.Trees.Proofs.Out.storedTag_wire, List.append_nil, List.append_assoc] using output
    · intro suffix suffixAligned
      exact grammar suffix (suffixAligned rfl)
  · by_cases chooseFixed : byteCost prepared.static_len ≤ byteCost prepared.opt_len ∨
        (prepared.strategy == Z_FIXED) = true
    · have avoid : ¬ ((UInt64.ofNat (represented xs)) + (4 : UInt64) ≤ byteCost prepared.static_len ∧
          defaultStoredSource d w != .null) := by
        simpa only [selectedCost, chooseFixed, ite_true] using chooseStored
      obtain ⟨after, result, next, body, padding, run, goodA, treesA, buffersA, sizesA, storageA,
        ledgerA, _frame, size, bound, _nonfinal, cursorA, _room, final, padBound, padNone, output, grammar⟩ :=
        fixed_block_ready_frame (ob := ob) goodP treesP buffersP cursorP memoryP pendingP bitsP
          countP packedP ledger.valid trace last
      obtain ⟨clearHeap, clearState, clearRun, clearGood, clearStateData⟩ :=
        fixed_block_clear_execution (ob := ob) goodP treesP buffersP cursorP memoryP pendingP bitsP
          countP packedP ledger.valid last
      have sameHeap : clearHeap = after := (Prod.mk.inj (Except.ok.inj (clearRun.symm.trans run))).2
      rw [sameHeap] at clearGood
      have sameState : clearState = result := Option.some.inj (clearGood.live.hs.symm.trans goodA.live.hs)
      have clearA : BlockInit.BlockClear result := sameState ▸ clearStateData
      have dispatch := flush_fixed_selected_dispatch good positive prepare goodP (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) chooseFixed avoid
      rw [outputP] at output
      refine ⟨z', after, result, next, 1, body, padding, dispatch.trans run, goodA, treesA, buffersA, account,
        sizesZ.trans (sizesP.trans sizesA), storageZ.trans (storageP.trans storageA), ledgerA, clearA,
        size, bound, cursorA, (by intro yes; exact (final yes).1), (by intro equal; cases equal), by decide +kernel, padBound, padNone, (by intro equal; cases equal), ?_, ?_⟩
      · simpa only [Zlib.Trees.Proofs.Out.fixedTag_wire, List.append_assoc] using output
      · intro suffix _aligned
        exact grammar suffix
    · have avoid : ¬ ((UInt64.ofNat (represented xs)) + (4 : UInt64) ≤ byteCost prepared.opt_len ∧
          defaultStoredSource d w != .null) := by
        simpa only [selectedCost, chooseFixed, ite_false] using chooseStored
      have different : byteCost prepared.static_len ≠ byteCost prepared.opt_len := by
        intro equal
        apply chooseFixed
        left
        rw [equal]
        exact Nat.le_refl _
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
      have dispatch := flush_dynamic_dispatch good positive prepare goodP (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) chooseFixed avoid different
      refine ⟨z', after, result, next, 2, body, padding, dispatch.trans joined, goodA, treesA, buffersA, account,
        sizesZ.trans sizesA, storageZ.trans storageA, ledgerA, clearA, size, bound, cursorA,
        (by intro yes; exact (final yes).1), (by intro equal; cases equal), by decide +kernel, padBound, padNone, (by intro equal; cases equal), ?_, ?_⟩
      · simpa only [Zlib.Trees.Proofs.dynamicTag_wire, List.append_assoc] using output
      · intro suffix _aligned
        exact grammar suffix

end Zlib.Deflate.Engine.Proofs
