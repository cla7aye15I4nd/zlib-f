import ZlibF.Proof.«deflate.c.engine.stored-block»

/-! # Complete actual flush execution when computed costs select stored bytes -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt storedTag)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateSelection (byteCost selectedCost)
set_option autoImplicit false

/-- Actual positive-level preparation and both possible byte-cost choices
dispatch to the original stored writer when its real comparison wins. -/
theorem flush_stored_dispatch {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d prepared : DeflateState} {mb : Int32}
    (good : DGood h r ds z d) (positive : 0 < d.level.toInt)
    (run : blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared))
    (after : DGood (setD (r.put h z') ds prepared) r ds z' prepared)
    (source : BPtr) (nonnull : source ≠ .null) (stored : UInt64) (last : Int32)
    (selected : stored + (4 : UInt64) ≤ selectedCost (byteCost prepared.opt_len)
      (byteCost prepared.static_len) (prepared.strategy == Z_FIXED)) :
    Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored last h =
      (do Zlib.Trees.«_tr_stored_block» (some (.tab ds)) source stored last
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) last) (setD (r.put h z') ds prepared) := by
  rw [flush_block_prepare_source]
  simp only [bind_app, pure_app, Zlib.Trees.Proofs.Out.rd_run good.live.hs,
    positive, ite_true, run, Zlib.Trees.Proofs.Out.rd_run after.live.hs]
  unfold selectedCost byteCost at selected
  split at selected <;> rename_i prefer <;>
    simp only [prefer, ite_true, ite_false, selected, show (source != .null) = true from bne_iff_ne.mpr nonnull,
      and_self, bind_app]

/-- `void ZLIB_INTERNAL _tr_flush_block(deflate_state *s, charf *buf, ulg stored_len, int last)`.
All hint statements and three actual constructors run first. If their real
computed comparison selects stored coding, the complete flush executes,
derives its own pending-space bound, resets the symbol ledger and counters,
and independently decodes to the next accepted input prefix. The strategy
must still establish these flush-cutpoint data and the actual source
pointer/length expressions through every flushing branch. -/
theorem flush_stored_prepared {h : Heap} {r : ZStreamRef} {ds pb ob w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (nonnegative : 0 ≤ d.block_start.toInt)
    (balance : BlockBalance d xs 0) (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) :
    ∃ (mb : Int32) (z' : ZStream) (prepared : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) ∧
      TreePreparationFrame d prepared ∧
      ((UInt64.ofNat (represented xs)) + (4 : UInt64) ≤
        selectedCost (byteCost prepared.opt_len) (byteCost prepared.static_len) (prepared.strategy == Z_FIXED) →
        ∃ after result next body,
          Zlib.Trees.«_tr_flush_block» (some (.tab ds)) (.ref (.blk w) d.block_start.toInt.toNat)
            (UInt64.ofNat (represented xs)) (if last then 1 else 0) h = .ok ((), after) ∧
          DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
          StreamAccounting z z' 0 0 ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
          SymbolLedger next result [] ∧ BlockInit.BlockClear result ∧
          next.size = 65536 ∧ result.pending.toNat ≤ 63488 ∧ result.pending_out = result.pending_buf ∧
          result.bi_valid.toInt = 0 ∧
          Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++ (storedTag last ++ body) ∧
          ∀ suffix : List Bool, suffix.length % 8 = 0 →
            ZlibF.Spec.Body [] 0 (inputPrefix input base) (body ++ suffix) suffix
              (inputPrefix input (base + represented xs))) := by
  obtain ⟨mb, z', prepared, prepare, goodP, treesP, buffersP, account, sizesP, storageP,
    fields, _exactCost, budget⟩ := block_prepare_static_budget_engine (ob := ob) good trees buffers ledger clear
  refine ⟨mb, z', prepared, prepare, fields, ?_⟩
  intro selected
  have end_ := trees.base.sym_end
  have symbols := ledger.count
  have countBound : xs.length ≤ 16383 := by have := trees.run.sym_next_le; omega
  have byteBound := represented_le ledger.valid
  have natural : (UInt64.ofNat (represented xs)).toNat = represented xs := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have room := ZlibF.Math.DeflateSelection.stored_default_room countBound budget
    (stored := UInt64.ofNat (represented xs)) (by rw [natural]; omega) selected
  rw [natural] at room
  have record := fields
  unfold TreePreparationFrame at record
  obtain ⟨after, result, next, body, run, goodA, treesA, buffersA, sizesA, storageA,
    ledgerA, clearA, size, bound, cursorA, aligned, output, grammar⟩ :=
    stored_block_ready (ob := ob) goodP treesP buffersP
      (by rw [record]; exact cursor) (by rw [record]; exact memory)
      (by rw [record]; exact pending) (by rw [record]; exact bits)
      (by rw [record]; exact win) (by simpa only [setD_bytes, ZStreamRef.put_bytes] using get)
      (by rw [record]; exact range) (by rw [record]; exact nonnegative)
      (by rw [record]; exact balance) (by rw [record]; exact accounted)
      (by rw [record]; exact view) room last
  have blockPosition : prepared.block_start = d.block_start := by rw [record]
  rw [blockPosition] at run
  have sourceRun := flush_stored_dispatch good positive prepare goodP
    (.ref (.blk w) d.block_start.toInt.toNat) (by intro no; cases no)
    (UInt64.ofNat (represented xs)) (if last then 1 else 0) selected
  have outputP : Zlib.Trees.Proofs.Out.outBits buf prepared = Zlib.Trees.Proofs.Out.outBits buf d := by
    rw [record]
    rfl
  rw [outputP] at output
  exact ⟨after, result, next, body, sourceRun.trans run, goodA, treesA, buffersA, account,
    sizesP.trans sizesA, storageP.trans storageA, ledgerA, clearA, size, bound, cursorA, aligned, output, grammar⟩

end Zlib.Deflate.Engine.Proofs
