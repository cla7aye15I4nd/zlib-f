import ZlibF.Proof.«trees.c.universal-stored»
import ZlibF.Proof.«trees.c.universal-fixed»
import ZlibF.Proof.«trees.c.universal-dynamic»
import ZlibF.Proof.«deflate.c.engine.flush-default»

/-!
# trees.c: `_tr_flush_block` for every block choice and every memLevel

Batch C of the deflate skeleton. `tr_flush_block_safe` covers the whole function at a positive
level: the data-type hint, the three tree constructions, the cost comparison, and the stored,
fixed and dynamic branches with the common tail. Every branch's output room is derived from the
recorded symbols and `lit_bufsize`. The dynamic branch takes the overlay room of the prepared
trees as a premise (`DynamicOverlay`); `dynamic_overlay_large` proves it for `memLevel ≥ 5`.
For `memLevel` 1 to 4 it is the open lemma of fact F9 (`docs/progress.md`).
-/

namespace Zlib.Deflate.Universal.Block
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs (dynamicHeaderBits)
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateSelection (byteCost selectedCost)
set_option autoImplicit false

/-- The rounded byte cost of the fixed-code block bounds a winning stored block, at any
`lit_bufsize`: its data and its worst six-byte header fit the `4 * lit_bufsize` pending bytes. -/
theorem stored_room_general {capacity symbols : Nat} {bits opt stored : UInt64} {forceFixed : Bool}
    (symbolsFit : symbols + 1 ≤ capacity) (capacityMax : capacity ≤ 32768)
    (budget : bits.toNat ≤ 31 * symbols + 7)
    (storedWord : stored.toNat ≤ 4294967296)
    (selected : stored + 4 ≤ selectedCost opt (byteCost bits) forceFixed) :
    stored.toNat + 6 ≤ 4 * capacity := by
  have first : (bits + 3).toNat = bits.toNat + 3 := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by change bits.toNat + 3 < 18446744073709551616; omega)
  have second : (bits + 3 + 7).toNat = bits.toNat + 10 := by
    rw [UInt64.toNat_add, first]
    exact Nat.mod_eq_of_lt (by change bits.toNat + 3 + 7 < 18446744073709551616; omega)
  have fixedBound : (byteCost bits).toNat = (bits.toNat + 10) / 8 := by
    unfold byteCost
    rw [UInt64.toNat_shiftRight, second]
    change (bits.toNat + 10) >>> 3 = _
    rw [Nat.shiftRight_eq_div_pow]
  have minBound := ZlibF.Math.DeflateSelection.selected_le_fixed opt (byteCost bits) forceFixed
  have add : (stored + 4).toNat = stored.toNat + 4 := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by change stored.toNat + 4 < 18446744073709551616; omega)
  change (stored + 4).toNat ≤ (selectedCost opt (byteCost bits) forceFixed).toNat at selected
  rw [add] at selected
  omega

/-- The overlay room of fact F9 for a dynamic block, as the dynamic branch of
`_tr_flush_block` needs it: on the heap where the trees are built, if the prepared costs select
the dynamic branch, the prepared state has its `DynamicRoom`. -/
def DynamicOverlay (h : Heap) (ds : Nat) (d : DeflateState) (xs : List Symbol) : Prop :=
  ∀ (mb : Int32) (ready : DeflateState),
    (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
      .ok (mb, setD h ds ready) →
    TreePreparationFrame d ready → (dynamicHeaderBits ready mb).length ≤ 2283 →
    1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 6257 * (xs.length + 3) →
    ¬ (byteCost ready.static_len ≤ byteCost ready.opt_len ∨ (ready.strategy == Z_FIXED) = true) →
    DynamicRoom ready mb xs

/-- **F9 for `memLevel ≥ 5`.** With `lit_bufsize ≥ 2048`, a drained entry and the recorded
symbols within the symbol buffer, the overlay room holds for every prepared state. -/
theorem dynamic_overlay_large {h : Heap} {ds : Nat} {d : DeflateState} {xs : List Symbol}
    (large : 2048 ≤ d.lit_bufsize.toNat) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (symbolsFit : xs.length + 1 ≤ d.lit_bufsize.toNat) : DynamicOverlay h ds d xs := by
  intro mb ready _run frame header excess _dynamic
  have same : ready.lit_bufsize = d.lit_bufsize ∧ ready.pending = d.pending ∧
      ready.bi_valid = d.bi_valid := by
    rw [frame]
    exact ⟨rfl, rfl, rfl⟩
  have bitsN : ready.bi_valid.toInt.toNat ≤ 7 := by rw [same.2.2]; omega
  exact dynamic_room_large (by rw [same.1]; exact large) (by rw [same.2.1]; exact pending) bitsN header
    (by rw [same.1]; exact symbolsFit) excess

/-- The value of a valid stored source of `stored_len` bytes: `NULL` (a negative `block_start`),
or a readable slice of a byte block other than `pending_buf`. -/
def StoredSource (h : Heap) (pb : Nat) (source : BPtr) (len : UInt64) : Prop :=
  source = .null ∨ ∃ w off a, source = .ref (.blk w) off ∧ h.bytes w = some a ∧ pb ≠ w ∧
    off + len.toNat ≤ a.size

/-- **`_tr_flush_block` at a positive level, every block choice, every memLevel.** From a
drained entry (`pending = 0`, at most seven held bits, the cursor at the start of `pending_buf`),
the recorded symbols with their frequencies (`SymbolLedger`), cleared costs (`BlockClear`), a
valid stored source of `stored_len ≤ 2^32` bytes and the overlay room of the dynamic branch, the
call does not fault. Afterwards the stream invariants hold, the block is empty and cleared, the
pending bytes lie within `pending_buf`, at most seven bits are held, and none after the last
block. -/
theorem tr_flush_block_safe {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (source : BPtr) (len : UInt64) (sourceOk : StoredSource h pb source len)
    (lenWord : len.toNat ≤ 4294967296)
    (overlay : ∀ z', DynamicOverlay (r.put h z') ds d xs) (last : Bool) :
    ∃ (z' : ZStream) (after : Heap) (result : DeflateState) (next : Array UInt8),
      Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source len (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      StreamAccounting z z' 0 0 ∧ ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      SymbolLedger next result [] ∧ BlockInit.BlockClear result ∧
      next.size = buf.size ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * buf.size ∧
      (last = true → result.bi_valid.toInt = 0) ∧ FlushFrame d result ∧ result.«matches» = 0 := by
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
  have pendingP : prepared.pending = 0 := by rw [record]; exact pending
  have bitsP : prepared.bi_valid.toInt ≤ 7 := by rw [record]; exact bits
  have countP : prepared.sym_next.toNat = 3 * xs.length := by rw [record]; exact ledger.count
  have packedP : PackedSymbols buf prepared.lit_bufsize.toNat xs := by rw [record]; exact ledger.packed
  have capacity : xs.length + 1 ≤ d.lit_bufsize.toNat := by
    have bound := trees.run.sym_next_le
    rw [ledger.count, trees.base.sym_end] at bound
    have low := trees.base.lit_lo
    omega
  have sizeBuf : buf.size = 4 * d.lit_bufsize.toNat := trees.base.size
  by_cases chooseStored : len + (4 : UInt64) ≤
      selectedCost (byteCost prepared.opt_len) (byteCost prepared.static_len) (prepared.strategy == Z_FIXED) ∧
      source != .null
  · -- stored
    have nonnull : source ≠ .null := by
      intro isNull
      have := chooseStored.2
      rw [isNull] at this
      simp at this
    obtain ⟨w, off, a, rfl, get, separate, input⟩ := sourceOk.resolve_left nonnull
    have room := stored_room_general capacity trees.base.lit_hi budget lenWord chooseStored.1
    obtain ⟨after, result, next, run, goodA, treesA, buffersA, sizesA, storageA,
      ledgerA, clearA, size, bound, cursorA, aligned, frameA, matchesA⟩ :=
      stored_block_safe (ob := ob) goodP treesP buffersP cursorP pendingP bitsP
        (by simpa only [setD_bytes, ZStreamRef.put_bytes] using get) separate len input
        (by rw [sizeBuf]; exact room) last
    have dispatch := flush_stored_dispatch good positive prepare goodP
      (.ref (.blk w) off) (by intro no; cases no) len (if last then 1 else 0) chooseStored.1
    refine ⟨z', after, result, next, dispatch.trans run, goodA, treesA, buffersA, account,
      sizesZ.trans (sizesP.trans sizesA), storageZ.trans (storageP.trans storageA), ledgerA, clearA,
      size, cursorA, ?_, fun _ => aligned, (FlushFrame.of_preparation fields).trans frameA, matchesA⟩
    rw [aligned, sizeBuf]
    simp only [Int.toNat_zero, Nat.add_zero]
    omega
  · by_cases chooseFixed : byteCost prepared.static_len ≤ byteCost prepared.opt_len ∨
        (prepared.strategy == Z_FIXED) = true
    · -- fixed
      have avoid : ¬ (len + (4 : UInt64) ≤ byteCost prepared.static_len ∧ source != .null) := by
        simpa only [selectedCost, chooseFixed, ite_true] using chooseStored
      obtain ⟨after, result, next, run, goodA, treesA, buffersA, sizesA, storageA,
        ledgerA, frameA, clearA, size, cursorA, bound, final⟩ :=
        fixed_block_safe (ob := ob) goodP treesP buffersP cursorP pendingP bitsP
          countP packedP ledger.valid last
      have dispatch := flush_fixed_selected_dispatch good positive prepare goodP source
        len (if last then 1 else 0) chooseFixed avoid
      have highA := treesA.run.bi_hi
      refine ⟨z', after, result, next, dispatch.trans run, goodA, treesA, buffersA, account,
        sizesZ.trans (sizesP.trans sizesA), storageZ.trans (storageP.trans storageA), ledgerA, clearA,
        size, cursorA, ?_, final, (FlushFrame.of_preparation fields).trans (FlushFrame.of_output frameA),
        by rw [frameA]⟩
      have low := trees.base.lit_lo
      rw [sizeBuf]; omega
    · -- dynamic
      have avoid : ¬ (len + (4 : UInt64) ≤ byteCost prepared.opt_len ∧ source != .null) := by
        simpa only [selectedCost, chooseFixed, ite_false] using chooseStored
      have different : byteCost prepared.static_len ≠ byteCost prepared.opt_len := by
        intro equal
        apply chooseFixed
        left
        rw [equal]
        exact UInt64.le_refl _
      have roomFn : ∀ (mb' : Int32) (ready : DeflateState),
          (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds)))
            (r.put h z') = .ok (mb', setD (r.put h z') ds ready) →
          TreePreparationFrame d ready → (dynamicHeaderBits ready mb').length ≤ 2283 →
          1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 6257 * (xs.length + 3) →
          DynamicRoom ready mb' xs := by
        intro mb' ready run' frame' header' excess'
        have sameReady : ready = prepared := Zlib.Trees.Proofs.same_record_of_runs run' allRun
        subst sameReady
        exact overlay z' mb' ready run' frame' header' excess' chooseFixed
      obtain ⟨after, result, next, emitRun, goodA, treesA, buffersA, sizesA, storageA,
        ledgerA, clearA, size, cursorA, bound, final, frameA, matchesA⟩ :=
        dynamic_block_safe (ob := ob) goodZ treesZ buffersZ cursor ledger clear roomFn last
      unfold dynamicPreparedPayload at emitRun
      have joined : ((do
          Zlib.Trees.Proofs.blPrepare (some (.tab ds))
          Zlib.Trees.build_bl_tree (some (.tab ds))) >>= fun idx => do
            Zlib.Trees.Proofs.dynamicBlockHeader (some (.tab ds)) (if last then 1 else 0) idx
            Zlib.Trees.compress_block (some (.tab ds)) (← Zlib.Trees.pLtree (some (.tab ds)))
              (← Zlib.Trees.pDtree (some (.tab ds)))
            Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0))
          (r.put h z') = .ok ((), after) := by
        simpa only [C.M_bind_assoc] using emitRun
      rw [bind_app, allRun] at joined
      have dispatch := flush_dynamic_dispatch good positive prepare goodP source
        len (if last then 1 else 0) chooseFixed avoid different
      refine ⟨z', after, result, next, dispatch.trans joined, goodA, treesA, buffersA, account,
        sizesZ.trans sizesA, storageZ.trans storageA, ledgerA, clearA, size, cursorA, bound, final, frameA, matchesA⟩

end Zlib.Deflate.Universal.Block
