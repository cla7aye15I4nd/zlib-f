import ZlibF.Proof.«deflate.c.engine.flush-large-size»
import ZlibF.Proof.«deflate.c.engine.stored-block-size»
import ZlibF.Proof.«deflate.c.engine.flush-stored»
import ZlibF.Proof.«deflate.c.engine.decision-size-history»

/-! # One tight bound for every actual default block choice -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt outBits)
open ZlibF.Math.DeflateSymbols
open ZlibF.Math.DeflateSelection (byteCost selectedCost)
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem prepare_unique {h : Heap} {r : ZStreamRef} {ds : Nat}
    {mb1 mb2 : Int32} {z1 z2 : ZStream} {d1 d2 : DeflateState}
    (first : blockPrepare (some (.tab ds)) h = .ok (mb1, setD (r.put h z1) ds d1))
    (second : blockPrepare (some (.tab ds)) h = .ok (mb2, setD (r.put h z2) ds d2)) : d1 = d2 := by
  have heaps := (Prod.mk.inj (Except.ok.inj (first.symm.trans second))).2
  have states := congrArg (fun heap => heap.dstates ds) heaps
  apply Option.some.inj
  simpa only [setD_dstates_same] using states

/-- Every real block choice adds at most represented bytes plus five to
the rounded bit potential. The quality and negative-source floor are
internal loop facts established by actual initialization and maintained
by the complete slow loop. Both final flags are covered. This theorem
does not yet accumulate block counts or bound a public utility run. -/
theorem flush_default_byte_count {h : Heap} {r : ZStreamRef} {ds pb w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (strategy : d.strategy = Z_DEFAULT_STRATEGY)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (floor : StoredSourceFloor d)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) :
    ∃ z' after result next,
      Zlib.Trees.«_tr_flush_block» (some (.tab ds)) (defaultStoredSource d w)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧
      ((outBits next result).length + 7) / 8 ≤ ((outBits buf d).length + 7) / 8 + represented xs + 5 := by
  obtain ⟨mb, z', prepared, prepare, goodP, treesP, buffersP, _account, _sizes, _storage,
    fields, _exactCost, budget⟩ := block_prepare_static_budget_engine (ob := 0) good trees buffers ledger clear
  have record := fields
  unfold TreePreparationFrame at record
  have cursorP : prepared.pending_out = prepared.pending_buf := by rw [record]; exact cursor
  have memoryP : prepared.lit_bufsize.toNat = 16384 := by rw [record]; exact memory
  have pendingP : prepared.pending = 0 := by rw [record]; exact pending
  have bitsP : prepared.bi_valid.toInt ≤ 7 := by rw [record]; exact bits
  have original : outBits buf prepared = outBits buf d := by rw [record]; rfl
  have notForced : (prepared.strategy == Z_FIXED) = false := by rw [record, strategy]; rfl
  by_cases nonnegative : 0 ≤ d.block_start.toInt
  · have source : defaultStoredSource d w = .ref (.blk w) d.block_start.toInt.toNat := if_pos nonnegative
    have nonnull : defaultStoredSource d w != .null := by rw [source]; rfl
    by_cases stored : UInt64.ofNat (represented xs) + (4 : UInt64) ≤
        selectedCost (byteCost prepared.opt_len) (byteCost prepared.static_len) (prepared.strategy == Z_FIXED)
    · have count : xs.length ≤ 16383 := by
        have extent := trees.base.sym_end
        have used := trees.run.sym_next_le
        have packedCount := ledger.count
        omega
      have byteBound := represented_le ledger.valid
      have natural : (UInt64.ofNat (represented xs)).toNat = represented xs := by
        rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
      have room := ZlibF.Math.DeflateSelection.stored_default_room count budget
        (stored := UInt64.ofNat (represented xs)) (by rw [natural]; omega) stored
      rw [natural] at room
      obtain ⟨after, result, next, emit, goodA, treesA, bound⟩ := stored_block_byte_count
        goodP treesP buffersP cursorP memoryP pendingP bitsP (by rw [record]; exact win)
        (by simpa only [setD_bytes, ZStreamRef.put_bytes] using get)
        (by rw [record]; exact range) (by rw [record]; exact nonnegative)
        (by rw [record]; exact balance) (by rw [record]; exact accounted)
        (by rw [record]; exact view) room last
      have position : prepared.block_start = d.block_start := by rw [record]
      rw [position] at emit
      have dispatch := flush_stored_dispatch good positive prepare goodP
        (.ref (.blk w) d.block_start.toInt.toNat) (by intro no; cases no)
        (UInt64.ofNat (represented xs)) (if last then 1 else 0) stored
      exact ⟨z', after, result, next, by rw [source]; exact dispatch.trans emit, goodA, treesA,
        by rwa [original] at bound⟩
    · by_cases fixed : byteCost prepared.static_len ≤ byteCost prepared.opt_len
      · obtain ⟨mb2, z2, p2, prep2, _cost, selected⟩ := flush_fixed_prepared_byte_count
          good trees buffers positive cursor memory pending bits ledger clear (defaultStoredSource d w) nonnull last
        have same := prepare_unique prep2 prepare
        subst p2
        have avoid : ¬ (UInt64.ofNat (represented xs) + (4 : UInt64) ≤ byteCost prepared.static_len ∧
            defaultStoredSource d w != .null) := by
          intro yes
          apply stored
          simpa only [selectedCost, notForced, Bool.false_eq_true, or_false, fixed, ite_true] using yes.1
        obtain ⟨after, result, next, run, goodA, treesA, bound⟩ := selected fixed avoid
        exact ⟨z2, after, result, next, run, goodA, treesA, by omega⟩
      · obtain ⟨mb2, z2, p2, prep2, selected⟩ := flush_dynamic_prepared_byte_count
          good trees buffers positive cursor memory pending bits ledger clear (defaultStoredSource d w) nonnull last
        have same := prepare_unique prep2 prepare
        subst p2
        have prefer : ¬ (byteCost prepared.static_len ≤ byteCost prepared.opt_len ∨
            (prepared.strategy == Z_FIXED) = true) := by simp only [notForced, Bool.false_eq_true, or_false]; exact fixed
        have avoid : ¬ (UInt64.ofNat (represented xs) + (4 : UInt64) ≤ byteCost prepared.opt_len ∧
            defaultStoredSource d w != .null) := by
          intro yes
          apply stored
          simpa only [selectedCost, prefer, ite_false] using yes.1
        obtain ⟨after, result, next, run, goodA, treesA, bound⟩ := selected prefer avoid
        exact ⟨z2, after, result, next, run, goodA, treesA, by omega⟩
  · have source : defaultStoredSource d w = .null := if_neg nonnegative
    have large : 32506 ≤ represented xs := represented_large_of_source_floor floor balance (by omega)
    by_cases fixed : byteCost prepared.static_len ≤ byteCost prepared.opt_len ∨ (prepared.strategy == Z_FIXED) = true
    · obtain ⟨mb2, z2, p2, prep2, selected⟩ := flush_large_fixed_byte_count
        good trees buffers positive cursor memory pending bits ledger clear quality large last
      have same := prepare_unique prep2 prepare
      subst p2
      obtain ⟨after, result, next, run, goodA, treesA, bound⟩ := selected fixed
      exact ⟨z2, after, result, next, by rwa [source], goodA, treesA, by omega⟩
    · obtain ⟨mb2, z2, p2, prep2, selected⟩ := flush_large_dynamic_byte_count
        good trees buffers positive cursor memory pending bits ledger clear quality large last
      have same := prepare_unique prep2 prepare
      subst p2
      obtain ⟨after, result, next, run, goodA, treesA, bound⟩ := selected fixed
      exact ⟨z2, after, result, next, by rwa [source], goodA, treesA, by omega⟩

end Zlib.Deflate.Engine.Proofs
