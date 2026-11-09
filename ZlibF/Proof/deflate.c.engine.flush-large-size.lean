import ZlibF.Proof.«deflate.c.engine.flush-dynamic-size»
import ZlibF.Proof.«deflate.c.engine.fixed-block-size»
import ZlibF.Proof.«deflate.c.engine.fixed-clear»
import ZlibF.Proof.«deflate.c.engine.filtered-static-budget»

/-! # A large filtered block cannot expand when its stored source is unavailable

The short-match quality and large represented size are internal history
obligations. These results do not add them to a public utility domain.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt outBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

private theorem prepare_record_eq {h : Heap} {r : ZStreamRef} {ds : Nat}
    {mb1 mb2 : Int32} {z1 z2 : ZStream} {d1 d2 : DeflateState}
    (first : blockPrepare (some (.tab ds)) h = .ok (mb1, setD (r.put h z1) ds d1))
    (second : blockPrepare (some (.tab ds)) h = .ok (mb2, setD (r.put h z2) ds d2)) : d1 = d2 := by
  have heaps := (Prod.mk.inj (Except.ok.inj (first.symm.trans second))).2
  have states := congrArg (fun heap => heap.dstates ds) heaps
  apply Option.some.inj
  simpa only [setD_dstates_same] using states

/-- Actual preparation installs a fixed rounded cost no larger than the
represented input for a large ledger obeying the real short-match rule.
The observed run is identified with the already proved actual constructor
execution. It is not an assumed constructor specification. -/
theorem block_prepare_large_static_byte_bound {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z z' : ZStream} {d prepared : DeflateState} {buf : Array UInt8} {xs : List Symbol} {mb : Int32}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (memory : d.lit_bufsize.toNat = 16384) (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (large : 32506 ≤ represented xs)
    (observed : blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared)) :
    (((prepared.static_len + 3 + 7) >>> 3)).toNat ≤ represented xs := by
  obtain ⟨otherMb, otherZ, other, run, _goodP, _treesP, _buffersP, _account, _sizes, _storage,
    _fields, exactCost, _budget⟩ :=
    block_prepare_static_budget_engine (ob := 0) good trees buffers ledger clear
  have same : other = prepared := prepare_record_eq run observed
  subst other
  have count : xs.length ≤ 16383 := by
    have extent := trees.base.sym_end
    have used := trees.run.sym_next_le
    have packedCount := ledger.count
    omega
  have original : originalStaticCost d ≤ 31 * xs.length + 7 := ledger_static_cost_budget ledger
  have natural : prepared.static_len.toNat = originalStaticCost d := by
    rw [exactCost, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have first : (prepared.static_len + 3).toNat = originalStaticCost d + 3 := by
    rw [UInt64.toNat_add, natural]
    change (originalStaticCost d + 3) % 18446744073709551616 = _
    exact Nat.mod_eq_of_lt (by omega)
  have second : (prepared.static_len + 3 + 7).toNat = originalStaticCost d + 10 := by
    rw [UInt64.toNat_add, first]
    change (originalStaticCost d + 3 + 7) % 18446744073709551616 = _
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [UInt64.toNat_shiftRight, second]
  change (originalStaticCost d + 10) >>> 3 ≤ _
  rw [Nat.shiftRight_eq_div_pow]
  exact ledger_large_static_no_expansion ledger quality count large

/-- The complete actual dynamic choice with a NULL stored source cannot
expand the rounded byte potential of a large filtered block. The data-type
hint, constructors, all source comparisons, writer, reset and alignment
are included. Whole histories must establish the two quality/size facts. -/
theorem flush_large_dynamic_byte_count {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (large : 32506 ≤ represented xs) (last : Bool) :
    ∃ (mb : Int32) (z' : ZStream) (prepared : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) ∧
      (¬ (((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∨
          (prepared.strategy == Z_FIXED) = true) →
        ∃ after result next,
          Zlib.Trees.«_tr_flush_block» (some (.tab ds)) .null (UInt64.ofNat (represented xs))
            (if last then 1 else 0) h = .ok ((), after) ∧
          DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧
          ((outBits next result).length + 7) / 8 ≤ ((outBits buf d).length + 7) / 8 + represented xs) := by
  obtain ⟨mb, z', prepared, prepare, selected⟩ := flush_dynamic_prepared_byte_cost
    good trees buffers positive cursor memory pending bits ledger clear .null (UInt64.ofNat (represented xs)) last
  have fixed := block_prepare_large_static_byte_bound good trees buffers memory ledger clear quality large prepare
  refine ⟨mb, z', prepared, prepare, ?_⟩
  intro prefer
  have avoid : ¬ (UInt64.ofNat (represented xs) + (4 : UInt64) ≤
      ((prepared.opt_len + 3 + 7) >>> 3) ∧ ((.null : BPtr) != .null) = true) := by simp
  obtain ⟨after, result, next, run, goodA, treesA, bound, _final⟩ := selected prefer avoid
  have smaller : ¬ ((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) :=
    fun yes => prefer (Or.inl yes)
  change ¬ (((prepared.static_len + 3 + 7) >>> 3)).toNat ≤
    (((prepared.opt_len + 3 + 7) >>> 3)).toNat at smaller
  exact ⟨after, result, next, run, goodA, treesA, by omega⟩

/-- The complete actual fixed choice with a NULL stored source has the
same non-expansion bound. Forced fixed coding is included. These remain
explicit internal quality/size cutpoint facts, not public preconditions. -/
theorem flush_large_fixed_byte_count {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (quality : ∀ s ∈ xs, s.distance ≠ 0 → s.value = 0 → s.distance ≤ 4096)
    (large : 32506 ≤ represented xs) (last : Bool) :
    ∃ (mb : Int32) (z' : ZStream) (prepared : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) ∧
      ((((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∨
          (prepared.strategy == Z_FIXED) = true) →
        ∃ after result next,
          Zlib.Trees.«_tr_flush_block» (some (.tab ds)) .null (UInt64.ofNat (represented xs))
            (if last then 1 else 0) h = .ok ((), after) ∧
          DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧
          ((outBits next result).length + 7) / 8 ≤ ((outBits buf d).length + 7) / 8 + represented xs) := by
  obtain ⟨mb, z', prepared, prepare, goodP, treesP, buffersP, _account, _sizes, _storage,
    fields, _exactCost, _budget⟩ :=
    block_prepare_static_budget_engine (ob := 0) good trees buffers ledger clear
  refine ⟨mb, z', prepared, prepare, ?_⟩
  intro prefer
  have record := fields
  unfold TreePreparationFrame at record
  obtain ⟨after, result, next, run, goodA, treesA, bound, _final⟩ := fixed_block_byte_count
    goodP treesP buffersP (by rw [record]; exact cursor) (by rw [record]; exact memory)
    (by rw [record]; exact pending) (by rw [record]; exact bits)
    (by rw [record]; exact ledger.count) (by rw [record]; exact ledger.packed) ledger.valid last
  have count : xs.length ≤ 16383 := by
    have extent := trees.base.sym_end
    have used := trees.run.sym_next_le
    have packedCount := ledger.count
    omega
  have fixedBound : (fixedWireCost xs + 10) / 8 ≤ represented xs := by
    rw [← ledger_static_wire_cost ledger]
    exact ledger_large_static_no_expansion ledger quality count large
  have dispatch := flush_fixed_selected_dispatch good positive prepare goodP .null (UInt64.ofNat (represented xs))
    (if last then 1 else 0) prefer (by simp)
  have prior : outBits buf prepared = outBits buf d := by rw [record]; rfl
  rw [prior] at bound
  exact ⟨after, result, next, dispatch.trans run, goodA, treesA, by omega⟩

end Zlib.Deflate.Engine.Proofs
