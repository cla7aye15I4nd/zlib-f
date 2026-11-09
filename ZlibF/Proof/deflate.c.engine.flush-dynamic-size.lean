import ZlibF.Proof.«deflate.c.engine.dynamic-block-size»
import ZlibF.Proof.«deflate.c.engine.flush-dynamic»

/-! # The complete real dynamic choice retains its computed byte bound -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt outBits outBits_length)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false
set_option maxRecDepth 10000

/-- `void ZLIB_INTERNAL _tr_flush_block(deflate_state *s, charf *buf,
ulg stored_len, int last)`.
The real data-type hint, preparation, dynamic choice, writer, reset and
final alignment retain exactly the byte estimate compared by the source.
The counter additions do not wrap: this follows from the real writer's
room and bit-count result, rather than an extra cost premise.
This is a conditional internal branch result, before publication. -/
theorem flush_dynamic_prepared_byte_cost {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (source : BPtr) (stored : UInt64) (last : Bool) :
    ∃ (mb : Int32) (z' : ZStream) (prepared : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) ∧
      (¬ (((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∨
          (prepared.strategy == Z_FIXED) = true) →
        ¬ (stored + (4 : UInt64) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∧ source != .null) →
        ∃ after result next,
          Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source stored (if last then 1 else 0) h = .ok ((), after) ∧
          DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧
          ((outBits next result).length + 7) / 8 ≤ ((outBits buf d).length + 7) / 8 +
            (((prepared.opt_len + 3 + 7) >>> 3)).toNat ∧
          (last = true → result.bi_valid.toInt = 0)) := by
  obtain ⟨z', hint, goodZ, treesZ, buffersZ, _accountZ, _sizesZ, _storageZ, _fieldsZ, _unknown, _known⟩ :=
    block_data_type_engine (ob := 0) good trees buffers
  obtain ⟨mb, prepared, allRun, goodP, _treesP, _buffersP, _sizesP, _storageP, _frameP, _outputP, _dataP⟩ :=
    all_trees_dynamic_data_engine (ob := 0) goodZ treesZ buffersZ ledger clear treesZ.run.sym_next_le memory pending bits
  have prepare : blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) := by
    unfold blockPrepare
    rw [bind_app, hint]
    exact allRun
  obtain ⟨countMb, counted, countHeap, countState, countBuf, countPrepare, _countRun,
    _countGood, _countTrees, _countBuffers, count, _countCursor, room⟩ :=
    dynamic_prepared_payload_bit_count goodZ treesZ buffersZ cursor memory pending bits ledger clear last
  have countedEq : counted = prepared := Zlib.Trees.Proofs.same_record_of_runs countPrepare allRun
  subst counted
  have costBound : prepared.opt_len.toNat ≤ 507901 := by
    rw [outBits_length] at count
    omega
  have first : (prepared.opt_len + 3).toNat = prepared.opt_len.toNat + 3 := by
    rw [UInt64.toNat_add]
    change (prepared.opt_len.toNat + 3) % 18446744073709551616 = _
    exact Nat.mod_eq_of_lt (by omega)
  have second : (prepared.opt_len + 3 + 7).toNat = prepared.opt_len.toNat + 10 := by
    rw [UInt64.toNat_add, first]
    change (prepared.opt_len.toNat + 3 + 7) % 18446744073709551616 = _
    rw [Nat.mod_eq_of_lt (by omega)]
  have rounded : (((prepared.opt_len + 3 + 7) >>> 3)).toNat = (prepared.opt_len.toNat + 10) / 8 := by
    rw [UInt64.toNat_shiftRight, second]
    change (prepared.opt_len.toNat + 10) >>> 3 = _
    rw [Nat.shiftRight_eq_div_pow]
  refine ⟨mb, z', prepared, prepare, ?_⟩
  intro prefer avoid
  obtain ⟨emitMb, emittedReady, after, result, next, emitPrepare, emit, goodA, treesA, size, final⟩ :=
    dynamic_prepared_block_byte_count goodZ treesZ buffersZ cursor memory pending bits ledger clear last
  have stateEq : emittedReady = prepared := Zlib.Trees.Proofs.same_record_of_runs emitPrepare allRun
  subst emittedReady
  unfold dynamicPreparedPayload at emit
  have joined : ((do
      Zlib.Trees.Proofs.blPrepare (some (.tab ds))
      Zlib.Trees.build_bl_tree (some (.tab ds))) >>= fun idx => do
        Zlib.Trees.Proofs.dynamicBlockHeader (some (.tab ds)) (if last then 1 else 0) idx
        Zlib.Trees.compress_block (some (.tab ds)) (← Zlib.Trees.pLtree (some (.tab ds)))
          (← Zlib.Trees.pDtree (some (.tab ds)))
        Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0))
      (r.put h z') = .ok ((), after) := by
    simpa only [M_bind_assoc] using emit
  rw [bind_app, allRun] at joined
  have different : ((prepared.static_len + 3 + 7) >>> 3) ≠ ((prepared.opt_len + 3 + 7) >>> 3) := by
    intro equal
    apply prefer
    left
    rw [equal]
    exact Nat.le_refl _
  have dispatch := flush_dynamic_dispatch good positive prepare goodP source stored (if last then 1 else 0)
    prefer avoid different
  exact ⟨after, result, next, dispatch.trans joined, goodA, treesA, by rwa [rounded], final⟩

/-- If the actual stored source is available, avoiding that earlier branch
makes the selected dynamic block cost at most its represented input plus
three bytes. The original ledger bounds the stored-word arithmetic.
No Huffman optimality statement is an input assumption. -/
theorem flush_dynamic_prepared_byte_count {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (source : BPtr) (nonnull : source != .null) (last : Bool) :
    ∃ (mb : Int32) (z' : ZStream) (prepared : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) ∧
      (¬ (((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) ∨
          (prepared.strategy == Z_FIXED) = true) →
        ¬ (UInt64.ofNat (represented xs) + (4 : UInt64) ≤
          ((prepared.opt_len + 3 + 7) >>> 3) ∧ source != .null) →
        ∃ after result next,
          Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source (UInt64.ofNat (represented xs))
            (if last then 1 else 0) h = .ok ((), after) ∧
          DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧
          ((outBits next result).length + 7) / 8 ≤
            ((outBits buf d).length + 7) / 8 + represented xs + 3) := by
  obtain ⟨mb, z', prepared, prepare, selected⟩ := flush_dynamic_prepared_byte_cost
    good trees buffers positive cursor memory pending bits ledger clear source (UInt64.ofNat (represented xs)) last
  refine ⟨mb, z', prepared, prepare, ?_⟩
  intro prefer avoid
  obtain ⟨after, result, next, run, goodA, treesA, bound, _final⟩ := selected prefer avoid
  have count : xs.length ≤ 16383 := by
    have extent := trees.base.sym_end
    have used := trees.run.sym_next_le
    have packedCount := ledger.count
    omega
  have bytes := represented_le ledger.valid
  have natural : (UInt64.ofNat (represented xs)).toNat = represented xs := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have storedWord : (UInt64.ofNat (represented xs) + (4 : UInt64)).toNat = represented xs + 4 := by
    rw [UInt64.toNat_add, natural]
    change (represented xs + 4) % 18446744073709551616 = _
    exact Nat.mod_eq_of_lt (by omega)
  have strict : (((prepared.opt_len + 3 + 7) >>> 3)).toNat < represented xs + 4 := by
    by_cases yes : (((prepared.opt_len + 3 + 7) >>> 3)).toNat < represented xs + 4
    · exact yes
    · apply False.elim
      apply avoid
      refine ⟨?_, nonnull⟩
      rw [UInt64.le_iff_toNat_le, storedWord]
      omega
  exact ⟨after, result, next, run, goodA, treesA, by omega⟩

end Zlib.Deflate.Engine.Proofs
