import ZlibF.Proof.«deflate.c.engine.static-budget»
import ZlibF.Proof.«deflate.c.engine.fixed-block»
import ZlibF.Proof.«deflate.c.engine.flush-fixed»
import ZlibF.Math.DeflateStreamBudget

/-! # Actual fixed output has the cost used by block selection

These results connect the original frequency ledger, the real preparation
counter and the actual fixed writer. They do not prove a size bound for
dynamic blocks or a complete compress utility call.
-/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs (fixedLiteralWords fixedDistanceWords)
open Zlib.Trees.Proofs.Out (TreesInvAt outBits outBits_length payloadSymBits codeBits)
set_option autoImplicit false
set_option maxRecDepth 10000

/-- Payload cost includes the seven-bit end marker and excludes the tag. -/
def fixedWireCost (xs : List Symbol) : Nat :=
  7 + (xs.map (fun s => (payloadSymBits fixedLiteralWords fixedDistanceWords
    (s.distance, s.value)).length)).sum

theorem fixed_wire_length (xs : List Symbol) :
    (xs.flatMap (fun s => payloadSymBits fixedLiteralWords fixedDistanceWords
      (s.distance, s.value)) ++ codeBits fixedLiteralWords 256).length = fixedWireCost xs := by
  simp only [List.length_append, List.length_flatMap, codeBits,
    Zlib.Trees.Proofs.Out.natBits_length, Zlib.Trees.Proofs.fixed_literal_end,
    show (7 : UInt16).toNat = 7 from rfl, fixedWireCost]
  omega

/-- The source histogram measured before tree construction equals the
complete fixed payload's bit count, with no guessed cost premise. -/
theorem ledger_static_wire_cost {buf : Array UInt8} {d : DeflateState} {xs : List Symbol}
    (ledger : SymbolLedger buf d xs) : originalStaticCost d = fixedWireCost xs := by
  have literal : mass (fun v => d.dyn_ltree[v]!.fc.toNat * staticLiteralCost v) 286 =
      7 + (xs.map (fun s => staticLiteralCost (s.literalKey symbolLengthCode))).sum := by
    rw [mass_congr (fun v fit => by rw [ledger.literal v fit]),
      literal_frequency_cost symbolLengthCode xs staticLiteralCost 286 (by decide +kernel)
        (fun s member => valid_literal_key (ledger.valid s member))]
    rfl
  have distance : mass (fun v => d.dyn_dtree[v]!.fc.toNat * staticDistanceCost v) 30 =
      (xs.map staticDistanceSymbolCost).sum := by
    rw [mass_congr (fun v fit => by rw [ledger.distance v fit])]
    exact weighted_optional_key (Symbol.distanceKey Zlib.Trees.Proofs.Out.dcodeN) 30 staticDistanceCost
      (fun s member _ selected => valid_distance_key (ledger.valid s member) selected)
  have costs (ys : List Symbol) (valid : ∀ s ∈ ys, s.Valid) :
      (ys.map (fun s => staticLiteralCost (s.literalKey symbolLengthCode))).sum +
      (ys.map staticDistanceSymbolCost).sum =
      (ys.map (fun s => (payloadSymBits fixedLiteralWords fixedDistanceWords
        (s.distance, s.value)).length)).sum := by
    induction ys with
    | nil => simp
    | cons s ys ih =>
      have head := static_symbol_cost s (valid s (by simp))
      have tail := ih (fun t member => valid t (by simp [member]))
      simp only [List.map_cons, List.sum_cons]
      omega
  have total := costs xs ledger.valid
  unfold originalStaticCost fixedWireCost
  rw [literal, distance]
  omega

/-- The real source constructors install the cost of the fixed wire.
This is equality in the unsigned counter; non-wrapping is separate. -/
theorem block_prepare_fixed_wire_cost {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs)
    (clear : BlockInit.BlockClear d) :
    ∃ (mb : Int32) (z' : ZStream) (result : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds result) ∧
      DGood (setD (r.put h z') ds result) r ds z' result ∧
      result.static_len = UInt64.ofNat (fixedWireCost xs) := by
  obtain ⟨mb, z', result, run, goodA, _treesA, _buffersA, _account,
    _sizes, _storage, _fields, cost, _budget⟩ :=
    block_prepare_static_budget_engine (ob := 0) good trees buffers ledger clear
  exact ⟨mb, z', result, run, goodA, by rwa [ledger_static_wire_cost ledger] at cost⟩

/-- Actual complete fixed payload execution has exactly the measured
bit increment. The entry conditions are those of its existing execution
proof, including default memory and at most ten tag-inclusive held bits. -/
theorem fixed_payload_bit_count {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 10)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) :
    ∃ next result,
      let after := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
      Zlib.Trees.compress_block (some (.tab ds)) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) h =
        .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧
      (outBits next result).length = (outBits buf d).length + fixedWireCost xs := by
  obtain ⟨next, result, run, goodA, treesA, _buffersA, _sizes, _storage, _fields,
    _size, _bound, _cursor, _room, output⟩ :=
    fixed_payload_ready_fields (ob := 0) good trees buffers cursor memory pending bits count packed valid
  refine ⟨next, result, run, goodA, treesA, ?_⟩
  rw [output, List.length_append, fixed_wire_length]

/-- The complete real fixed branch, reset and optional final alignment
cost no more rounded bytes than the counter estimate `(payload + 10)/8`.
Both final flags and every initial held-bit count at most seven are
included. This proves the selected fragment, before publication; the
full flush's choice and its dynamic alternative remain separate. -/
theorem fixed_block_byte_count {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) (last : Bool) :
    ∃ after result next,
      (do Zlib.Trees.Proofs.fixedBlockPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧
      ((outBits next result).length + 7) / 8 ≤
        ((outBits buf d).length + 7) / 8 + (fixedWireCost xs + 10) / 8 ∧
      (last = true → result.bi_valid.toInt = 0) := by
  obtain ⟨tagged, headerRun, goodH, treesH, buffersH, _sizesH, _storageH, diffH,
    pendingH, bitsH, cursorH, outputH⟩ :=
    fixed_header_engine (ob := 0) good trees buffers cursor pending bits last
  obtain ⟨_, _, _, _, fieldsH⟩ := diffH
  obtain ⟨emittedBuf, emitted, payloadRun, goodE, treesE, buffersE, _sizesE, _storageE,
    _fieldsE, _sizeE, _pendingE, cursorE, roomE, outputE⟩ :=
    fixed_payload_ready_fields (ob := 0) goodH treesH buffersH cursorH
      (by rw [fieldsH]; exact memory) pendingH bitsH
      (by rw [fieldsH]; exact count) (by rw [fieldsH]; exact packed) valid
  have lengthE : (outBits emittedBuf emitted).length =
      (outBits buf d).length + 3 + fixedWireCost xs := by
    rw [outputE, outputH, List.length_append, List.length_append,
      Zlib.Trees.Proofs.Out.fixedTag_length, fixed_wire_length]
  obtain ⟨a1, a2, a3, reset, resetRun, goodR, treesR, buffersR, _sizesR, _storageR,
    resetFields, _ledgerR, resetBits⟩ :=
    init_block_engine (ob := 0) goodE treesE buffersE
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursorE
  have roomR : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    rw [resetFields]
    exact roomE
  have lengthR : (outBits emittedBuf reset).length =
      (outBits buf d).length + 3 + fixedWireCost xs := by
    rw [resetBits]
    exact lengthE
  have rounded : ((outBits emittedBuf reset).length + 7) / 8 ≤
      ((outBits buf d).length + 7) / 8 + (fixedWireCost xs + 10) / 8 := by
    rw [lengthR]
    have bound := ZlibF.Math.DeflateBound.ceil_bytes_append (outBits buf d).length (3 + fixedWireCost xs)
    omega
  cases last with
  | false =>
    change Zlib.Trees.Proofs.fixedBlockHeader (some (.tab ds)) 0 h = .ok ((), setD h ds tagged) at headerRun
    refine ⟨_, reset, emittedBuf, ?_, goodR, treesR, rounded, by simp⟩
    unfold Zlib.Trees.Proofs.fixedBlockPayload Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, headerRun, payloadRun, resetRun,
      show ((0 : Int32) != 0) = false from rfl, Bool.false_eq_true, ite_false, pure_app]
  | true =>
    change Zlib.Trees.Proofs.fixedBlockHeader (some (.tab ds)) 1 h = .ok ((), setD h ds tagged) at headerRun
    obtain ⟨next, result, windupRun, goodA, treesA, _buffersA, _sizesA, _storageA,
      _fieldsA, _sizeA, _pendingA, zeroA, _wordA, _cursorA, outputA⟩ :=
      windup_engine (ob := 0) goodR treesR buffersR cursorR roomR
    have windupCount := congrArg List.length outputA
    simp only [List.length_append, List.length_replicate, outBits_length] at windupCount
    have sameRounded : ((outBits next result).length + 7) / 8 =
        ((outBits emittedBuf reset).length + 7) / 8 := by
      rw [outBits_length, outBits_length]
      omega
    refine ⟨_, result, next, ?_, goodA, treesA, by rw [sameRounded]; exact rounded,
      by intro _; exact zeroA⟩
    unfold Zlib.Trees.Proofs.fixedBlockPayload Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, headerRun, payloadRun, resetRun,
      show ((1 : Int32) != 0) = true from rfl, ite_true, windupRun]

/-- `void ZLIB_INTERNAL _tr_flush_block(deflate_state *s, charf *buf,
ulg stored_len, int last)`.
The actual preparation and fixed choice emit at most represented input
plus three bytes beyond the rounded prior bits whenever the source bytes
are still available for the stored comparison. The branch conditions are
on the real prepared counters, not an assumed constructor contract.
This is an internal branch result. Negative source positions, dynamic
coding and whole-call block counting remain separate obligations. -/
theorem flush_fixed_prepared_byte_count {h : Heap} {r : ZStreamRef} {ds pb : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (source : BPtr) (nonnull : source != .null) (last : Bool) :
    ∃ (mb : Int32) (z' : ZStream) (prepared : DeflateState),
      blockPrepare (some (.tab ds)) h = .ok (mb, setD (r.put h z') ds prepared) ∧
      prepared.static_len = UInt64.ofNat (fixedWireCost xs) ∧
      ( ((prepared.static_len + 3 + 7) >>> 3) ≤ ((prepared.opt_len + 3 + 7) >>> 3) →
        ¬ (UInt64.ofNat (represented xs) + (4 : UInt64) ≤
          ((prepared.static_len + 3 + 7) >>> 3) ∧ source != .null) →
        ∃ after result next,
          Zlib.Trees.«_tr_flush_block» (some (.tab ds)) source (UInt64.ofNat (represented xs))
            (if last then 1 else 0) h = .ok ((), after) ∧
          DGood after r ds z' result ∧ TreesInvAt after ds result pb next ∧
          ((outBits next result).length + 7) / 8 ≤
            ((outBits buf d).length + 7) / 8 + represented xs + 3 ) := by
  obtain ⟨mb, z', prepared, prepare, goodP, treesP, buffersP, _account, _sizes, _storage,
    fields, exactCost, _budget⟩ :=
    block_prepare_static_budget_engine (ob := 0) good trees buffers ledger clear
  have cost : prepared.static_len = UInt64.ofNat (fixedWireCost xs) := by
    rwa [ledger_static_wire_cost ledger] at exactCost
  refine ⟨mb, z', prepared, prepare, cost, ?_⟩
  intro prefer avoid
  have record := fields
  unfold TreePreparationFrame at record
  obtain ⟨after, result, next, run, goodA, treesA, size, _final⟩ :=
    fixed_block_byte_count goodP treesP buffersP
      (by rw [record]; exact cursor) (by rw [record]; exact memory)
      (by rw [record]; exact pending) (by rw [record]; exact bits)
      (by rw [record]; exact ledger.count) (by rw [record]; exact ledger.packed) ledger.valid last
  have sourceRun := flush_fixed_dispatch good positive prepare goodP source
    (UInt64.ofNat (represented xs)) (if last then 1 else 0) prefer avoid
  have count : xs.length ≤ 16383 := by
    have extent := trees.base.sym_end
    have used := trees.run.sym_next_le
    have packedCount := ledger.count
    omega
  have bytes := represented_le ledger.valid
  have wireBudget : fixedWireCost xs ≤ 31 * xs.length + 7 := by
    rw [← ledger_static_wire_cost ledger]
    exact ledger_static_cost_budget ledger
  have wireWord : prepared.static_len.toNat = fixedWireCost xs := by
    rw [cost, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have first : (prepared.static_len + 3).toNat = fixedWireCost xs + 3 := by
    rw [UInt64.toNat_add, wireWord]
    change (fixedWireCost xs + 3) % 18446744073709551616 = _
    exact Nat.mod_eq_of_lt (by omega)
  have second : (prepared.static_len + 3 + 7).toNat = fixedWireCost xs + 10 := by
    rw [UInt64.toNat_add, first]
    change (fixedWireCost xs + 3 + 7) % 18446744073709551616 = _
    rw [Nat.mod_eq_of_lt (by omega)]
  have rounded : (((prepared.static_len + 3 + 7) >>> 3)).toNat = (fixedWireCost xs + 10) / 8 := by
    rw [UInt64.toNat_shiftRight, second]
    change (fixedWireCost xs + 10) >>> 3 = _
    rw [Nat.shiftRight_eq_div_pow]
  have storedWord : (UInt64.ofNat (represented xs) + (4 : UInt64)).toNat = represented xs + 4 := by
    have natural : (UInt64.ofNat (represented xs)).toNat = represented xs := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    rw [UInt64.toNat_add, natural]
    change (represented xs + 4) % 18446744073709551616 = _
    exact Nat.mod_eq_of_lt (by omega)
  have strict : (fixedWireCost xs + 10) / 8 < represented xs + 4 := by
    by_cases yes : (fixedWireCost xs + 10) / 8 < represented xs + 4
    · exact yes
    · apply False.elim
      apply avoid
      refine ⟨?_, nonnull⟩
      rw [UInt64.le_iff_toNat_le, storedWord, rounded]
      omega
  have prior : outBits buf prepared = outBits buf d := by rw [record]; rfl
  rw [prior] at size
  exact ⟨after, result, next, sourceRun.trans run, goodA, treesA, by omega⟩

end Zlib.Deflate.Engine.Proofs
