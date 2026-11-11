import ZlibF.Proof.«deflate.c.engine.dynamic-format»
import ZlibF.Proof.«deflate.c.engine.block-windup»
import ZlibF.Proof.«trees.c.universal-stored»

/-!
# trees.c: the dynamic branch of a block flush, for every memLevel with a large symbol buffer

Batch C of the deflate skeleton. Tree construction, `send_all_trees`, `compress_block` with the
constructed trees, `init_block` and the final `bi_windup`, with the output room expressed in
`lit_bufsize` instead of the default 16384.

The room has two parts (fact F9 of `docs/proof/trees.md`): every prefix of the emitted header and
symbols stays below the next unread symbol, and the whole block fits `pending_buf`. Both follow
from the proved header bound (2283 bits) and symbol excess bound (6.257 bits per symbol above 24)
when `lit_bufsize ≥ 2048`, that is `memLevel ≥ 5`. For `memLevel` 1 to 4 the prefix bound is open
(`docs/progress.md`); the lemmas below that take a `DynamicRoom` premise are stated for every
memLevel, and only `dynamic_room_large` needs `2048 ≤ lit_bufsize`.
-/

namespace Zlib.Deflate.Universal.Block
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs (sourceWords SourceCodeFacts PreparedHeaderData dynamicHeaderBits dynamicTag
  DynamicPayloadData dynamicPayloadPrefix)
open Zlib.Trees.Proofs.Out (TreesInvAt BitsDiff payloadSymBits codeBits dcodeN)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The overlay room of a dynamic block, at any memLevel: the entry bits, the three tag bits,
the tree description and every prefix of the symbol codes stay fifteen bits below the next
unread symbol, and the whole block with the end code and the final alignment fits the
`4 * lit_bufsize` bytes of `pending_buf`. -/
structure DynamicRoom (d : DeflateState) (mb : Int32) (xs : List Symbol) : Prop where
  prefix_room : ∀ k, 8 * d.pending.toNat + d.bi_valid.toInt.toNat + 3 +
    (dynamicHeaderBits d mb).length + ((dynamicSymbolCosts d xs).take k).sum + 15 ≤
      8 * (d.lit_bufsize.toNat + 3 * k)
  block_room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + 3 +
    (dynamicHeaderBits d mb).length + (dynamicSymbolCosts d xs).sum + 15 + 7 ≤
      8 * (4 * d.lit_bufsize.toNat)

/-- The room of the symbol codes after the header, at any memLevel. -/
structure PayloadRoom (d : DeflateState) (xs : List Symbol) : Prop where
  prefix_room : ∀ k, 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
    ((dynamicSymbolCosts d xs).take k).sum + 15 ≤ 8 * (d.lit_bufsize.toNat + 3 * k)
  block_room : 8 * d.pending.toNat + d.bi_valid.toInt.toNat +
    (dynamicSymbolCosts d xs).sum + 15 + 7 ≤ 8 * (4 * d.lit_bufsize.toNat)

/-- The proved header and excess bounds give the overlay room when `lit_bufsize ≥ 2048`
(`memLevel ≥ 5`), from a drained entry with at most seven held bits. -/
theorem dynamic_room_large {d : DeflateState} {mb : Int32} {xs : List Symbol}
    (large : 2048 ≤ d.lit_bufsize.toNat) (pending : d.pending = 0) (bits : d.bi_valid.toInt.toNat ≤ 7)
    (header : (dynamicHeaderBits d mb).length ≤ 2283)
    (symbolsFit : xs.length + 1 ≤ d.lit_bufsize.toNat)
    (excess : 1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts d xs) ≤ 6257 * (xs.length + 3)) :
    DynamicRoom d mb xs := by
  have costLength : (dynamicSymbolCosts d xs).length = xs.length := by
    simp only [dynamicSymbolCosts, List.length_map]
  have pendingZero : d.pending.toNat = 0 := by rw [pending]; rfl
  constructor
  · intro k
    have prefixBound := Zlib.Trees.Overlay.prefix_bits_le (dynamicSymbolCosts d xs) k
    omega
  · have total := Zlib.Trees.Overlay.prefix_bits_le (dynamicSymbolCosts d xs) (dynamicSymbolCosts d xs).length
    rw [List.take_length] at total
    omega

/-- Tree preparation (`build_tree` of the literal/length and distance trees, `build_bl_tree`)
from the recorded symbols, at any memLevel. It supplies the header data, the header bound
and the excess bound on the prepared state. -/
theorem dynamic_prepare_safe {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (buffers : StreamBuffers h r) (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) :
    ∃ (mb : Int32) (result : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds result) ∧
      DGood (setD h ds result) r ds z result ∧ TreesInvAt (setD h ds result) ds result pb buf ∧
      StreamBuffers (setD h ds result) r ∧ ByteSizes h (setD h ds result) ∧
      OutputStorage h (setD h ds result) r ds pb ob ∧ TreePreparationFrame d result ∧
      Zlib.Trees.Proofs.Out.outBits buf result = Zlib.Trees.Proofs.Out.outBits buf d ∧
      PreparedHeaderData result mb ∧ (dynamicHeaderBits result mb).length ≤ 2283 ∧
      1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts result xs) ≤ 6257 * (xs.length + 3) := by
  obtain ⟨mb, result, run, goodA, treesA, buffersA, sizes, storage,
    _lower, _upper, _guards, fields, output, excess⟩ :=
    all_trees_symbol_excess_engine (ob := ob) good trees buffers ledger trees.run.sym_next_le
  obtain ⟨_literal, ready, prepare, _goodR, treesR, _buffersR, _sizesR, _storageR,
    input, _frameL, _frameD, _outputR⟩ := source_trees_engine (ob := ob) good trees buffers
  obtain ⟨mb2, other, build, header⟩ := Zlib.Trees.Proofs.build_bl_tree_header_budget treesR input
  have complete : (do
        Zlib.Trees.Proofs.blPrepare (some (.tab ds))
        Zlib.Trees.build_bl_tree (some (.tab ds))) h = .ok (mb2, setD h ds other) := by
    rw [bind_app, prepare]
    change Zlib.Trees.build_bl_tree (some (.tab ds)) (setD h ds ready) =
      .ok (mb2, setD (setD h ds ready) ds other) at build
    simpa only [setD_setD] using build
  have sameResult : result = other := Zlib.Trees.Proofs.same_record_of_runs run complete
  have sameIndex : mb = mb2 := (Prod.mk.inj (Except.ok.inj (run.symm.trans complete))).1
  rw [← sameResult, ← sameIndex] at header
  obtain ⟨otherMb, other2, dataRun, data⟩ :=
    Zlib.Trees.Proofs.prepare_header_data trees ledger.end_marker clear.bl
  have same2 : other2 = result := Zlib.Trees.Proofs.same_record_of_runs dataRun run
  have sameIndex2 : otherMb = mb := (Prod.mk.inj (Except.ok.inj (dataRun.symm.trans run))).1
  subst other2
  subst otherMb
  exact ⟨mb, result, run, goodA, treesA, buffersA, sizes, storage, fields, output, data, header, excess⟩

/-- `send_all_trees` with its tag, from prepared header data and the overlay room, at any
memLevel. The unread symbols are untouched and the payload room carries over. -/
theorem dynamic_header_safe {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol} {mb : Int32}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (data : PreparedHeaderData d mb) (room : DynamicRoom d mb xs)
    (packed : PackedSymbols buf d.lit_bufsize.toNat xs) (last : Bool) :
    ∃ next result,
      let after := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
      Zlib.Trees.Proofs.dynamicBlockHeader (some (.tab ds)) (if last then 1 else 0) mb h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BitsDiff d result ∧ next.size = buf.size ∧
      result.pending_out = result.pending_buf ∧ PackedSymbols next result.lit_bufsize.toNat xs ∧
      PreparedHeaderData result mb ∧ PayloadRoom result xs ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (dynamicTag last ++ dynamicHeaderBits d mb) := by
  have initialRoom := room.prefix_room 0
  simp only [List.take_zero, List.sum_nil, Nat.add_zero, Nat.mul_zero] at initialRoom
  have headerRoom : 8 * d.pending.toNat + d.bi_valid.toInt.toNat + 3 +
      (dynamicHeaderBits d mb).length ≤ 8 * buf.size := by
    have size := trees.base.size
    omega
  obtain ⟨next, result, run, treesA, output, size, frame, _lower, _upper, diff⟩ :=
    Zlib.Trees.Proofs.dynamic_block_header_emit trees data last headerRoom
  have goodA := output_bits_good good cursor trees.base.bytes size diff treesA
  have buffersA := output_bits_buffers good buffers cursor trees.base.bytes size diff treesA
  have sizes := output_bits_sizes good trees.base.bytes size diff
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := next)
    good.live.hs trees.base.bytes
  have bitCount := congrArg List.length output
  simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append,
    dynamicTag, Zlib.Trees.Proofs.Out.natBits_length] at bitCount
  have capacity : result.lit_bufsize = d.lit_bufsize := by
    obtain ⟨p, word, valid, used, fields⟩ := diff
    rw [fields]
  have cursorA : result.pending_out = result.pending_buf := by
    obtain ⟨p, word, valid, used, fields⟩ := diff
    rw [fields]
    exact cursor
  have packedA : PackedSymbols next result.lit_bufsize.toNat xs := by
    rw [capacity]
    intro i s selected
    obtain ⟨low, high, value⟩ := packed i s selected
    have untouched (j : Nat) (bound : d.lit_bufsize.toNat ≤ j) : bfn next j = bfn buf j := by
      exact frame j (Or.inr (by omega))
    exact ⟨(untouched _ (by omega)).trans low, (untouched _ (by omega)).trans high,
      (untouched _ (by omega)).trans value⟩
  have costs := dynamicSymbolCosts_bitsDiff xs diff
  have payload : PayloadRoom result xs := by
    constructor
    · intro k
      rw [costs, capacity]
      have before := room.prefix_room k
      omega
    · rw [costs, capacity]
      have before := room.block_room
      omega
  exact ⟨next, result, run, goodA, treesA, buffersA, sizes, storage, diff, size,
    cursorA, packedA, data.bitsDiff diff, payload, output⟩

/-- The code-fit and room premises of the dynamic `compress_block` loop, from the recorded
symbols, the constructed codes and the payload room, at any memLevel. -/
theorem dynamic_payload_data_safe {h : Heap} {ds pb : Nat} {original d : DeflateState}
    {originalBuf buf : Array UInt8} {xs : List Symbol}
    (trees : TreesInvAt h ds d pb buf) (ledger : SymbolLedger originalBuf original xs)
    (codes : SourceCodeFacts original d) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (room : PayloadRoom d xs) :
    DynamicPayloadData d buf xs.length := by
  constructor
  · exact packed_payload_legal packed ledger.valid
  · intro i bound
    have selected : xs[i]? = some xs[i] := List.getElem?_eq_getElem bound
    have member := List.mem_of_getElem? selected
    rw [packed_payload_symbol packed ledger.valid i xs[i] selected]
    have key : Zlib.Trees.Proofs.dynamicLiteralKey (xs[i].distance, xs[i].value) =
        xs[i].literalKey symbolLengthCode := rfl
    rw [key]
    exact codes.literal _ (valid_literal_key (ledger.valid xs[i] member)) (ledger.literal_used member)
  · intro i bound nonzero
    have selected : xs[i]? = some xs[i] := List.getElem?_eq_getElem bound
    have member := List.mem_of_getElem? selected
    have read := packed_payload_symbol packed ledger.valid i xs[i] selected
    rw [read] at nonzero ⊢
    have selectedKey : xs[i].distanceKey dcodeN = some (dcodeN (xs[i].distance - 1)) := by
      simp only [Symbol.distanceKey, nonzero, ite_false]
    exact codes.distance _ (valid_distance_key (ledger.valid xs[i] member) selectedKey)
      (ledger.distance_used member nonzero)
  · exact codes.literal 256 (by decide +kernel) ledger.end_marker
  · intro k fit
    rw [packed_dynamic_prefix_length packed ledger.valid k fit]
    exact room.prefix_room k
  · rw [packed_dynamic_prefix_length packed ledger.valid xs.length (Nat.le_refl _)]
    have length : (dynamicSymbolCosts d xs).length = xs.length := by
      simp only [dynamicSymbolCosts, List.length_map]
    rw [← length, List.take_length]
    have size := trees.base.size
    have bound := room.block_room
    omega

/-- The dynamic `compress_block` with the constructed trees, at any memLevel. -/
theorem dynamic_payload_safe {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {original d : DeflateState} {originalBuf buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (ledger : SymbolLedger originalBuf original xs) (codes : SourceCodeFacts original d)
    (packed : PackedSymbols buf d.lit_bufsize.toNat xs) (room : PayloadRoom d xs)
    (count : d.sym_next.toNat = 3 * xs.length) :
    ∃ next result,
      let after := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
      Zlib.Trees.compress_block (some (.tab ds)) (.ref (Zlib.Trees.Proofs.TK.lit.ref ds) 0)
        (.ref (Zlib.Trees.Proofs.TK.dist.ref ds) 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BitsDiff d result ∧ next.size = buf.size ∧
      result.pending_out = result.pending_buf ∧ SourceCodeFacts original result ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat + 7 ≤ 8 * buf.size ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (xs.flatMap (fun s => payloadSymBits (sourceWords d .lit) (sourceWords d .dist) (s.distance, s.value)) ++
          codeBits (sourceWords d .lit) 256) := by
  have data := dynamic_payload_data_safe trees ledger codes packed room
  obtain ⟨next, result, run, treesA, output, size, _frame, _lower, _upper, diff⟩ :=
    Zlib.Trees.Proofs.compress_block_dynamic_emit trees xs.length count data
  have goodA := output_bits_good good cursor trees.base.bytes size diff treesA
  have buffersA := output_bits_buffers good buffers cursor trees.base.bytes size diff treesA
  have sizes := output_bits_sizes good trees.base.bytes size diff
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := next)
    good.live.hs trees.base.bytes
  have bitCount := congrArg List.length output
  simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append, codeBits,
    Zlib.Trees.Proofs.Out.natBits_length] at bitCount
  have prefixLength := packed_dynamic_prefix_length packed ledger.valid xs.length (Nat.le_refl _)
  have costLength : (dynamicSymbolCosts d xs).length = xs.length := by
    simp only [dynamicSymbolCosts, List.length_map]
  have allCosts : (dynamicSymbolCosts d xs).take xs.length = dynamicSymbolCosts d xs := by
    rw [← costLength, List.take_length]
  rw [allCosts] at prefixLength
  have completeRoom : 8 * result.pending.toNat + result.bi_valid.toInt.toNat + 7 ≤ 8 * buf.size := by
    have codeBound := data.end_marker.1
    have blockRoom := room.block_room
    have sizeBuf := trees.base.size
    omega
  have cursorA : result.pending_out = result.pending_buf := by
    obtain ⟨p, word, valid, used, fields⟩ := diff
    rw [fields]
    exact cursor
  rw [packed_dynamic_payload_bits packed ledger.valid] at output
  exact ⟨next, result, run, goodA, treesA, buffersA, sizes, storage, diff,
    size, cursorA, codes.bitsDiff diff, completeRoom, output⟩

/-- Preparation, header and dynamic payload in source order (`dynamicPreparedPayload`), at any
memLevel, given the overlay room of the prepared state. -/
theorem dynamic_prepared_safe {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (room : ∀ (mb : Int32) (ready : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds ready) →
      TreePreparationFrame d ready → (dynamicHeaderBits ready mb).length ≤ 2283 →
      1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 6257 * (xs.length + 3) →
      DynamicRoom ready mb xs)
    (last : Bool) :
    ∃ (after : Heap) (result : DeflateState) (next : Array UInt8),
      dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      next.size = buf.size ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat + 7 ≤ 8 * buf.size ∧ FlushFrame d result := by
  obtain ⟨mb, ready, prepare, goodR, treesR, buffersR, sizesR, storageR, frameR, _outputR, data,
    header, excess⟩ := dynamic_prepare_safe (ob := ob) good trees buffers ledger clear
  have roomR := room mb ready prepare frameR header excess
  obtain ⟨otherMb, other, codeRun, codes⟩ := Zlib.Trees.Proofs.prepare_source_code_facts trees
  have same : other = ready := Zlib.Trees.Proofs.same_record_of_runs codeRun prepare
  subst other
  have cursorR : ready.pending_out = ready.pending_buf := by rw [frameR]; exact cursor
  have packedR : PackedSymbols buf ready.lit_bufsize.toNat xs := by rw [frameR]; exact ledger.packed
  have countR : ready.sym_next.toNat = 3 * xs.length := by rw [frameR]; exact ledger.count
  obtain ⟨headerBuf, headerState, headerRun, goodH, treesH, buffersH, sizesH, storageH,
    diffH, headerSize, cursorH, packedH, _headerDataH, roomH, _outputH⟩ :=
    dynamic_header_safe (ob := ob) goodR treesR buffersR cursorR data roomR packedR last
  have countH : headerState.sym_next.toNat = 3 * xs.length := by
    obtain ⟨_, _, _, _, fields⟩ := diffH
    rw [fields]
    exact countR
  obtain ⟨next, result, payloadRun, goodA, treesA, buffersA, sizesA, storageA, diffA,
    sizeA, cursorA, _codesA, roomA, _outputA⟩ :=
    dynamic_payload_safe (ob := ob) goodH treesH buffersH cursorH ledger (codes.bitsDiff diffH)
      packedH roomH countH
  refine ⟨_, result, next, ?_, goodA, treesA, buffersA,
    (sizesR.trans sizesH).trans sizesA, (storageR.trans storageH).trans storageA,
    sizeA.trans headerSize, cursorA, by rw [← headerSize]; exact roomA,
    ((FlushFrame.of_preparation frameR).trans (FlushFrame.of_bits diffH)).trans (FlushFrame.of_bits diffA)⟩
  unfold dynamicPreparedPayload
  rw [← C.M_bind_assoc, bind_app, prepare]
  simp only [bind_app, headerRun, Zlib.Trees.Proofs.Out.pLtree_run goodH.live.hs,
    Zlib.Trees.Proofs.Out.pDtree_run goodH.live.hs]
  exact payloadRun

/-- The selected dynamic branch and the common tail of `_tr_flush_block`, at any memLevel,
given the overlay room of the prepared state. -/
theorem dynamic_block_safe {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (room : ∀ (mb : Int32) (ready : DeflateState),
      (do Zlib.Trees.Proofs.blPrepare (some (.tab ds)); Zlib.Trees.build_bl_tree (some (.tab ds))) h =
        .ok (mb, setD h ds ready) →
      TreePreparationFrame d ready → (dynamicHeaderBits ready mb).length ≤ 2283 →
      1000 * Zlib.Trees.Overlay.bitExcess (dynamicSymbolCosts ready xs) ≤ 6257 * (xs.length + 3) →
      DynamicRoom ready mb xs)
    (last : Bool) :
    ∃ after result next,
      (do dynamicPreparedPayload (some (.tab ds)) (if last then 1 else 0)
          Zlib.Trees.Proofs.flushBlockTail (some (.tab ds)) (if last then 1 else 0)) h = .ok ((), after) ∧
      DGood after r ds z result ∧ TreesInvAt after ds result pb next ∧ StreamBuffers after r ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ SymbolLedger next result [] ∧
      BlockInit.BlockClear result ∧ next.size = buf.size ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * buf.size ∧
      (last = true → result.bi_valid.toInt = 0) ∧ FlushFrame d result := by
  obtain ⟨emittedHeap, emitted, emittedBuf, emittedRun, goodE, treesE, buffersE,
    sizesE, storageE, sizeE, cursorE, roomE, frameE⟩ :=
    dynamic_prepared_safe (ob := ob) good trees buffers cursor ledger clear room last
  obtain ⟨reset, resetRun, goodR, treesR, buffersR, sizesR, storageR, ledgerR, clearR, _resetBits⟩ :=
    init_block_clear_engine (ob := ob) goodE treesE buffersE
  obtain ⟨a1, a2, a3, reset2, resetRun2, _good2, _trees2, _buffers2, _sizes2, _storage2,
    resetFields, _ledger2, _output2⟩ := init_block_engine (ob := ob) goodE treesE buffersE
  have same : reset2 = reset := Zlib.Trees.Proofs.same_record_of_runs resetRun2 resetRun
  rw [same] at resetFields
  have roomR : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat + 7 ≤ 8 * buf.size := by
    rw [resetFields]
    exact roomE
  have cursorR : reset.pending_out = reset.pending_buf := by rw [resetFields]; exact cursorE
  have frameR : FlushFrame d reset := frameE.trans (FlushFrame.of_reset resetFields)
  have sizes := sizesE.trans sizesR
  have storage := storageE.trans storageR
  have physicalRoom : 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat ≤ 8 * emittedBuf.size := by
    rw [sizeE]
    omega
  cases last with
  | false =>
    change dynamicPreparedPayload (some (.tab ds)) 0 h = .ok ((), emittedHeap) at emittedRun
    refine ⟨_, reset, emittedBuf, ?_, goodR, treesR, buffersR, sizes, storage,
      ledgerR, clearR, sizeE, cursorR, by omega, by simp, frameR⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, emittedRun, resetRun, show ((0 : Int32) != 0) = false from rfl,
      Bool.false_eq_true, ite_false, pure_app]
  | true =>
    change dynamicPreparedPayload (some (.tab ds)) 1 h = .ok ((), emittedHeap) at emittedRun
    obtain ⟨next, result, windupRun, goodA, treesA, buffersA, sizesA, storageA, diffA,
      sizeA, _pendingA, zeroA, _wordA, cursorA, outputA⟩ :=
      windup_engine (ob := ob) goodR treesR buffersR cursorR physicalRoom
    let padding := List.replicate ((8 - reset.bi_valid.toInt.toNat % 8) % 8) false
    have padBound : padding.length < 8 := by
      simpa only [padding, List.length_replicate] using
        Nat.mod_lt (8 - reset.bi_valid.toInt.toNat % 8) (by decide : 0 < 8)
    have bitCount := congrArg List.length outputA
    change (Zlib.Trees.Proofs.Out.outBits next result).length =
      (Zlib.Trees.Proofs.Out.outBits emittedBuf reset ++ padding).length at bitCount
    simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append] at bitCount
    have physical : 8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * buf.size := by
      rw [zeroA] at bitCount ⊢
      change 8 * result.pending.toNat = 8 * reset.pending.toNat + reset.bi_valid.toInt.toNat + padding.length at bitCount
      omega
    refine ⟨_, result, next, ?_, goodA, treesA, buffersA,
      sizes.trans sizesA, storage.trans storageA, empty_ledger_bits ledgerR diffA, clearR.bits diffA,
      sizeA.trans sizeE, cursorA, physical, fun _ => zeroA, frameR.trans (FlushFrame.of_bits diffA)⟩
    unfold Zlib.Trees.Proofs.flushBlockTail
    simp only [bind_app, emittedRun, resetRun, show ((1 : Int32) != 0) = true from rfl,
      ite_true, windupRun]

end Zlib.Deflate.Universal.Block
