import ZlibF.Proof.«trees.c.compress-fixed»
import ZlibF.Proof.«deflate.c.engine.symbol-boundary»
import ZlibF.Proof.«deflate.c.engine.pending-block-output»

/-! # Actual packed engine symbols reach fixed payload output and publication -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- The three actual packed bytes reconstruct the same logical symbol.
The proof uses the legal distance/value range, including 32768 and 258. -/
theorem packed_payload_symbol {buf : Array UInt8} {base : Nat} {xs : List Symbol}
    (packed : PackedSymbols buf base xs) (valid : ∀ s ∈ xs, s.Valid)
    (i : Nat) (s : Symbol) (selected : xs[i]? = some s) :
    Zlib.Trees.Proofs.Out.payloadSymAt buf base i = (s.distance, s.value) := by
  obtain ⟨lo, hi, value⟩ := packed i s selected
  obtain ⟨distance, length⟩ := valid s (List.mem_of_getElem? selected)
  have byte (j : Nat) : buf[j]! = bfn buf j := by
    rw [Array.getElem!_eq_getD]
    rfl
  unfold Zlib.Trees.Proofs.Out.payloadSymAt
  rw [byte, byte, byte, lo, hi, value]
  apply Prod.ext
  · rw [UInt16.toNat_toUInt8, UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, UInt16.toNat_ofNat']
    simp only [show ((8 : UInt16).toNat % 16) = 8 from rfl, Nat.shiftRight_eq_div_pow,
      show 2 ^ 8 = 256 from rfl]
    omega
  · rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt length]

/-- The writer's original-byte payload list equals the engine's actual
packed logical symbol list. Unused symbol bytes remain unconstrained. -/
theorem packed_payload_list {buf : Array UInt8} {base : Nat} {xs : List Symbol}
    (packed : PackedSymbols buf base xs) (valid : ∀ s ∈ xs, s.Valid) :
    (List.range xs.length).map (Zlib.Trees.Proofs.Out.payloadSymAt buf base) =
      xs.map (fun s => (s.distance, s.value)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have index : i < xs.length := by simpa using hi
  simp only [List.getElem_map, List.getElem_range]
  exact packed_payload_symbol packed valid i xs[i] (List.getElem?_eq_getElem index)

/-- Payload transmission order is exactly the stored engine symbol order. -/
theorem packed_fixed_payload_bits {buf : Array UInt8} {base : Nat} {xs : List Symbol}
    (packed : PackedSymbols buf base xs) (valid : ∀ s ∈ xs, s.Valid) :
    Zlib.Trees.Proofs.fixedPayloadPrefix buf base xs.length =
      xs.flatMap (fun s => Zlib.Trees.Proofs.Out.payloadSymBits
        Zlib.Trees.Proofs.fixedLiteralWords Zlib.Trees.Proofs.fixedDistanceWords (s.distance, s.value)) := by
  rw [Zlib.Trees.Proofs.fixedPayloadPrefix, Zlib.Trees.Proofs.Out.payloadPrefixBits,
    packed_payload_list packed valid, List.flatMap_map]

/-- The actual ledger established by init and real tallies supplies every
original-symbol legality condition needed by the complete fixed writer. -/
theorem packed_payload_legal {buf : Array UInt8} {base : Nat} {xs : List Symbol}
    (packed : PackedSymbols buf base xs) (valid : ∀ s ∈ xs, s.Valid) :
    ∀ i, i < xs.length → (Zlib.Trees.Proofs.Out.payloadSymAt buf base i).1 ≤ 32768 := by
  intro i bound
  have selected : xs[i]? = some xs[i] := List.getElem?_eq_getElem bound
  rw [packed_payload_symbol packed valid i xs[i] selected]
  exact (valid xs[i] (List.mem_of_getElem? selected)).1


/-- `local void compress_block(deflate_state *s, const ct_data *ltree, const ct_data *dtree)`.
Actual packed engine symbols feed the complete fixed writer. The default
memory equation gives all read/write room and leaves at least enough
room for complete-bit publication. The returned DGood and caller ranges
come from the same actual output heap. No callee contract is assumed.
This is the fixed-table branch, with a drained entry and at most ten bits
including its block tag; public block selection remains separate. -/
theorem fixed_payload_ready {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (cursor : d.pending_out = d.pending_buf) (memory : d.lit_bufsize.toNat = 16384)
    (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 10)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) :
    ∃ next result,
      let ready := setD (Zlib.Trees.Proofs.Out.setB h pb next) ds result
      Zlib.Trees.compress_block (some (.tab ds)) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0) h = .ok ((), ready) ∧
      DGood ready r ds z result ∧ TreesInvAt ready ds result pb next ∧ StreamBuffers ready r ∧
      ByteSizes h ready ∧ OutputStorage h ready r ds pb ob ∧
      next.size = 65536 ∧ result.pending.toNat ≤ 63486 ∧ result.pending_out = result.pending_buf ∧
      8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size ∧
      Zlib.Trees.Proofs.Out.outBits next result = Zlib.Trees.Proofs.Out.outBits buf d ++
        (xs.flatMap (fun s => Zlib.Trees.Proofs.Out.payloadSymBits
          Zlib.Trees.Proofs.fixedLiteralWords Zlib.Trees.Proofs.fixedDistanceWords (s.distance, s.value)) ++
          Zlib.Trees.Proofs.Out.codeBits Zlib.Trees.Proofs.fixedLiteralWords 256) := by
  have legal := packed_payload_legal packed valid
  obtain ⟨next, result, run, treesA, output, size, _frame, _lower, _upper, fields⟩ :=
    Zlib.Trees.Proofs.compress_block_fixed_emit trees pending bits xs.length count legal
  have goodA := output_bits_good good cursor trees.base.bytes size fields treesA
  have buffersA := output_bits_buffers good buffers cursor trees.base.bytes size fields treesA
  have sizes := output_bits_sizes good trees.base.bytes size fields
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := next)
    good.live.hs trees.base.bytes
  have capacity := trees.run.sym_next_le
  rw [count, trees.base.sym_end, memory] at capacity
  have length := Zlib.Trees.Proofs.fixedPayloadPrefix_length buf d.lit_bufsize.toNat xs.length legal
  have bitCount := congrArg List.length output
  simp only [Zlib.Trees.Proofs.Out.outBits_length, List.length_append, Zlib.Trees.Proofs.Out.codeBits,
    Zlib.Trees.Proofs.fixed_literal_end, Zlib.Trees.Proofs.Out.natBits_length,
    show (7 : UInt16).toNat = 7 from rfl, pending, UInt64.toNat_zero] at bitCount
  have pendingBound : result.pending.toNat ≤ 63486 := by omega
  have sizeA : next.size = 65536 := by rw [size, trees.base.size, memory]
  have cursorA : result.pending_out = result.pending_buf := by
    obtain ⟨_, _, _, _, equal⟩ := fields
    rw [equal]
    exact cursor
  have validA := treesA.run.bi_hi
  have room : 8 * result.pending.toNat + result.bi_valid.toInt.toNat ≤ 8 * next.size := by rw [sizeA]; omega
  rw [packed_fixed_payload_bits packed valid] at output
  exact ⟨next, result, run, goodA, treesA, buffersA, sizes, storage, sizeA, pendingBound, cursorA, room, output⟩

/-- `local void compress_block(deflate_state *s, const ct_data *ltree, const ct_data *dtree)`
followed by actual flush_pending. Real symbol data produce the publishing
room; it is not an assumption of this composed execution. Arbitrary raw
output capacity, including zero and partial copies, is included. Written
bytes plus public PendingBits equal the exact fixed payload after the
entry bits. Whole block selection, padding and public deflate remain open. -/
theorem fixed_payload_publish {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 10)
    (count : d.sym_next.toNat = 3 * xs.length) (packed : PackedSymbols buf d.lit_bufsize.toNat xs)
    (valid : ∀ s ∈ xs, s.Valid) :
    ∃ produced after z' result written remaining,
      (do Zlib.Trees.compress_block (some (.tab ds)) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0)
          flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ result.bi_valid.toInt < 8 ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ++
        (xs.flatMap (fun s => Zlib.Trees.Proofs.Out.payloadSymBits
          Zlib.Trees.Proofs.fixedLiteralWords Zlib.Trees.Proofs.fixedDistanceWords (s.distance, s.value)) ++
          Zlib.Trees.Proofs.Out.codeBits Zlib.Trees.Proofs.fixedLiteralWords 256) := by
  obtain ⟨next, emitted, run, goodE, treesE, buffersE, sizesE, storageE,
    _size, _pendingBound, cursorE, room, payload⟩ :=
    fixed_payload_ready (ob := ob) good trees buffers cursor memory pending bits count packed valid
  obtain ⟨produced, after, z', result, written, remaining, flush, goodA, buffersA, account, sizesA, storageA,
    _count, _pendingCount, low, _valid, _fields, bytes, pendingA, output⟩ :=
    flush_pending_raw_bits goodE treesE buffersE pointer cursorE room
  refine ⟨produced, after, z', result, written, remaining, ?_, goodA, buffersA, account,
    sizesE.trans sizesA, storageE.trans storageA, low, bytes, pendingA, output.trans payload⟩
  simp only [bind_app, run, flush]


/-- The real ledger supplies packed bytes, symbol count and legality.
Its frequency clauses are not callee contracts and are not needed by
this fixed-table consumer. -/
theorem fixed_payload_ledger_publish {h : Heap} {r : ZStreamRef} {ds pb ob oo : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 10)
    (ledger : SymbolLedger buf d xs) :
    ∃ produced after z' result written remaining,
      (do Zlib.Trees.compress_block (some (.tab ds)) (.ref .st_static_ltree 0) (.ref .st_static_dtree 0)
          flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ result.bi_valid.toInt < 8 ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ++
        (xs.flatMap (fun s => Zlib.Trees.Proofs.Out.payloadSymBits
          Zlib.Trees.Proofs.fixedLiteralWords Zlib.Trees.Proofs.fixedDistanceWords (s.distance, s.value)) ++
          Zlib.Trees.Proofs.Out.codeBits Zlib.Trees.Proofs.fixedLiteralWords 256) :=
  fixed_payload_publish good trees buffers pointer cursor memory pending bits ledger.count ledger.packed ledger.valid

end Zlib.Deflate.Engine.Proofs
