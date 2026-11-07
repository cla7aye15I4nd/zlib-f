import ZlibF.Proof.«deflate.c.engine.flush-default-output»
import ZlibF.Math.DeflateBlockStream

/-! # The real strategy macro computes the proved flush pointer and length -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The actual loads, signed source test, checked pointer addition and
checked signed length subtraction before the flush call. -/
def flushOnlyArguments (s : DeflateStatePtr) : M (BPtr × UInt64) := do
  let d ← ldDeflateState s
  let source ← if d.block_start ≥ 0 then padd d.window d.block_start.toUInt64.toUInt32.toNat else pure (Ptr.null : BPtr)
  let length ← lsub d.strstart.toUInt64.toInt64 d.block_start
  return (source, length.toUInt64)

/-- Naming the argument prefix retains the full macro, including its
post-flush block_start update and real pending publication. -/
theorem flush_block_only_arguments_source (s : DeflateStatePtr) (last : Int32) :
    FLUSH_BLOCK_ONLY s last = (do
      let (source, length) ← flushOnlyArguments s
      Zlib.Trees.«_tr_flush_block» s source length last
      wr s fun d => { d with block_start := d.strstart.toUInt64.toInt64 }
      flush_pending (← rd s (·.strm))) := by
  unfold FLUSH_BLOCK_ONLY flushOnlyArguments
  simp only [M_bind_assoc, M_pure_bind, Zlib.Trees.Proofs.merge_ite_bind]

/-- At a real zero-credit block cutpoint, the macro computes exactly the
source pointer and length used by the unrestricted flush theorem. The
signed subtraction and the narrowing pointer-offset casts are checked,
including the actual null-source branch after window slides. -/
theorem default_flush_arguments {h : Heap} {r : ZStreamRef} {ds pb w : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (memory : d.lit_bufsize.toNat = 16384) (ledger : SymbolLedger buf d xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0) :
    flushOnlyArguments (some (.tab ds)) h =
      .ok ((defaultStoredSource d w, UInt64.ofNat (represented xs)), h) := by
  have difference := default_stored_length trees ledger memory trees.run.sym_next_le balance (by omega) (by omega)
  dsimp only at difference
  have delta : ((d.strstart.toNat : Int) - d.block_start.toInt).toNat = represented xs := by
    unfold BlockBalance at balance
    omega
  have sizeBound := difference.2.2
  rw [difference.2.1, delta] at sizeBound
  have word : (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64 =
      UInt64.ofNat (represented xs) := by
    apply UInt64.toNat_inj.mp
    rw [difference.2.1, delta, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  unfold flushOnlyArguments
  rw [bind_app, ldDeflateState_tab good.live.hs]
  by_cases nonnegative : 0 ≤ d.block_start.toInt
  · have bound : d.block_start.toInt.toNat ≤ window.size :=
      Nat.le_trans (Nat.le_add_right _ _) (stored_window_readable good win get range balance nonnegative)
    have size := window_extent good win get
    have cast : d.block_start.toUInt64.toUInt32.toNat = d.block_start.toInt.toNat := by
      rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le (show 0 ≤ d.block_start from by simpa only [Int64.le_iff_toInt_le, Int64.toInt_zero] using nonnegative)]
      change d.block_start.toInt.toNat % 4294967296 = d.block_start.toInt.toNat
      exact Nat.mod_eq_of_lt (by omega)
    have add := padd_ok' (r := BRef.blk w) (a := window) (off := 0)
      (n := d.block_start.toUInt64.toUInt32.toNat) get (by rw [cast]; omega)
    change (do
      let source ← if d.block_start ≥ 0 then padd d.window d.block_start.toUInt64.toUInt32.toNat else pure Ptr.null
      let length ← lsub d.strstart.toUInt64.toInt64 d.block_start
      return (source, length.toUInt64)) h = _
    rw [if_pos (show d.block_start ≥ 0 from by simpa only [Int64.le_iff_toInt_le, Int64.toInt_zero] using nonnegative), win, bind_app, add]
    rw [difference.1]
    simp only [bind_app, pure_app, cast, Nat.zero_add, word, defaultStoredSource, nonnegative, ite_true]
  · change (do
      let source ← if d.block_start ≥ 0 then padd d.window d.block_start.toUInt64.toUInt32.toNat else pure Ptr.null
      let length ← lsub d.strstart.toUInt64.toInt64 d.block_start
      return (source, length.toUInt64)) h = _
    rw [if_neg (show ¬ d.block_start ≥ 0 from by simpa only [Int64.le_iff_toInt_le, Int64.toInt_zero] using nonnegative), difference.1]
    simp only [bind_app, pure_app, word, defaultStoredSource, nonnegative, ite_false]

/-- The macro's actual block_start update changes no byte, tree, output
bit or owned allocation. It is safe even before the strategy's next
advance/deferred-byte step restores the outer history boundary. -/
theorem flush_block_start_engine {h : Heap} {r : ZStreamRef} {ds pb ob : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r) :
    let result : DeflateState := { d with block_start := d.strstart.toUInt64.toInt64 }
    wr (some (.tab ds)) (fun d => { d with block_start := d.strstart.toUInt64.toInt64 }) h =
      .ok ((), setD h ds result) ∧ DGood (setD h ds result) r ds z result ∧
      TreesInvAt (setD h ds result) ds result pb buf ∧ StreamBuffers (setD h ds result) r ∧
      ByteSizes h (setD h ds result) ∧ OutputStorage h (setD h ds result) r ds pb ob := by
  let result : DeflateState := { d with block_start := d.strstart.toUInt64.toInt64 }
  have inv : DStInv h ds result :=
    { good.inv with blocks := good.inv.blocks_keys rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl }
  have goodA := good.setD' (d' := result) rfl good.live.status inv (by trkeep)
  have treesA := trees_at_buffer goodA trees.base.pbuf trees.base.bytes
  have sizes := block_record_sizes good.live.hs (show result.depth = d.depth from rfl)
  have owned := stream_owned_keys good goodA rfl rfl rfl rfl
  have buffersA := stream_buffers_sizes good.live.hz goodA.live.hz buffers sizes owned (stream_accounting_zero z)
  have storage := output_bits_storage (r := r) (ob := ob) (result := result) (next := buf)
    good.live.hs trees.base.bytes
  rw [Zlib.Trees.Proofs.Out.setB_self trees.base.bytes] at storage
  refine ⟨?_, goodA, treesA, buffersA, sizes, storage⟩
  simp only [wrD_eq, good.live.hs]

/-- `FLUSH_BLOCK_ONLY(s, last)`.
The complete real macro computes its checked source and length, executes
all actual flush choices, updates block_start and publishes pending bytes.
Caller capacity may be zero or short. Exact emitted bits, input-prefix
meaning, reset data and the new block-start equality survive publication.
The outer strategy must still establish this explicit zero-credit entry. -/
theorem flush_block_only_publish {h : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState)
      (written : List UInt8) (remaining : List Bool) (kind : Nat) (body padding : List Bool),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BlockInit.BlockClear result ∧
      Zlib.Trees.Proofs.Out.InitialFrequencies result.dyn_ltree result.dyn_dtree ∧
      result.block_start = result.strstart.toUInt64.toInt64 ∧ result.bi_valid.toInt < 8 ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      (63488 + (if last then 0 else 2) ≤ z.avail_out.toNat → result.pending.toNat = 0) ∧
      (last = true → result.bi_valid.toInt.toNat = 0) ∧ kind < 3 ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧ (kind = 0 → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ++
        (Zlib.Trees.Proofs.Out.natBits (if last then 1 else 0) 1 ++
          Zlib.Trees.Proofs.Out.natBits kind 2 ++ body ++ padding) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  have arguments := default_flush_arguments good trees memory ledger win get range balance
  obtain ⟨ze, ready, emitted, outputBuf, kind, body, padding, run, goodE, treesE, buffersE,
    accountE, sizesE, storageE, ledgerE, clearE, sizeE, boundE, cursorE, finalE, kindBound,
    padBound, padNone, storedPad, outputE, grammar⟩ :=
    flush_default_ready (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  let updated : DeflateState := { emitted with block_start := emitted.strstart.toUInt64.toInt64 }
  obtain ⟨updateRun, goodU, treesU, buffersU, sizesU, storageU⟩ :=
    flush_block_start_engine (ob := ob) goodE treesE buffersE
  have nextOut : ze.next_out = z.next_out := by rw [accountE.2.2.2.2.2.1, advance_zero]
  have pointerE : ze.next_out = .ref (.blk ob) oo := nextOut.trans pointer
  have available : ze.avail_out.toNat = z.avail_out.toNat := by have := accountE.2.2.2.1; omega
  have roomU : 8 * updated.pending.toNat + updated.bi_valid.toInt.toNat ≤ 8 * outputBuf.size := by
    rw [sizeE]
    have high := treesE.run.bi_hi
    have low := treesE.run.bi_lo
    change 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 524288
    omega
  obtain ⟨produced, after, z', result, written, remaining, flush, goodA, buffersA, accountA,
    sizesA, storageA, copied, left, low, validA, fieldsA, bytes, pendingA, outputA⟩ :=
    flush_pending_raw_bits goodU treesU buffersU pointerE cursorE roomU
  have ledgerU : SymbolLedger outputBuf updated [] := ledgerE.keep rfl rfl rfl rfl
  have ledgerA : SymbolLedger outputBuf result [] := by rw [fieldsA]; exact ledgerU.keep rfl rfl rfl rfl
  have clearA : BlockInit.BlockClear result := by rw [fieldsA]; exact ⟨clearE.bl, clearE.opt, clearE.fixed⟩
  have frequencies : Zlib.Trees.Proofs.Out.InitialFrequencies result.dyn_ltree result.dyn_dtree := by
    constructor
    · intro k bound
      simpa only [literalFrequency, countKey, Nat.add_zero] using ledgerA.literal k bound
    · intro k bound
      simpa only [distanceFrequency, countKey] using ledgerA.distance k bound
  have position : result.block_start = result.strstart.toUInt64.toInt64 := by rw [fieldsA]
  have final : last = true → result.bi_valid.toInt.toNat = 0 := by
    intro flag
    have validU : updated.bi_valid.toInt = 0 := finalE flag
    rw [validU] at validA
    exact validA
  have drained : 63488 + (if last then 0 else 2) ≤ z.avail_out.toNat → result.pending.toNat = 0 := by
    intro capacity
    change produced = min (emitted.pending.toNat + emitted.bi_valid.toInt.toNat / 8) ze.avail_out.toNat at copied
    change result.pending.toNat + produced = emitted.pending.toNat + emitted.bi_valid.toInt.toNat / 8 at left
    by_cases flag : last = true
    · rw [finalE flag] at copied left
      rw [available] at copied
      simp only [Int.toNat_zero, Nat.zero_div, Nat.add_zero] at copied left
      simp [flag] at capacity
      omega
    · have high := treesE.run.bi_hi
      rw [available] at copied
      simp [flag] at capacity
      omega
  have bytesA : Bytes after z.next_out produced written := by rw [nextOut] at bytes; exact bytes
  have account : StreamAccounting z z' 0 produced := by
    simpa only [Nat.zero_add] using stream_accounting_trans accountE accountA
  refine ⟨produced, after, z', result, written, remaining, kind, body, padding, ?_, goodA, buffersA,
    account, (sizesE.trans sizesU).trans sizesA, (storageE.trans storageU).trans storageA,
    clearA, frequencies, position, low, bytesA, pendingA, drained, final, kindBound,
    padBound, padNone, storedPad, outputA.trans outputE, grammar⟩
  have streamRead : rd (some (.tab ds)) (·.strm) (setD ready ds updated) =
      .ok (some r, setD ready ds updated) := by
    simp only [rdD_eq, setD_dstates_same]
    rw [show updated.strm = some r from goodE.live.back]
  rw [flush_block_only_arguments_source, bind_app, arguments]
  simp only [bind_app, run, updateRun]
  change (rd (some (.tab ds)) (·.strm) >>= fun strm => flush_pending strm)
    (setD ready ds updated) = .ok ((), after)
  rw [bind_app, streamRead]
  exact flush

/-- `FLUSH_BLOCK_ONLY(s, 1)`.
The complete real macro, including argument evaluation and its actual
block_start store, publishes an independently valid raw stream from a
byte-aligned zero-credit block cutpoint with enough caller output space.
This does not prove the surrounding deflate_slow loop or public wrapper. -/
theorem flush_block_only_final_valid {h : Heap} {r : ZStreamRef} {ds pb ob oo w origin : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt = 0)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input 0 xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i))
    (capacity : 63488 ≤ z.avail_out.toNat) :
    ∃ produced after z' result written,
      FLUSH_BLOCK_ONLY (some (.tab ds)) 1 h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BlockInit.BlockClear result ∧
      result.block_start = result.strstart.toUInt64.toInt64 ∧ result.pending.toNat = 0 ∧
      result.bi_valid.toInt.toNat = 0 ∧ Bytes after z.next_out produced written ∧
      ZlibF.Spec.Deflate.Valid (inputPrefix input (represented xs)) written := by
  obtain ⟨produced, after, z', result, written, remaining, kind, body, padding, run, goodA, buffersA,
    account, sizes, storage, clearA, _frequencies, position, _low, bytes, pendingA, drained, final, kindBound,
    padBound, _padNone, storedPad, output, grammar⟩ :=
    flush_block_only_publish good trees buffers positive pointer cursor memory pending (by rw [bits]; decide +kernel)
      ledger clear trace win get range balance (by simpa only [Nat.zero_add] using accounted) view true
  have drainedA := drained (by simpa only [ite_true, Nat.add_zero] using capacity)
  have validZero := final rfl
  have remainingZero := pending_bits_empty pendingA drainedA validZero
  have before : Zlib.Trees.Proofs.Out.outBits buf d = [] := by
    simp [Zlib.Trees.Proofs.Out.outBits, Zlib.Trees.Proofs.Out.bytesBits, Zlib.Trees.Proofs.Out.natBits, pending, bits]
  rw [remainingZero, List.append_nil, before, List.nil_append] at output
  have bodyGrammar := grammar padding (fun isStored => by rw [storedPad isStored]; rfl)
  have accepted : ZlibF.Spec.Deflate.Valid (inputPrefix input (represented xs)) written :=
    Zlib.Trees.Proofs.Out.terminal_block_valid (by omega) padBound output
      (by simpa only [inputPrefix, List.range_zero, List.map_nil, Nat.zero_add] using bodyGrammar)
  exact ⟨produced, after, z', result, written, run, goodA, buffersA, account, sizes, storage,
    clearA, position, drainedA, validZero, bytes, accepted⟩

end Zlib.Deflate.Engine.Proofs
