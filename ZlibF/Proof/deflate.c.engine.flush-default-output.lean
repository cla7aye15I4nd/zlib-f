import ZlibF.Proof.«deflate.c.engine.flush-default»
import ZlibF.Proof.«deflate.c.engine.pending-block-output»

/-! # All real flush choices publish exact output and terminal raw streams -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt natBits)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Complete actual block preparation, unrestricted cost selection,
emission and reset followed by real pending publication. Zero and short
caller output capacities retain the exact remaining PendingBits. This
internal default-memory result leaves strategy cutpoints, macro updates,
the public loop and legal histories as separate obligations. -/
theorem flush_default_publish {h : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
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
      (do Zlib.Trees.«_tr_flush_block» (some (.tab ds)) (defaultStoredSource d w)
            (UInt64.ofNat (represented xs)) (if last then 1 else 0)
          flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BlockInit.BlockClear result ∧
      Zlib.Trees.Proofs.Out.InitialFrequencies result.dyn_ltree result.dyn_dtree ∧ result.bi_valid.toInt < 8 ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      (63488 + (if last then 0 else 2) ≤ z.avail_out.toNat → result.pending.toNat = 0) ∧
      (last = true → result.bi_valid.toInt.toNat = 0) ∧ kind < 3 ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧ (kind = 0 → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ++
        (natBits (if last then 1 else 0) 1 ++ natBits kind 2 ++ body ++ padding) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  obtain ⟨ze, ready, emitted, outputBuf, kind, body, padding, run, goodE, treesE, buffersE,
    accountE, sizesE, storageE, ledgerE, clearE, sizeE, boundE, cursorE, finalE, kindBound,
    padBound, padNone, storedPad, outputE, grammar⟩ :=
    flush_default_ready (ob := ob) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  have nextOut : ze.next_out = z.next_out := by
    rw [accountE.2.2.2.2.2.1, advance_zero]
  have pointerE : ze.next_out = .ref (.blk ob) oo := nextOut.trans pointer
  have available : ze.avail_out.toNat = z.avail_out.toNat := by have := accountE.2.2.2.1; omega
  have roomE : 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 8 * outputBuf.size := by
    rw [sizeE]
    have high := treesE.run.bi_hi
    have low := treesE.run.bi_lo
    omega
  obtain ⟨produced, after, z', result, written, remaining, flush, goodA, buffersA, accountA,
    sizesA, storageA, copied, left, low, validA, fieldsA, bytes, pendingA, outputA⟩ :=
    flush_pending_raw_bits goodE treesE buffersE pointerE cursorE roomE
  have ledgerA : SymbolLedger outputBuf result [] := by rw [fieldsA]; exact ledgerE.keep rfl rfl rfl rfl
  have clearA : BlockInit.BlockClear result := by rw [fieldsA]; exact ⟨clearE.bl, clearE.opt, clearE.fixed⟩
  have frequencies : Zlib.Trees.Proofs.Out.InitialFrequencies result.dyn_ltree result.dyn_dtree := by
    constructor
    · intro k bound
      simpa only [literalFrequency, countKey, Nat.add_zero] using ledgerA.literal k bound
    · intro k bound
      simpa only [distanceFrequency, countKey] using ledgerA.distance k bound
  have final : last = true → result.bi_valid.toInt.toNat = 0 := by
    intro flag
    rw [finalE flag] at validA
    exact validA
  have drained : 63488 + (if last then 0 else 2) ≤ z.avail_out.toNat → result.pending.toNat = 0 := by
    intro capacity
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
    account, sizesE.trans sizesA, storageE.trans storageA, clearA, frequencies, low, bytesA, pendingA,
    drained, final, kindBound, padBound, padNone, storedPad, outputA.trans outputE, grammar⟩
  rw [bind_app, run]
  exact flush

/-- At an initial byte boundary and with enough caller capacity, the
complete actual flush and publication produce a valid independent raw
DEFLATE stream for every real encoding choice. This remains an internal
block-entry result, not the public compression loop or wrapper theorem. -/
theorem flush_default_final_valid {h : Heap} {r : ZStreamRef} {ds pb ob oo w origin : Nat}
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
      (do Zlib.Trees.«_tr_flush_block» (some (.tab ds)) (defaultStoredSource d w)
            (UInt64.ofNat (represented xs)) 1
          flush_pending (some r)) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧ BlockInit.BlockClear result ∧
      result.pending.toNat = 0 ∧ result.bi_valid.toInt.toNat = 0 ∧ Bytes after z.next_out produced written ∧
      ZlibF.Spec.Deflate.Valid (inputPrefix input (represented xs)) written := by
  obtain ⟨produced, after, z', result, written, remaining, kind, body, padding, run, goodA, buffersA,
    account, sizes, storage, clearA, _frequencies, _low, bytes, pendingA, drained, final, kindBound,
    padBound, _padNone, storedPad, output, grammar⟩ :=
    flush_default_publish good trees buffers positive pointer cursor memory pending (by rw [bits]; decide +kernel)
      ledger clear trace win get range balance (by simpa only [Nat.zero_add] using accounted) view true
  have drainedA := drained (by simpa only [ite_true, Nat.add_zero] using capacity)
  have validZero := final rfl
  have remainingZero := pending_bits_empty pendingA drainedA validZero
  have before : Zlib.Trees.Proofs.Out.outBits buf d = [] := by
    simp [Zlib.Trees.Proofs.Out.outBits, Zlib.Trees.Proofs.Out.bytesBits, Zlib.Trees.Proofs.Out.natBits, pending, bits]
  rw [remainingZero, List.append_nil, before, List.nil_append] at output
  have bodyGrammar := grammar padding (fun isStored => by rw [storedPad isStored]; rfl)
  have block : ZlibF.Spec.Blocks [] [] (ZlibF.Spec.bytesToBits written) padding
      (inputPrefix input (represented xs)) := by
    rw [output, List.append_assoc, List.append_assoc]
    apply ZlibF.Spec.Blocks.last (Zlib.Trees.Proofs.Out.readBits_natBits 1 1 _ (by decide +kernel))
      (Zlib.Trees.Proofs.Out.readBits_natBits 2 kind _ (by omega))
    simpa only [inputPrefix, List.range_zero, List.map_nil, Nat.zero_add] using bodyGrammar
  refine ⟨produced, after, z', result, written, run, goodA, buffersA, account, sizes, storage,
    clearA, drainedA, validZero, bytes, padding, block, ?_⟩
  rw [Nat.mod_eq_of_lt padBound, List.drop_length]
  rfl

end Zlib.Deflate.Engine.Proofs
