import ZlibF.Proof.«deflate.c.engine.generic-foreign-complete-pending»
import ZlibF.Proof.«deflate.c.engine.flush-arguments-aligned»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Real foreign-output block publication retains the source-selected stored branch's byte alignment. -/
theorem default_foreign_flush_block_only_publish_aligned {h : Heap} {r : ZStreamRef} {ds pb owner oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
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
      ByteSizes h after ∧ OutputStorage h after r ds pb owner ∧ BlockInit.BlockClear result ∧
      Zlib.Trees.Proofs.Out.InitialFrequencies result.dyn_ltree result.dyn_dtree ∧
      result.block_start = result.strstart.toUInt64.toInt64 ∧ result.bi_valid.toInt < 8 ∧
      Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      (63488 + (if last then 0 else 2) ≤ z.avail_out.toNat → result.pending.toNat = 0) ∧
      (last = true → result.bi_valid.toInt.toNat = 0) ∧ (kind = 0 → result.bi_valid.toInt.toNat = 0) ∧ kind < 3 ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧ (kind = 0 → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = Zlib.Trees.Proofs.Out.outBits buf d ++
        (Zlib.Trees.Proofs.Out.natBits (if last then 1 else 0) 1 ++
          Zlib.Trees.Proofs.Out.natBits kind 2 ++ body ++ padding) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  have arguments := default_flush_arguments good trees memory ledger win get range balance
  obtain ⟨ze, ready, emitted, outputBuf, kind, body, padding, run, goodE, treesE, buffersE,
    accountE, sizesE, storageE, ledgerE, clearE, sizeE, boundE, cursorE, finalE, storedE, kindBound,
    padBound, padNone, storedPad, outputE, grammar⟩ :=
    flush_default_ready_aligned (ob := owner) good trees buffers positive cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  let updated : DeflateState := { emitted with block_start := emitted.strstart.toUInt64.toInt64 }
  obtain ⟨updateRun, goodU, treesU, buffersU, sizesU, storageU⟩ :=
    flush_block_start_engine (ob := owner) goodE treesE buffersE
  have nextOut : ze.next_out = z.next_out := by rw [accountE.2.2.2.2.2.1, advance_zero]
  have pointerE : ze.next_out = .ref (.dstate_depth owner) oo := nextOut.trans pointer
  have available : ze.avail_out.toNat = z.avail_out.toNat := by have := accountE.2.2.2.1; omega
  have roomU : 8 * updated.pending.toNat + updated.bi_valid.toInt.toNat ≤ 8 * outputBuf.size := by
    rw [sizeE]
    have high := treesE.run.bi_hi
    have low := treesE.run.bi_lo
    change 8 * emitted.pending.toNat + emitted.bi_valid.toInt.toNat ≤ 524288
    omega
  obtain ⟨produced, after, z', result, written, remaining, flush, goodA, buffersA, accountA,
    sizesA, storageA, copied, left, low, validA, fieldsA, bytes, pendingA, outputA,_bufferFrame⟩ :=
    flush_pending_foreign_bits_frame goodU treesU buffersU pointerE cursorE roomU
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
  have stored : kind = 0 → result.bi_valid.toInt.toNat = 0 := by
    intro flag
    have validU : updated.bi_valid.toInt = 0 := storedE flag
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
    clearA, frequencies, position, low, bytesA, pendingA, drained, final, stored, kindBound,
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

end Zlib.Deflate.Engine.Proofs
