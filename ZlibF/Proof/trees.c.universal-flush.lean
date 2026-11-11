import ZlibF.Proof.«trees.c.universal-block»
import ZlibF.Proof.«deflate.c.engine.flush-arguments»
import ZlibF.Proof.«deflate.c.engine.pending-empty-cursor»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-complete-pending»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-pending-phase»
import ZlibF.Proof.«deflate.c.engine.flush-frame»

/-!
# trees.c: `FLUSH_BLOCK_ONLY` for every block choice and every memLevel

Batch C of the deflate skeleton. The macro computes the stored source (`window + block_start`,
or `NULL` after a slide made `block_start` negative) and the checked signed length
`strstart - block_start`, runs `_tr_flush_block` (`tr_flush_block_safe`), sets `block_start` to
`strstart` and publishes the pending bytes with `flush_pending`.
-/

namespace Zlib.Deflate.Universal.Block
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The checked signed length `(long)s->strstart - s->block_start` of the macro, when
`-w_size ≤ block_start ≤ strstart ≤ window_size`. -/
theorem flush_length_general {d : DeflateState}
    (low : -(d.w_size.toNat : Int) ≤ d.block_start.toInt) (high : d.block_start.toInt ≤ d.strstart.toNat)
    (range : d.strstart.toNat ≤ 65536) (wsize : d.w_size.toNat ≤ 32768) :
    let value := (d.strstart.toNat : Int) - d.block_start.toInt
    lsub d.strstart.toUInt64.toInt64 d.block_start = pure (Int64.ofInt value) ∧
      (Int64.ofInt value).toUInt64.toNat = value.toNat ∧
      (Int64.ofInt value).toUInt64.toNat ≤ 98304 := by
  have valueLo : 0 ≤ (d.strstart.toNat : Int) - d.block_start.toInt := by omega
  have startBound := d.strstart.toNat_lt
  have cast : d.strstart.toUInt64.toInt64.toInt = (d.strstart.toNat : Int) := by
    rw [Int64.toInt, UInt64.toBitVec_toInt64, BitVec.toInt_eq_toNat_of_lt]
    · simp
    · simp
      omega
  dsimp only
  have word : (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64.toNat =
      ((d.strstart.toNat : Int) - d.block_start.toInt).toNat := by
    change (BitVec.ofInt 64 ((d.strstart.toNat : Int) - d.block_start.toInt)).toNat = _
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt valueLo (by omega)]
  refine ⟨?_, word, by rw [word]; omega⟩
  unfold lsub chk64
  rw [cast]
  rw [if_pos (show -9223372036854775808 ≤ (d.strstart.toNat : Int) - d.block_start.toInt ∧
    (d.strstart.toNat : Int) - d.block_start.toInt ≤ 9223372036854775807 by omega)]

/-- The stored source the macro passes: a slice of the window from `block_start`, or `NULL`. -/
def flushSource (d : DeflateState) (window : Nat) : BPtr :=
  if 0 ≤ d.block_start.toInt then .ref (.blk window) d.block_start.toInt.toNat else .null

/-- The macro's argument evaluation (`flushOnlyArguments`), with the checked pointer
addition and signed subtraction, and the validity of the stored source. -/
theorem flush_arguments_general {h : Heap} {r : ZStreamRef} {ds pb w : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (low : -(d.w_size.toNat : Int) ≤ d.block_start.toInt) (high : d.block_start.toInt ≤ d.strstart.toNat)
    (range : d.strstart.toNat ≤ d.window_size.toNat) :
    let len := UInt64.ofNat ((d.strstart.toNat : Int) - d.block_start.toInt).toNat
    flushOnlyArguments (some (.tab ds)) h = .ok ((flushSource d w, len), h) ∧
      StoredSource h pb (flushSource d w) len ∧ len.toNat ≤ 4294967296 := by
  have size := window_extent good win get
  have wsize : d.w_size.toNat ≤ 32768 := by
    have bits := good.inv.wbits_hi
    have wsz := good.inv.wsize
    have pow : 2 ^ d.w_bits.toNat ≤ 2 ^ 15 := Nat.pow_le_pow_right (by decide) bits
    omega
  have difference := flush_length_general low high (by omega) wsize
  dsimp only at difference
  have lenEq : (Int64.ofInt ((d.strstart.toNat : Int) - d.block_start.toInt)).toUInt64 =
      UInt64.ofNat ((d.strstart.toNat : Int) - d.block_start.toInt).toNat := by
    apply UInt64.toNat_inj.mp
    rw [difference.2.1, UInt64.toNat_ofNat']
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have lenNat : (UInt64.ofNat ((d.strstart.toNat : Int) - d.block_start.toInt).toNat).toNat =
      ((d.strstart.toNat : Int) - d.block_start.toInt).toNat := by
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  have separate : pb ≠ w := stored_window_separate good trees win
  dsimp only
  refine ⟨?_, ?_, by rw [lenNat]; omega⟩
  · unfold flushOnlyArguments
    rw [bind_app, ldDeflateState_tab good.live.hs]
    by_cases nonnegative : 0 ≤ d.block_start.toInt
    · have cast : d.block_start.toUInt64.toUInt32.toNat = d.block_start.toInt.toNat := by
        rw [UInt64.toNat_toUInt32, Int64.toNat_toUInt64_of_le (show 0 ≤ d.block_start from by
          simpa only [Int64.le_iff_toInt_le, Int64.toInt_zero] using nonnegative)]
        change d.block_start.toInt.toNat % 4294967296 = d.block_start.toInt.toNat
        exact Nat.mod_eq_of_lt (by omega)
      have add := padd_ok' (r := BRef.blk w) (a := window) (off := 0)
        (n := d.block_start.toUInt64.toUInt32.toNat) get (by rw [cast]; omega)
      change (do
        let source ← if d.block_start ≥ 0 then padd d.window d.block_start.toUInt64.toUInt32.toNat else pure Ptr.null
        let length ← lsub d.strstart.toUInt64.toInt64 d.block_start
        return (source, length.toUInt64)) h = _
      rw [if_pos (show d.block_start ≥ 0 from by
        simpa only [Int64.le_iff_toInt_le, Int64.toInt_zero] using nonnegative), win, bind_app, add]
      rw [difference.1]
      simp only [bind_app, pure_app, cast, Nat.zero_add, lenEq, flushSource, nonnegative, ite_true]
    · change (do
        let source ← if d.block_start ≥ 0 then padd d.window d.block_start.toUInt64.toUInt32.toNat else pure Ptr.null
        let length ← lsub d.strstart.toUInt64.toInt64 d.block_start
        return (source, length.toUInt64)) h = _
      rw [if_neg (show ¬ d.block_start ≥ 0 from by
        simpa only [Int64.le_iff_toInt_le, Int64.toInt_zero] using nonnegative), difference.1]
      simp only [bind_app, pure_app, lenEq, flushSource, nonnegative, ite_false]
  · by_cases nonnegative : 0 ≤ d.block_start.toInt
    · refine Or.inr ⟨w, d.block_start.toInt.toNat, window, ?_, get, separate, ?_⟩
      · simp only [flushSource, nonnegative, ite_true]
      · rw [lenNat]
        omega
    · left
      simp only [flushSource, nonnegative, ite_false]

/-- `FlushFrame` is the frame `FlushWorkFrame` of the default flush proofs (the same fields). -/
theorem FlushFrame.work {a b : DeflateState} (frame : FlushFrame a b) : FlushWorkFrame a b := by
  unfold FlushFrame at frame
  unfold FlushWorkFrame
  rw [frame]

/-- **`FLUSH_BLOCK_ONLY(s, last)` at a positive level, every block choice, every memLevel.**
From a drained entry with the recorded symbols, cleared costs, the window shape
(`-w_size ≤ block_start ≤ strstart ≤ window_size`), a non-`NULL` output pointer and the overlay
room of the dynamic branch, the macro does not fault. Afterwards the stream invariants and the
caller buffers hold, the stream record changed only by the published output
(`StreamAccounting z z' 0 produced`), the block is empty and cleared, `block_start = strstart`,
at most seven bits are held, and the pending cursor is consistent. -/
theorem flush_block_only_safe {h : Heap} {r : ZStreamRef} {ds pb ob w : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt)
    (pointer : (∃ oo, z.next_out = .ref (.blk ob) oo) ∨ (∃ oo, z.next_out = .ref (.dstate_depth ob) oo))
    (cursor : d.pending_out = d.pending_buf) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (low : -(d.w_size.toNat : Int) ≤ d.block_start.toInt) (high : d.block_start.toInt ≤ d.strstart.toNat)
    (range : d.strstart.toNat ≤ d.window_size.toNat)
    (overlay : ∀ z', DynamicOverlay (r.put h z') ds d xs) (last : Bool) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      DGood after r ds z' result ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧
      ByteSizes h after ∧ OutputStorage h after r ds pb ob ∧
      BlockInit.BlockClear result ∧ (∃ b, SymbolLedger b result []) ∧ result.bi_valid.toInt < 8 ∧
      (last = true → result.bi_valid.toInt = 0) ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      FlushFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      (result.pending = 0 ∨ z'.avail_out = 0) := by
  obtain ⟨arguments, sourceOk, lenWord⟩ := flush_arguments_general good trees win get low high range
  obtain ⟨ze, ready, emitted, outputBuf, run, goodE, treesE, buffersE, accountE, sizesE, storageE,
    ledgerE, clearE, sizeE, cursorE, roomE, finalE⟩ :=
    tr_flush_block_safe (ob := ob) good trees buffers positive cursor pending bits ledger clear
      (flushSource d w) _ sourceOk lenWord overlay last
  let updated : DeflateState := { emitted with block_start := emitted.strstart.toUInt64.toInt64 }
  obtain ⟨updateRun, goodU, treesU, buffersU, sizesU, storageU⟩ :=
    flush_block_start_engine (ob := ob) goodE treesE buffersE
  have nextOut : ze.next_out = z.next_out := by rw [accountE.2.2.2.2.2.1, advance_zero]
  have roomU : 8 * updated.pending.toNat + updated.bi_valid.toInt.toNat ≤ 8 * outputBuf.size := by
    rw [sizeE]
    exact roomE
  have publish : ∃ produced after z' result,
      flush_pending (some r) (setD ready ds updated) = .ok ((), after) ∧ DGood after r ds z' result ∧
      StreamBuffers after r ∧ StreamAccounting ze z' 0 produced ∧ ByteSizes (setD ready ds updated) after ∧
      OutputStorage (setD ready ds updated) after r ds pb ob ∧ result.bi_valid.toInt < 8 ∧
      result.bi_valid.toInt.toNat = updated.bi_valid.toInt.toNat % 8 ∧
      result = { updated with
        pending := result.pending, pending_out := result.pending_out, bi_buf := result.bi_buf,
        bi_valid := result.bi_valid, bi_used := result.bi_used } ∧
      (result.pending = 0 → result.pending_out = result.pending_buf) ∧
      (result.pending = 0 ∨ z'.avail_out = 0) := by
    rcases pointer with ⟨oo, pointer⟩ | ⟨oo, pointer⟩
    · have pointerE : ze.next_out = .ref (.blk ob) oo := nextOut.trans pointer
      obtain ⟨produced, after, z', result, _written, _remaining, flush, goodA, buffersA, accountA,
        sizesA, storageA, copied, left, low, validA, fieldsA, _bytes, _pendingA, _outputA⟩ :=
        flush_pending_raw_bits goodU treesU buffersU pointerE cursorE roomU
      refine ⟨produced, after, z', result, flush, goodA, buffersA, accountA, sizesA, storageA, low, validA,
        fieldsA, raw_pending_run_empty_cursor goodU treesU buffersU pointerE cursorE roomU flush goodA.live.hs, ?_⟩
      have out := accountA.2.2.2.1
      by_cases full : produced = ze.avail_out.toNat
      · right; apply UInt32.toNat_inj.mp; change z'.avail_out.toNat = 0; omega
      · left; apply UInt64.toNat_inj.mp; change result.pending.toNat = 0; omega
    · have pointerE : ze.next_out = .ref (.dstate_depth ob) oo := nextOut.trans pointer
      obtain ⟨produced, after, z', result, _written, _remaining, flush, goodA, buffersA, accountA,
        sizesA, storageA, copied, left, low, validA, fieldsA, _bytes, _pendingA, _outputA, _bufferA⟩ :=
        flush_pending_foreign_bits_frame goodU treesU buffersU pointerE cursorE roomU
      refine ⟨produced, after, z', result, flush, goodA, buffersA, accountA, sizesA, storageA, low, validA,
        fieldsA, foreign_pending_run_empty_cursor goodU treesU buffersU pointerE cursorE roomU flush goodA.live.hs, ?_⟩
      have out := accountA.2.2.2.1
      by_cases full : produced = ze.avail_out.toNat
      · right; apply UInt32.toNat_inj.mp; change z'.avail_out.toNat = 0; omega
      · left; apply UInt64.toNat_inj.mp; change result.pending.toNat = 0; omega
  obtain ⟨produced, after, z', result, flush, goodA, buffersA, accountA, sizesA, storageA, low, validA,
    fieldsA, cursorA, drained⟩ := publish
  have ledgerU : SymbolLedger outputBuf updated [] := ledgerE.keep rfl rfl rfl rfl
  have ledgerA : SymbolLedger outputBuf result [] := by rw [fieldsA]; exact ledgerU.keep rfl rfl rfl rfl
  have clearA : BlockInit.BlockClear result := by rw [fieldsA]; exact ⟨clearE.bl, clearE.opt, clearE.fixed⟩
  have final : last = true → result.bi_valid.toInt = 0 := by
    intro flag
    have validU : updated.bi_valid.toInt = 0 := finalE.1 flag
    rw [validU] at validA
    have nonnegative := goodA.inv.bits.1
    simp only [Int.toNat_zero, Nat.zero_mod] at validA
    omega
  have frameA : FlushFrame { d with block_start := d.strstart.toUInt64.toInt64 } result := by
    have frameE := finalE.2
    unfold FlushFrame at frameE ⊢
    rw [fieldsA]
    dsimp only [updated]
    rw [frameE]
  have account : StreamAccounting z z' 0 produced := by
    simpa only [Nat.zero_add] using stream_accounting_trans accountE accountA
  refine ⟨produced, after, z', result, ?_, goodA, buffersA, account, (sizesE.trans sizesU).trans sizesA,
    (storageE.trans storageU).trans storageA, clearA, ⟨outputBuf, ledgerA⟩, low, final, cursorA, frameA, drained⟩
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

end Zlib.Deflate.Universal.Block
