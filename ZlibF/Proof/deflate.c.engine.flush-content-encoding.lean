import ZlibF.Proof.«deflate.c.engine.flush-control»

/-! # One actual flush restores content and retains its independently decoded output -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The complete actual flush macro simultaneously restores the next content
boundary and identifies the emitted block's independent byte meaning. Caller
output can be empty or short; its written bytes and the remaining pending
bits retain the entire encoding. All three real block choices are covered.
This is an internal zero-deferred-byte cutpoint for default memory and raw
output. Full strategy and public encoded histories remain separate. -/
theorem flush_block_only_content_encoding {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (last : Bool) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState)
      (before : List Bool) (written : List UInt8) (remaining : List Bool)
      (kind : Nat) (body padding : List Bool),
      FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      (63488 + (if last then 0 else 2) ≤ z.avail_out.toNat → result.pending.toNat = 0) ∧
      (last = true → result.bi_valid.toInt.toNat = 0) ∧ kind < 3 ∧
      padding.length < 8 ∧ (last = false → padding = []) ∧ (kind = 0 → padding = []) ∧
      ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits (if last then 1 else 0) 1 ++
          Zlib.Trees.Proofs.Out.natBits kind 2 ++ body ++ padding) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, window, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by
    simpa only [deferredCredit, available, ite_true] using balance
  have account0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨produced, after, z', result, written, remaining, kind, body, padding,
    run, goodA, buffersA, accountA, _sizes, _storage, clearA, _frequencies,
    _position, _low, bytesA, pendingA, drainedA, finalA, kindA, padBound,
    padNone, storedPad, outputA, grammarA⟩ :=
    flush_block_only_publish boundary.good trees buffers positive pointer cursor memory pending bits
      ledger clear boundary.trace win get boundary.range balance0 account0 view last
  obtain ⟨contentProduced, contentHeap, contentZ, contentD, contentRun,
    contentA, _contentBuffers, _contentAccount, _contentClear, frameA⟩ :=
    flush_block_only_content_boundary boundary buffers positive pointer cursor memory pending bits clear available last
  have heapEq : contentHeap = after :=
    (Prod.mk.inj (Except.ok.inj (contentRun.symm.trans run))).2
  rw [heapEq] at contentA
  have streamEq : contentZ = z' := Option.some.inj (contentA.good.live.hz.symm.trans goodA.live.hz)
  have stateEq : contentD = result := Option.some.inj (contentA.good.live.hs.symm.trans goodA.live.hs)
  rw [streamEq, stateEq] at contentA
  rw [stateEq] at frameA
  exact ⟨produced, after, z', result, Zlib.Trees.Proofs.Out.outBits buf d,
    written, remaining, kind, body, padding, run, contentA, buffersA, accountA,
    clearA, frameA, pending_bits_base trees cursor, bytesA, pendingA, drainedA,
    finalA, kindA, padBound, padNone, storedPad, outputA, grammarA⟩

/-- The real nonfinal wrapper retains the same block meaning and restored
content boundary on both branches of its actual output-full decision. -/
theorem flush_nonfinal_content_encoding {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState)
      (before : List Bool) (written : List UInt8) (remaining : List Bool) (kind : Nat) (body : List Bool),
      FLUSH_BLOCK (some (.tab ds)) 0 h =
        .ok ((if z'.avail_out == 0 then some need_more else none), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      kind < 3 ∧ ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
      ∀ suffix : List Bool, (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Body [] kind (inputPrefix input base) (body ++ suffix) suffix
          (inputPrefix input (base + represented xs)) := by
  obtain ⟨produced, after, z', result, before, written, remaining, kind, body, padding,
    run, boundaryA, buffersA, accountA, clearA, frameA, beforeA, bytesA, pendingA,
    _drained, _final, kindA, _padBound, padNone, _storedPad, outputA, grammarA⟩ :=
    flush_block_only_content_encoding boundary buffers positive pointer cursor memory pending bits clear available false
  have emptyPadding := padNone rfl
  rw [emptyPadding, List.append_nil] at outputA
  refine ⟨produced, after, z', result, before, written, remaining, kind, body,
    ?_, boundaryA, buffersA, accountA, clearA, frameA, beforeA, bytesA, pendingA, kindA, outputA, grammarA⟩
  have run0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 h = .ok ((), after) := run
  unfold FLUSH_BLOCK
  simp only [bind_app, run0, ldDeflateState_tab boundaryA.good.live.hs,
    boundaryA.good.live.back, zrd_eq, boundaryA.good.live.hz]
  by_cases empty : (z'.avail_out == 0) = true <;> simp [empty, pure_app]

/-- The actual nonfinal flush's decoded body extends any later independently
valid block continuation. The stored choice retains its real byte-alignment
condition. No specification of an unproved C callee is assumed: the supplied
continuation is solely a mathematical parser derivation for later bits. -/
theorem flush_nonfinal_content_continuation {h : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState)
      (before : List Bool) (written : List UInt8) (remaining : List Bool) (kind : Nat) (body : List Bool),
      FLUSH_BLOCK (some (.tab ds)) 0 h =
        .ok ((if z'.avail_out == 0 then some need_more else none), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      PendingBits h d before ∧ Bytes after z.next_out produced written ∧ PendingBits after result remaining ∧
      kind < 3 ∧ ZlibF.Spec.bytesToBits written ++ remaining = before ++
        (Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ∧
      ∀ (suffix rest : List Bool) (decoded : List UInt8), (kind = 0 → suffix.length % 8 = 0) →
        ZlibF.Spec.Blocks [] (inputPrefix input (base + represented xs)) suffix rest decoded →
        ZlibF.Spec.Blocks [] (inputPrefix input base)
          ((Zlib.Trees.Proofs.Out.natBits 0 1 ++ Zlib.Trees.Proofs.Out.natBits kind 2 ++ body) ++ suffix)
          rest decoded := by
  obtain ⟨produced, after, z', result, before, written, remaining, kind, body,
    run, boundaryA, buffersA, accountA, clearA, frameA, beforeA, bytesA, pendingA,
    kindA, outputA, grammarA⟩ :=
    flush_nonfinal_content_encoding boundary buffers positive pointer cursor memory pending bits clear available
  refine ⟨produced, after, z', result, before, written, remaining, kind, body,
    run, boundaryA, buffersA, accountA, clearA, frameA, beforeA, bytesA, pendingA, kindA, outputA, ?_⟩
  intro suffix rest decoded aligned next
  simp only [List.append_assoc]
  exact ZlibF.Spec.Blocks.more
    (Zlib.Trees.Proofs.Out.readBits_natBits 1 0 _ (by decide +kernel))
    (Zlib.Trees.Proofs.Out.readBits_natBits 2 kind _ (by omega)) (grammarA suffix aligned) next

end Zlib.Deflate.Engine.Proofs
