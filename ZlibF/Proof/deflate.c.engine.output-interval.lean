import ZlibF.Proof.«deflate.c.engine.raw-output-interval»

/-! # Exact raw caller output intervals through actual strategy execution -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real macro's exact interval can be composed without repackaging array witnesses. -/
theorem flush_macro_run_output_effect {h after : Heap} {r : ZStreamRef}
    {ds pb ob oo w origin base produced : Nat} {z z' : ZStream} {d : DeflateState}
    {buf window : Array UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : ZlibF.Math.DeflateSymbols.Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + ZlibF.Math.DeflateSymbols.represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool)
    (run : FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after))
    (live : r.get after = some z') (account : StreamAccounting z z' 0 produced) :
    RawOutputInterval h after ob oo produced := by
  intro before getBefore
  exact flush_macro_run_output_interval good trees buffers positive pointer cursor memory pending bits ledger clear trace
    win get range balance accounted view last run live account getBefore

/-- The actual return wrapper only reads after publishing the block. -/
theorem flush_control_run_output_effect {h after : Heap} {r : ZStreamRef} {ds ob oo origin base produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {ret : Option block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (last : Bool)
    (run : FLUSH_BLOCK (some (.tab ds)) (if last then 1 else 0) h = .ok (ret, after))
    (live : r.get after = some z') (account : StreamAccounting z z' 0 produced) :
    RawOutputInterval h after ob oo produced := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, wa, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have accounted0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨amount, other, otherZ, otherD, _written, _remaining, _kind, _body, _padding,
      macroRun, goodA, _buffersA, accountA, _sizes, storage, _rest⟩ :=
    flush_block_only_publish boundary.good trees buffers positive pointer cursor memory pending bits
      ledger clear boundary.trace win get boundary.range balance0 accounted0 view last
  let control : Option block_state :=
    if otherZ.avail_out == 0 then
      if last then
        if otherD.pending != 0 || otherD.wrap != 0 then some finish_started else none
      else some need_more
    else none
  have tested : FLUSH_BLOCK (some (.tab ds)) (if last then 1 else 0) h = .ok (control, other) := by
    unfold FLUSH_BLOCK
    simp only [bind_app, macroRun, ldDeflateState_tab goodA.live.hs, goodA.live.back, zrd_eq, goodA.live.hz]
    by_cases empty : (otherZ.avail_out == 0) = true <;>
      by_cases queued : (otherD.pending != 0 || otherD.wrap != 0) = true <;>
      cases last <;> simp [control, empty, queued, pure_app]
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  have getA := goodA.live.hz
  rw [eq] at getA
  have sameZ : otherZ = z' := Option.some.inj (getA.symm.trans live)
  have count : amount = produced := (stream_accounting_counts_unique
    (by simpa only [sameZ] using accountA) account).2
  rw [← eq, ← count]
  exact flush_macro_run_output_effect boundary.good trees buffers positive pointer cursor memory pending bits
    ledger clear boundary.trace win get boundary.range balance0 accounted0 view last macroRun goodA.live.hz accountA

end Zlib.Deflate.Engine.Proofs
