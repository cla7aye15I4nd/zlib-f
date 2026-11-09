import ZlibF.Proof.«deflate.c.engine.generic-foreign-owner-readonly-algebra»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_flush_macro_run_owner_readonly {h : Heap} {r : ZStreamRef} {ds pb owner oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool)
    {after : Heap} (run : FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after)) :
    ForeignOwnerReadonly h after owner := by
  obtain ⟨_produced,other,_z',_result,_written,_remaining,_kind,_body,_padding,
    tested,_goodA,_buffersA,_accountA,_sizes,_storage,_fields,_low,_final,_clear,_count,
    _frequencies,_cursor,_phase,_position,_bytes,_pending,bufferFrame,_rest⟩ :=
    default_flush_block_only_foreign_publish good trees buffers positive pointer cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  have fields := ForeignOwnerReadonly.of_buffer_frame good buffers pointer bufferFrame
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [← eq]
  exact fields

/-- The actual return wrapper only reads after publishing the block. -/
theorem default_foreign_flush_control_run_owner_readonly {h after : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {ret : Option block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (last : Bool)
    (run : FLUSH_BLOCK (some (.tab ds)) (if last then 1 else 0) h = .ok (ret, after))
 :
    ForeignOwnerReadonly h after owner := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, wa, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have accounted0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨_amount, other, otherZ, otherD, _written, _remaining, _kind, _body, _padding,
      macroRun, goodA, _buffersA, _accountA, _sizes, storage, _rest⟩ :=
    default_flush_block_only_foreign_publish boundary.good trees buffers positive pointer cursor memory pending bits
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
  have fields := default_foreign_flush_macro_run_owner_readonly boundary.good trees buffers positive pointer cursor memory pending bits
    ledger clear boundary.trace win get boundary.range balance0 accounted0 view last macroRun
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [← eq]
  exact fields

end Zlib.Deflate.Engine.Proofs
