import ZlibF.Proof.«deflate.c.engine.full-storage»
import ZlibF.Proof.«deflate.c.engine.flush-macro-counters»
import ZlibF.Proof.«deflate.c.engine.flush-end-frontier»

/-! # Complete object and allocation effects of the actual strategy -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Private read/write effects may be composed with later caller output. -/
theorem full_private_frame_add_output {h g : Heap} {r : ZStreamRef} {ds ob : Nat} {d : DeflateState}
    (frame : Frame h g (fun b => StreamRoot r b ∨ DeflateOwned ds d b)) :
    Frame h g (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) :=
  full_frame_weaken frame (fun _ changed => changed.elim Or.inl (fun owned => Or.inr (Or.inl owned)))

/-- The exact publication storage frame lies within the private blocks,
stream root and caller output allocation. -/
theorem OutputStorage.private_frame {h g : Heap} {r : ZStreamRef} {ds pb ob : Nat} {d : DeflateState}
    (storage : OutputStorage h g r ds pb ob) (pending : d.pending_buf = .ref (.blk pb) 0) :
    Frame h g (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) := by
  apply full_frame_weaken storage.frame
  intro b changed
  rcases changed with root | state | same | output
  · exact Or.inl root
  · exact Or.inr (Or.inl (Or.inl state))
  · subst b; exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr pending)))))
  · exact Or.inr (Or.inr output)

/-- Actual computed block publication retains its complete storage frame. -/
theorem flush_macro_run_output_storage {h : Heap} {r : ZStreamRef} {ds pb ob oo w origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf window : Array UInt8} {xs : List Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool)
    {after : Heap} (run : FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after)) :
    OutputStorage h after r ds pb ob := by
  obtain ⟨_produced, other, _z', _result, _written, _remaining, _kind, _body, _padding,
      tested, _goodA, _buffersA, _accountA, _sizes, storage, _rest⟩ :=
    flush_block_only_publish good trees buffers positive pointer cursor memory pending bits ledger clear trace
      win get range balance accounted view last
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  rw [← eq]
  exact storage

/-- The actual return wrapper only reads after publishing the block. -/
theorem flush_control_run_full_storage {h after : Heap} {r : ZStreamRef} {ds ob oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {ret : Option block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.blk ob) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (last : Bool)
    (run : FLUSH_BLOCK (some (.tab ds)) (if last then 1 else 0) h = .ok (ret, after))
 :
    Shape h after ∧ Frame h after (fun b => StreamRoot r b ∨ DeflateOwned ds d b ∨ b = ob) ∧
      LiveChange h after (fun _ => False) (fun _ => False) ∧ after.nalloc = h.nalloc ∧ after.nextBlk = h.nextBlk := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, wa, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have accounted0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨_amount, other, otherZ, otherD, _written, _remaining, _kind, _body, _padding,
      macroRun, goodA, _buffersA, _accountA, _sizes, storage, _rest⟩ :=
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
  rw [← eq]
  exact ⟨storage.shape, storage.private_frame trees.base.pbuf, full_shape_live_change storage.shape,
    storage.nalloc, storage.nextBlk⟩

end Zlib.Deflate.Engine.Proofs
