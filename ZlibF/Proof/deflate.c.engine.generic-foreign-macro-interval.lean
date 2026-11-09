import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-content»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-body-encoding»
import ZlibF.Proof.«deflate.c.engine.generic-output-append»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- A real private frame leaves every admitted foreign caller output byte unchanged. -/
theorem ByteOutputInterval.of_foreign_private_frame {h g : Heap} {r : ZStreamRef} {ds owner offset produced : Nat}
    {z : ZStream} {d : DeflateState} (good : DGood h r ds z d) (buffers : StreamBuffers h r)
    (pointer : z.next_out=.ref (.dstate_depth owner) offset)
    (frame : Frame h g (fun b => StreamRoot r b ∨ DeflateOwned ds d b)) :
    ByteOutputInterval h g (.dstate_depth owner) offset produced :=
  .of_same (private_frame_foreign_output_same good buffers pointer frame)

/-- Deterministic source execution identifies the actual heap and accounted output count. -/
theorem ByteOutputInterval.identify {α : Type} {program : M α} {h other after : Heap}
    {a b : α} {r : ZStreamRef} {z firstZ finalZ : ZStream} {ref : BRef}
    {offset firstUsed finalUsed firstOut finalOut : Nat}
    (tested : program h=.ok (a,other)) (run : program h=.ok (b,after))
    (firstLive : r.get other=some firstZ) (finalLive : r.get after=some finalZ)
    (firstAccount : StreamAccounting z firstZ firstUsed firstOut)
    (finalAccount : StreamAccounting z finalZ finalUsed finalOut)
    (effect : ByteOutputInterval h other ref offset firstOut) :
    ByteOutputInterval h after ref offset finalOut := by
  have heaps := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  have streams := actual_run_stream_unique tested run firstLive finalLive
  rw [streams] at firstAccount
  have count := (stream_accounting_counts_unique firstAccount finalAccount).2
  rw [← heaps,← count]
  exact effect

theorem default_foreign_flush_macro_run_output_interval {h after : Heap} {r : ZStreamRef}
    {ds pb owner oo w origin base produced : Nat} {z z' : ZStream} {d : DeflateState}
    {buf window : Array UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol} {input : Nat → UInt8}
    (good : DGood h r ds z d) (trees : Zlib.Trees.Proofs.Out.TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (positive : 0 < d.level.toInt) (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (ledger : SymbolLedger buf d xs) (clear : BlockInit.BlockClear d) (trace : ZlibF.Math.DeflateSymbols.Trace input base xs)
    (win : d.window = .ref (.blk w) 0) (get : h.bytes w = some window)
    (range : fillEnd d ≤ d.window_size.toNat) (balance : BlockBalance d xs 0)
    (accounted : base + ZlibF.Math.DeflateSymbols.represented xs = origin + d.strstart.toNat)
    (view : ∀ i, i < fillEnd d → bfn window i = input (origin + i)) (last : Bool)
    (run : FLUSH_BLOCK_ONLY (some (.tab ds)) (if last then 1 else 0) h = .ok ((), after))
    (live : r.get after = some z') (account : StreamAccounting z z' 0 produced) :
    ByteOutputInterval h after (.dstate_depth owner) oo produced := by
  obtain ⟨amount,other,otherZ,otherD,_written,_remaining,_kind,_body,_padding,
    actual,goodA,_buffersA,accountA,_sizes,_storage,_frame,_low,_final,_clear,_count,_freq,
    _cursor,_phase,_position,_bytes,_pending,bufferFrame,_rest⟩ :=
    default_flush_block_only_foreign_publish good trees buffers positive pointer cursor memory pending bits
      ledger clear trace win get range balance accounted view last
  have effect : ByteOutputInterval h other (.dstate_depth owner) oo amount := by
    apply ByteOutputInterval.of_buffer_frame
    simpa only [pointer] using bufferFrame
  exact ByteOutputInterval.identify actual run goodA.live.hz live accountA account effect

/-- The actual return wrapper only reads after publishing the block. -/
theorem default_foreign_flush_control_run_output_interval {h after : Heap} {r : ZStreamRef} {ds owner oo origin base produced : Nat}
    {z z' : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    {ret : Option block_state}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) (last : Bool)
    (run : FLUSH_BLOCK (some (.tab ds)) (if last then 1 else 0) h = .ok (ret, after))
    (live : r.get after = some z') (account : StreamAccounting z z' 0 produced) :
    ByteOutputInterval h after (.dstate_depth owner) oo produced := by
  obtain ⟨pb, buf, trees, ledger, balance⟩ := boundary.symbols
  obtain ⟨w, wa, win, get, view, _form⟩ := boundary.data
  have balance0 : BlockBalance d xs 0 := by simpa only [deferredCredit, available, ite_true] using balance
  have accounted0 : base + represented xs = origin + d.strstart.toNat := by
    simpa only [pendingCredit, available, ite_true, Nat.add_zero] using boundary.accounted
  obtain ⟨amount, other, otherZ, otherD, _written, _remaining, _kind, _body, _padding,
      macroRun, goodA, _buffersA, accountA, _sizes, storage, _rest⟩ :=
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
  have eq := (Prod.mk.inj (Except.ok.inj (tested.symm.trans run))).2
  have getA := goodA.live.hz
  rw [eq] at getA
  have sameZ : otherZ = z' := Option.some.inj (getA.symm.trans live)
  have count : amount = produced := (stream_accounting_counts_unique
    (by simpa only [sameZ] using accountA) account).2
  rw [← eq, ← count]
  exact default_foreign_flush_macro_run_output_interval boundary.good trees buffers positive pointer cursor memory pending bits
    ledger clear boundary.trace win get boundary.range balance0 accounted0 view last macroRun goodA.live.hz accountA

end Zlib.Deflate.Engine.Proofs
