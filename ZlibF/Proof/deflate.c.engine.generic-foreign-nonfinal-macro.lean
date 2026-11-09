import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-content»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-positive-loop»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- The real nonfinal control wrapper retains the initialized content
boundary and the publication phase needed for another loop iteration.
Its need_more test uses the same returned stream as the phase conclusion. -/
theorem default_foreign_flush_nonfinal_loop_boundary {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK (some (.tab ds)) 0 h =
        .ok ((if z'.avail_out == 0 then some need_more else none), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) ∧ StrategyControls d result := by
  obtain ⟨produced,after,z',result,_before,_written,_remaining,_kind,_body,_padding,
      macroRun,stateA,_endA,buffersA,accountA,clearA,fields,lowA,readyA,cursorA,_rest⟩ :=
    default_foreign_flush_macro_content_encoding boundary frontier buffers positive pointer cursor memory pending bits clear available false
  have controlsA : StrategyControls d result:=⟨cursorA,by rw [fields],by rw [fields]⟩
  refine ⟨produced,after,z',result,?_,stateA,buffersA,accountA,clearA,fields,lowA,readyA,controlsA⟩
  have run0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 h=.ok ((),after):=macroRun
  unfold FLUSH_BLOCK
  simp only [bind_app,run0,ldDeflateState_tab stateA.good.live.hs,stateA.good.live.back,zrd_eq,stateA.good.live.hz]
  by_cases empty : (z'.avail_out==0)=true <;> simp [empty,pure_app]

end Zlib.Deflate.Engine.Proofs
