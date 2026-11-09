import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-aligned»
import ZlibF.Proof.«deflate.c.engine.generic-foreign-macro-content»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

theorem default_foreign_flush_nonfinal_end_boundary {h : Heap} {r : ZStreamRef} {ds owner oo origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs) (frontier : EndFrontier h d)
    (buffers : StreamBuffers h r) (positive : 0 < d.level.toInt)
    (pointer : z.next_out = .ref (.dstate_depth owner) oo) (cursor : d.pending_out = d.pending_buf)
    (memory : d.lit_bufsize.toNat = 16384) (pending : d.pending = 0) (bits : d.bi_valid.toInt ≤ 7)
    (clear : BlockInit.BlockClear d) (available : d.match_available = 0) :
    ∃ (produced : Nat) (after : Heap) (z' : ZStream) (result : DeflateState),
      FLUSH_BLOCK (some (.tab ds)) 0 h =
        .ok ((if z'.avail_out == 0 then some need_more else none), after) ∧
      ContentBoundary after r ds z' result input origin (base + represented xs) [] ∧ EndFrontier after result ∧
      StreamBuffers after r ∧ StreamAccounting z z' 0 produced ∧ BlockInit.BlockClear result ∧
      FlushWorkFrame { d with block_start := d.strstart.toUInt64.toInt64 } result ∧
      result.bi_valid.toInt < 8 ∧ (0 < z'.avail_out.toNat → PublishReady result) := by
  obtain ⟨produced,after,z',result,_before,_written,_remaining,_kind,_body,_padding,
    run,boundaryA,endA,buffersA,accountA,clearA,frameA,lowA,phaseA,_rest⟩ :=
    default_foreign_flush_macro_content_encoding boundary frontier buffers positive pointer cursor memory pending bits clear available false
  have run0 : FLUSH_BLOCK_ONLY (some (.tab ds)) 0 h=.ok ((),after) := run
  refine ⟨produced,after,z',result,?_,boundaryA,endA,buffersA,accountA,clearA,frameA,lowA,phaseA⟩
  unfold FLUSH_BLOCK
  simp only [bind_app,run0,ldDeflateState_tab boundaryA.good.live.hs,boundaryA.good.live.back,zrd_eq,boundaryA.good.live.hz]
  by_cases empty : (z'.avail_out==0)=true <;> simp [empty,pure_app]

end Zlib.Deflate.Engine.Proofs
