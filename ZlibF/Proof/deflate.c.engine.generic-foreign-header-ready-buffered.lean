import ZlibF.Proof.«deflate.c.engine.generic-header-ready»
import ZlibF.Proof.«deflate.c.engine.header-buffered»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Trees.Proofs.Out (TreesInvAt)
set_option autoImplicit false

/-- Actual private header preparation retains empty initialized content.
This source cut does not restrict the caller output representation. -/
theorem foreign_header_ready_buffered {h : Heap} {r : ZStreamRef} {ds pb origin base : Nat}
    {z : ZStream} {d : DeflateState} {buf : Array UInt8} {input : Nat → UInt8} {config : EngineConfig}
    (boundary : BufferedBoundary h r ds z d input origin base [] config)
    (trees : TreesInvAt h ds d pb buf) (buffers : StreamBuffers h r)
    (pending : d.pending = 0) (cursor : d.pending_out = d.pending_buf) :
    BufferedBoundary (levelHeaderReady h r ds pb z d buf) r ds {z with adler := 1}
      (levelHeaderState d) input origin base [] config ∧
    StreamBuffers (levelHeaderReady h r ds pb z d buf) r := by
  obtain ⟨goodA, _treesA, buffersA, _sizesA, _storageA, _accountA, _frameA, _preciseA, _values⟩ :=
    generic_zlib_header_ready_engine boundary.good trees buffers pending cursor
  have privateWindow : ∀ b, d.window = .ref (.blk b) 0 →
      (levelHeaderReady h r ds pb z d buf).bytes b = h.bytes b := by
    intro b win
    obtain ⟨w,p,q,pb0,blocks⟩ := boundary.good.inv.blocks
    have wid : w = b := by simpa only [win,Ptr.ref.injEq,BRef.blk.injEq,and_true] using blocks.win.symm
    have bid : pb0 = pb := by simpa only [trees.base.pbuf,Ptr.ref.injEq,BRef.blk.injEq,and_true] using blocks.pbuf.symm
    subst w pb0
    simp only [levelHeaderReady,setD_bytes,ZStreamRef.put_bytes,upd_ne _ _ _ _ blocks.wb]
  have words : (levelHeaderReady h r ds pb z d buf).words = h.words := by
    simp only [levelHeaderReady,setD_words,ZStreamRef.put_words]
  have fields : levelHeaderState d = { d with
      pending := (levelHeaderState d).pending,
      pending_out := (levelHeaderState d).pending_out, status := (levelHeaderState d).status,
      last_flush := (levelHeaderState d).last_flush, wrap := (levelHeaderState d).wrap} := by rfl
  have contentA := empty_content_control_transfer boundary.toContentBoundary goodA privateWindow words fields
  have frontierA : EndFrontier (levelHeaderReady h r ds pb z d buf) (levelHeaderState d) := by
    have chains := control_heap_chains boundary.end_frontier privateWindow words fields
    exact chains
  have configuration : ConfigFrame d (levelHeaderState d) := by rfl
  have clearA : BlockInit.BlockClear (levelHeaderState d) :=
    ⟨boundary.clear.bl,boundary.clear.opt,boundary.clear.fixed⟩
  have cursorA : (levelHeaderState d).pending = 0 →
      (levelHeaderState d).pending_out = (levelHeaderState d).pending_buf := by
    intro impossible
    cases (show (2 : UInt64) ≠ 0 from by decide) impossible
  exact ⟨⟨contentA,Eq.trans configuration boundary.configuration,clearA,boundary.bits,
    boundary.strict,frontierA,cursorA⟩,buffersA⟩
end Zlib.Deflate.Engine.Proofs
