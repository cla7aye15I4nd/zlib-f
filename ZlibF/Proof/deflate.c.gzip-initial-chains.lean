import ZlibF.Proof.«deflate.c.gzip-init-witness»
import ZlibF.Proof.«deflate.c.engine.initial»

namespace Zlib.Deflate.Engine.Proofs.DefaultGzipBoundary
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Proofs.DefaultGzipInit
open Zlib.Deflate.Proofs.DefaultInit (successfulBuffers stateHeap)
set_option autoImplicit false

/-- Empty actual hash heads after the gzip initializer establish chains0.
The fresh predecessor and window arrays remain arbitrary. This helper's
representation premise is produced by the actual initializer below. -/
theorem initialized_gzip_chains {h : Heap} {r : ZStreamRef} {z : ZStream} {level : Int32}
    {a1 a2 a3 : Array CtData} {qa : Array UInt16}
    (good : DGood (successHeap h r z level a1 a2 a3 qa) r h.nextBlk
      (resultStream h r z level) (resultState h r level a1 a2 a3)) :
    HeapChains (successHeap h r z level a1 a2 a3 qa) (resultState h r level a1 a2 a3) 0 := by
  obtain ⟨w, p, q, b, blocks⟩ := good.inv.blocks
  obtain ⟨wa, hw, _⟩ := blocks.wa
  obtain ⟨pa, hp, _⟩ := blocks.pa
  obtain ⟨heads, hq, size⟩ := blocks.qa
  have qid : q = h.nextBlk + 3 := by
    simpa only [resultState, finalState, lmD, resetState, rkPost, rkPost3, rkMid,
      Zlib.Trees.Proofs.Out.ibRec, Zlib.Trees.Proofs.Out.trInitRec,
      readyState, allocatedState, Ptr.ref.injEq, WRef.blk.injEq, and_true] using blocks.head.symm
  have eq : heads = clearHead qa 32768 := by
    rw [qid] at hq
    simpa [successHeap, readyHeap, successfulBuffers, publishedHeap, stateHeap, setW,
      Nat.add_assoc] using hq.symm
  have qs : 32768 ≤ qa.size := by
    rw [eq, size_clearHead] at size
    change qa.size = 32768 at size
    omega
  refine ⟨w, p, q, wa, pa, heads, blocks.win, blocks.prev, blocks.head, hw, hp, hq, ?_⟩
  apply chains_empty
  intro k hk
  change k < 32768 at hk
  rw [eq]
  have zero := clear_head_zero qa 32768 (by decide) qs k hk
  simp only [wfn, Array.getD_eq_getD_getElem?, zero, Option.getD_some]

end Zlib.Deflate.Engine.Proofs.DefaultGzipBoundary
