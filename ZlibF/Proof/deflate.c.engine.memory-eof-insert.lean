import ZlibF.Proof.«deflate.c.engine.eof-tail-encoding»

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Actual insertion reset keeps caller ranges and the exact content/frontiers. -/
theorem memory_eof_insert_content_buffers {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z : ZStream} {d : DeflateState} {xs : List Symbol} {input : Nat → UInt8}
    (boundary : ContentBoundary h r ds z d input origin base xs)
    (frontier : EndFrontier h d) (buffers : StreamBuffers h r) (empty : d.lookahead = 0) :
    wr (some (.tab ds)) eofInsert h = .ok ((), setD h ds (eofInsert d)) ∧
      ContentBoundary (setD h ds (eofInsert d)) r ds z (eofInsert d) input origin base xs ∧
      EndFrontier (setD h ds (eofInsert d)) (eofInsert d) ∧
      StreamBuffers (setD h ds (eofInsert d)) r ∧ ConfigFrame d (eofInsert d) := by
  obtain ⟨run, stateA, endA, configA⟩ := eof_insert_content_boundary boundary frontier empty
  have owned := stream_owned_keys boundary.good stateA.good rfl rfl rfl rfl
  have buffersA := stream_buffers_private_read boundary.good.live.hz stateA.good.live.hz buffers
    (byte_frame_setD h ds (eofInsert d))
    (fun k equal => (stream_owned_deflate boundary.good k).mpr (Or.inl equal)) owned (stream_accounting_zero z) rfl
  exact ⟨run, stateA, endA, buffersA, configA⟩

end Zlib.Deflate.Engine.Proofs
#print axioms Zlib.Deflate.Engine.Proofs.memory_eof_insert_content_buffers
