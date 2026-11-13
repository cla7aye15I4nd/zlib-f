import ZlibF.Proof.«deflate.c.engine.stream-control»
import ZlibF.Proof.«deflate.c.engine.finish-protocol»

/-! # Entry error returns retain the initialized protocol -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Stream-only scalar stores preserve every private protocol phase. -/
theorem default_phase_stream_control {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d : DeflateState} {config : EngineConfig}
    (boundary : DefaultFinishBoundary h r ds z d config)
    (goodA : DGood (r.put h z') r ds z' d) (adler : z'.adler = z.adler) :
    (∃ input origin base, EngineStart (r.put h z') r ds z' d ∧
      BufferedBoundary (r.put h z') r ds z' d input origin base [] config) ∨
      PublicFinishPhase (r.put h z') r ds z' d config := by
  rcases boundary.phase with ⟨input, origin, base, start, state⟩ | working | finishing
  · have chainsA : HeapChains (r.put h z') d 0 :=
      control_heap_chains start.chains (fun _ _ => by simp only [ZStreamRef.put_bytes])
        (by simp only [ZStreamRef.put_words]) rfl
    have startA : EngineStart (r.put h z') r ds z' d :=
      { start with good := goodA, chains := chainsA, adler := adler.trans start.adler }
    exact Or.inl ⟨input, origin, base, startA, stream_control_buffered state goodA⟩
  · obtain ⟨input, origin, base, xs, state, status⟩ := working
    exact Or.inr (Or.inl ⟨input, origin, base, xs, stream_control_buffered state goodA, status⟩)
  · exact Or.inr (Or.inr finishing)

/-- A real entry refusal before private mutation preserves the complete
initialized protocol and actual reachability. The actual static-message
callee is proved; the source prefix must establish the displayed equality. -/
theorem public_entry_refusal_protocol {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} {config : EngineConfig} (flush err : Int32)
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (source : deflate (some r) flush h = ERR_RETURN (some r) err h) :
    ∃ message,
      let z' := { z with msg := message }
      let after := r.put h z'
      deflate (some r) flush h = .ok (err, after) ∧
      DefaultFinishBoundary after r ds z' d config ∧ StreamBuffers after r ∧ StreamAccounting z z' 0 0 := by
  obtain ⟨message, refused⟩ := err_return_run boundary.good.live.hz err
  let z' := { z with msg := message }
  have goodA := stream_control_good (z' := z') boundary.good rfl boundary.good.live.zalloc boundary.good.live.zfree
  have account : StreamAccounting z z' 0 0 := stream_accounting_zero z
  have buffersA := stream_control_buffers boundary.good goodA buffers account
  have phaseA := default_phase_stream_control boundary goodA rfl
  have run := source.trans refused
  have reachableA : StreamReachable .deflate (r.put h z') r := by
    apply StreamReachable.step (call := .deflate (some r) flush) (value := err) boundary.reachable (fun k => nomatch k)
    · exact ⟨rfl, rfl⟩
    · exact ⟨buffers, default_finish_active_header boundary.good boundary.no_header⟩
    · simp only [Call.execute, heapCall, run, z']
  exact ⟨message, run, ⟨goodA, reachableA, boundary.configuration, phaseA, boundary.lower, boundary.upper⟩, buffersA, account⟩

end Zlib.Deflate.Engine.Proofs
