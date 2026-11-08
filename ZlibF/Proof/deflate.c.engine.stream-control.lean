import ZlibF.Proof.«deflate.c.engine.buffered-boundary»
import ZlibF.Proof.«deflate.c.engine.read-zlib»

/-! # Stream scalar stores retain private content and caller storage -/

namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open ZlibF.Math.DeflateSymbols
set_option autoImplicit false

/-- Updating only the stream control record retains the represented engine. -/
theorem stream_control_good {h : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (state : z'.state = z.state)
    (alloc : z'.zalloc ≠ .null) (free : z'.zfree ≠ .null) : DGood (r.put h z') r ds z' d := by
  have goodA := good.setZD (z' := z') (d' := d) state alloc free rfl good.live.status good.inv (by trkeep)
  rw [setD_self (by simpa using good.live.hs)] at goodA
  exact goodA

/-- Every readable byte view and extent survives a stream-record update. -/
theorem stream_control_sizes (h : Heap) (r : ZStreamRef) (z' : ZStream) : ByteSizes h (r.put h z') := by
  refine ⟨?_, ?_⟩
  · intro ref a get
    exact ⟨a, (byte_get_stream_put h r z' ref).trans get, rfl⟩
  · intro ref
    cases ref <;> cases r <;> simp only [Space.ro, ZStreamRef.put] <;> first | rfl | split <;> rfl

/-- Stream scalar updates with actual zero input/output movement retain caller ranges. -/
theorem stream_control_buffers {h : Heap} {r : ZStreamRef} {ds : Nat} {z z' : ZStream} {d : DeflateState}
    (good : DGood h r ds z d) (goodA : DGood (r.put h z') r ds z' d)
    (buffers : StreamBuffers h r) (account : StreamAccounting z z' 0 0) : StreamBuffers (r.put h z') r := by
  exact stream_buffers_sizes good.live.hz goodA.live.hz buffers (stream_control_sizes h r z')
    (stream_owned_keys good goodA rfl rfl rfl rfl) account

/-- The same private content and EOF frontier survive stream scalar stores. -/
theorem stream_control_buffered {h : Heap} {r : ZStreamRef} {ds origin base : Nat}
    {z z' : ZStream} {d : DeflateState} {input : Nat → UInt8} {xs : List ZlibF.Math.DeflateSymbols.Symbol}
    {config : EngineConfig} (boundary : BufferedBoundary h r ds z d input origin base xs config)
    (goodA : DGood (r.put h z') r ds z' d) :
    BufferedBoundary (r.put h z') r ds z' d input origin base xs config := by
  apply buffered_control_transfer boundary goodA
  · intro b _owned
    simp only [ZStreamRef.put_bytes]
  · simp only [ZStreamRef.put_words]
  · rfl
  · rfl
  · exact boundary.empty_cursor

/-- The actual error macro obtains its proved static message and stores it. -/
theorem err_return_run {h : Heap} {r : ZStreamRef} {z : ZStream}
    (live : r.get h = some z) (err : Int32) :
    ∃ message, ERR_RETURN (some r) err h = .ok (err, r.put h { z with msg := message }) := by
  obtain ⟨message, after, run, frame⟩ := Zlib.Zutil.Proofs.zError_safe h err
  change after = h at frame
  subst after
  change Zlib.Zutil.zError err h = .ok (message, h) at run
  refine ⟨message, ?_⟩
  unfold ERR_RETURN ERR_MSG
  simp only [bind_app, run, zwr_eq, live, pure_app]

end Zlib.Deflate.Engine.Proofs
