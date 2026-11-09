import ZlibF.Proof.«deflate.c.engine.generic-all-scalar-protocol»
import ZlibF.Proof.«deflate.c.engine.encoded-state»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false
/-- Attach the derived all-scalar protocol to any proved actual run at the exact
same heap and returned records, without an output-representation restriction. -/
theorem generic_all_scalar_protocol_of_run {h after : Heap} {r : ZStreamRef} {ds : Nat}
    {z z' : ZStream} {d result : DeflateState} {config : EngineConfig} {flush rc : Int32}
    (boundary : DefaultFinishBoundary h r ds z d config) (buffers : StreamBuffers h r)
    (run : deflate (some r) flush h = .ok (rc, after)) (goodA : DGood after r ds z' result) :
    DefaultFinishBoundary after r ds z' result config := by
  obtain ⟨_used, _produced, _rc, other, otherZ, otherD, otherRun, stateA, _buffersA, _account, _allowed⟩ :=
    boundary.generic_all_scalar_request buffers flush
  have heaps : other = after := (Prod.mk.inj (Except.ok.inj (otherRun.symm.trans run))).2
  subst other
  have sameZ : otherZ = z' := Option.some.inj (stateA.good.live.hz.symm.trans goodA.live.hz)
  have sameD : otherD = result := Option.some.inj (stateA.good.live.hs.symm.trans goodA.live.hs)
  subst otherZ otherD
  exact stateA


end Zlib.Deflate.Engine.Proofs
