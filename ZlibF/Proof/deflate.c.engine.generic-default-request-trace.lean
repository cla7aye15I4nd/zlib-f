import ZlibF.Proof.«deflate.c.engine.generic-all-scalar-protocol»
import ZlibF.Proof.«deflate.c.engine.generic-default-data-trace»
namespace Zlib.Deflate.Engine.Proofs
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual basic call histories with every signed flush and no readable-input
observation requirement. A bad-input refusal can be followed by further calls.
Constructors record only actual successful default init, legal caller edits,
public caller buffers and actual returning runs; they assume no invariant,
allocator identity, custom-header condition or called-function specification. -/
inductive GenericDefaultRequestTrace (r : ZStreamRef) : Heap → Prop
  | init {h after version} : InitDomain h r version →
      C.run (deflateInit_ (some r) Z_DEFAULT_COMPRESSION version 112) h=.ok (Z_OK,after) →
      GenericDefaultRequestTrace r after
  | caller {h after} : GenericDefaultRequestTrace r h → Rebuffer h after r →
      GenericDefaultRequestTrace r after
  | step {h after flush rc} : GenericDefaultRequestTrace r h → StreamBuffers h r →
      deflate (some r) flush h=.ok (rc,after) → GenericDefaultRequestTrace r after

/-- Every observed byte history embeds into actual basic request history.
The converse is not asserted: a NULL positive-input refusal has no byte snapshot. -/
theorem GenericDefaultDataTrace.request_trace {h : Heap} {r : ZStreamRef} {log : DataLog}
    (history : GenericDefaultDataTrace r h log) : GenericDefaultRequestTrace r h := by
  induction history with
  | init domain actual => exact .init domain actual
  | caller _ edit ih => exact .caller ih edit
  | step _ _ observed ih =>
      obtain ⟨_z,_z',_get,_get',buffers,_header,_snapshot,_used,_bytes,run⟩ := observed
      exact .step ih buffers run

end Zlib.Deflate.Engine.Proofs
