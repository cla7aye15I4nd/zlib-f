import ZlibF.Proof.«workspace-inflate.c.prime-default-state»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Default zlib/raw-recovery streams reject every gzip-header registration
before dereferencing its argument. The actual unchanged heap retains J. -/
theorem inflateGetHeader_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) (header : GzHeaderPtr) :
    C.run (inflateGetHeader (some r) header) h = .ok (Z_STREAM_ERROR, h) ∧
      DefaultStateJ h r zs z s :=
  ⟨(inflateGetHeader_default_J invariant.toDefaultDecodeJ header).1, invariant⟩

/-- In the selected build the actual undermine operation refuses the
request and retains the initialized sane decoder relation. -/
theorem inflateUndermine_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) (subvert : Int32) :
    C.run (inflateUndermine (some r) subvert) h = .ok (Z_DATA_ERROR, h) ∧
      DefaultStateJ h r zs z s :=
  ⟨(inflateUndermine_default_J invariant.toDefaultDecodeJ subvert).1, invariant⟩

end Zlib.Inflate.Proofs
