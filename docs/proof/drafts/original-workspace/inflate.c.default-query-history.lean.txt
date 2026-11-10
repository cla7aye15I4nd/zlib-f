import ZlibF.Proof.«inflate.c.default-state»
import ZlibF.Proof.«inflate.c.misc»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The translated sync-point query leaves the default decoder relation
unchanged. Its result is the current stored-block alignment test. -/
theorem inflateSyncPoint_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) :
    (Call.inflateSyncPoint (some r)).execute default h =
      .ok (((if s.mode = STORED ∧ s.bits = 0 then (1 : Int32) else (0 : Int32)), default), h) ∧
    DefaultStateJ h r zs z s := by
  have run := inflateSyncPoint_spec invariant.good.live
  refine ⟨?_, invariant⟩
  change inflateSyncPoint (some r) h = _ at run
  simp only [Call.execute, heapCall, run]
  rfl

/-- The translated mark query returns without changing any decoder field. -/
theorem inflateMark_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) :
    ∃ value, (Call.inflateMark (some r)).execute default h =
      .ok ((value, default), h) ∧ DefaultStateJ h r zs z s ∧
      value.toInt = markValue s := by
  obtain ⟨value, run, marked⟩ := inflateMark_spec invariant.good.live
  refine ⟨value, ?_, invariant, marked⟩
  change inflateMark (some r) h = _ at run
  simp only [Call.execute, heapCall, run]

/-- The translated code-count query returns without changing the decoder. -/
theorem inflateCodesUsed_default_state {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState} (invariant : DefaultStateJ h r zs z s) :
    ∃ used, used ≤ 1444 ∧
      (Call.inflateCodesUsed (some r)).execute default h =
        .ok ((UInt64.ofNat used, default), h) ∧
      DefaultStateJ h r zs z s := by
  obtain ⟨used, bound, _, run⟩ := inflateCodesUsed_spec invariant.good
  refine ⟨used, bound, ?_, invariant⟩
  change inflateCodesUsed (some r) h = _ at run
  simp only [Call.execute, heapCall, run]

end Zlib.Inflate.Proofs
