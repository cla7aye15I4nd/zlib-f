import ZlibF.Spec.Public.History

open C ZlibF.Spec.Public

/-! The deflate history domain excluded a `deflateGetDictionary` destination inside a deflate state
record: the model views another stream's `depth` scratch array as a writable byte range
(`dstate_depth`), and the step proof first covered byte blocks only. That layout is not undefined
behaviour of the C. The exclusion is gone: the arguments ask only for a writable caller range
outside this stream (`CallerRange`), and the step proof is a frame argument for both views
(`deflate.c.universal-ops-caller-view`). This regression fails if the domain is narrowed again. -/
namespace DeflateGetDictDepthViewRegression

theorem depth_view_admitted (h : Heap) (r : ZStreamRef) (owner off : Nat) (lengthPresent : Bool) :
    StreamArguments h r (.deflateGetDictionary (some r) (.ref (.dstate_depth owner) off) lengthPresent) ↔
      ∃ z i s, r.get h = some z ∧ z.state = some (.deflate i) ∧ h.dstates i = some s ∧
        CallerRange h r (.ref (.dstate_depth owner) off)
          (min s.w_size.toNat (s.strstart.toNat + s.lookahead.toNat)) true :=
  Iff.rfl

end DeflateGetDictDepthViewRegression
