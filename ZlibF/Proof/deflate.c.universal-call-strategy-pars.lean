import ZlibF.Proof.«deflate.c.universal-call-dispatch»
import ZlibF.Proof.«deflate.c.universal-params-deflate»

/-!
# deflate.c: what the strategy dispatch keeps of the state record

Batch C (owner 2's M5 and M17). Every strategy keeps the parameter fields of every state record
exactly (`ExactM`, batch C's parameter frame), among them `status`, `last_flush` and `wrap`: the
strategies never write them. So after the dispatch the record has the status, `last_flush` and
`wrap` it had before.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Universal.Params
set_option autoImplicit false

/-- The dispatch keeps every parameter of every record exactly. -/
theorem exact_dispatch (s : DeflateStatePtr) (flush : Int32) (d : DeflateState) : ExactM (dispatch s flush d) := by
  unfold dispatch
  refine ExactM.ite _ (exact_deflate_stored _ _) (ExactM.ite _ (exact_deflate_huff _ _)
    (ExactM.ite _ (exact_deflate_rle _ _) (ExactM.bind (exact_config_at _) (fun c => ?_))))
  split
  · exact exact_deflate_stored _ _
  · exact exact_deflate_fast _ _
  · exact exact_deflate_slow _ _

/-- **The dispatch keeps `status`, `last_flush` and `wrap`** (M5, M17) of the stream's record, and
the other parameters: `level`, `gzhead`. -/
theorem dispatch_keeps {h after : Heap} {ds : Nat} {d d0 d' : DeflateState} {flush : Int32} {b : block_state}
    (run : dispatch (some (.tab ds)) flush d h = .ok (b, after)) (get : h.dstates ds = some d0)
    (get' : after.dstates ds = some d') :
    d'.status = d0.status ∧ d'.last_flush = d0.last_flush ∧ d'.wrap = d0.wrap ∧ d'.level = d0.level ∧
      d'.gzhead = d0.gzhead := by
  obtain ⟨d1, get1, eq⟩ := (exact_dispatch _ _ _ h b after run).1 ds d0 get
  have same : d1 = d' := Option.some.inj (get1.symm.trans get')
  subst same
  simp only [Pars, Prod.mk.injEq] at eq
  obtain ⟨l, _, _, g, _, w, st, lf⟩ := eq
  exact ⟨st, lf, w, l, g⟩

end Zlib.Deflate.Universal.Call
