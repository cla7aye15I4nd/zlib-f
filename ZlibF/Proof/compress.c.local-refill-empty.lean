import ZlibF.Proof.«compress.c.local-fill»
import ZlibF.Proof.«deflate.c.engine.fill-resume-empty»

/-! # Real empty-input refill retains the local padded window -/
namespace ZlibF.Spec.Public.Proofs.CompressLocalRefillEmpty
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs
open Zlib.Deflate.Engine.Proofs ZlibF.Spec.Public
open ZlibF.Spec.Public.Proofs.CompressLocalInit
set_option autoImplicit false

/-- The actual non-sliding body exits at its empty-input check before
reading caller bytes or priming hashes. Only live records are needed. -/
theorem local_fill_body_no_input {h : Heap} {r : ZStreamRef} {ds : Nat}
    {z : ZStream} {d : DeflateState} (live : DLive h r ds z d) (input : z.avail_in = 0)
    (noSlide : ¬d.strstart ≥ d.w_size+(d.w_size-MIN_LOOKAHEAD_u)) :
    fillBody (some (.tab ds)) d.w_size false h = .ok (true,h) := by
  simp only [fillBody,bind_app,ldDeflateState_tab live.hs,noSlide,ite_false,
    rdD_eq,live.hs,live.back,zrd_eq,live.hz,input]
  rfl

/-- A real resumed refill with no new input retains the entire heap when
its valid endpoint already has the required padding. This includes old
caller typed collisions; no table, allocation or scalar is changed. -/
theorem local_fill_window_resume_no_input {h : Heap} {r : ZStreamRef} {cutoff ds : Nat}
    {z : ZStream} {d : DeflateState} (state : LocalState h cutoff r ds z d)
    (input : z.avail_in = 0) (noSlide : ¬d.strstart ≥ d.w_size+(d.w_size-MIN_LOOKAHEAD_u))
    (range : d.strstart.toNat+d.lookahead.toNat ≤ d.window_size.toNat)
    (padded : min (d.strstart.toNat+d.lookahead.toNat+258) d.window_size.toNat ≤ d.high_water.toNat) :
    fill_window (some (.tab ds)) h = .ok ((),h) ∧ LocalState h cutoff r ds z d ∧ StreamAccounting z z 0 0 := by
  have loop := do_once (local_fill_body_no_input state.live input noSlide) (fill_cond_break (some (.tab ds)) h)
  refine ⟨?_,state,stream_accounting_zero z⟩
  rw [fill_window_source]
  simp only [bind_app,rdD_eq,state.live.hs,loop]
  exact fill_high_water_retained state.live.hs state.inv range padded

end ZlibF.Spec.Public.Proofs.CompressLocalRefillEmpty
