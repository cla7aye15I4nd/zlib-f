import ZlibF.Proof.«deflate.c.universal-call-poststrat»
import ZlibF.Proof.«deflate.c.universal-call-markers»

/-!
# deflate.c: evaluating the strategy phase of one call

Owner 2 of the deflate split (`deflate_call`). The strategy phase tests whether a strategy runs,
runs the dispatch, and then (`strategyAfter`) stores `FINISH_STATE` on a finishing return,
returns `Z_OK` on `need_more` and `finish_started` (with `last_flush := -1` on a full output),
runs the flush markers on `block_done`, and continues to the trailer otherwise. Each outcome is
stated with one store `{ d with status, last_flush }`, the form of `post_store`.
-/

namespace Zlib.Deflate.Universal.Call
open C Zlib.Deflate Zlib.Deflate.Spec Zlib.Deflate.Proofs ZlibF.Spec.Public
open Zlib.Deflate.Engine.Proofs
set_option autoImplicit false

/-- The strategy phase: the test, then the dispatch and what follows it. -/
theorem strategy_phase_eval {h : Heap} {r : ZStreamRef} {ds : Nat} {z : ZStream} {d : DeflateState}
    (hz : r.get h = some z) (hs : h.dstates ds = some d) (flush : Int32) (k : M Int32) :
    strategyPhase (some r) (some (.tab ds)) flush k h =
      if (z.avail_in != 0 || d.lookahead != 0 || (flush != Z_NO_FLUSH && d.status != FINISH_STATE)) = true then
        (dispatch (some (.tab ds)) flush d >>= fun b => strategyAfter (some r) (some (.tab ds)) flush b k) h
      else k h := by
  rw [strategy_phase_split]
  unfold strategyPhase'
  simp only [bind_app, ldDeflateState_tab hs, zrd_eq, hz]
  split
  · unfold dispatch
    by_cases l0 : (d.level == 0) = true
    · simp only [l0, ite_true]; rfl
    · simp only [l0, Bool.false_eq_true, ite_false]
      by_cases hf : (d.strategy == Z_HUFFMAN_ONLY) = true
      · simp only [hf, ite_true]; rfl
      · simp only [hf, Bool.false_eq_true, ite_false]
        by_cases rl : (d.strategy == Z_RLE) = true
        · simp only [rl, ite_true]; rfl
        · simp only [rl, Bool.false_eq_true, ite_false]
          simp only [bind_app]
          cases config_at d.level h with
          | error _ => rfl
          | ok p =>
            obtain ⟨c, h1⟩ := p
            dsimp only
            cases hf : c.func <;> simp only [hf, bind_app]
  · rfl

/-- `strategyAfter` on `need_more`. -/
theorem after_need_more {a : Heap} {r : ZStreamRef} {ds : Nat} {z1 : ZStream} {d1 : DeflateState}
    (hz : r.get a = some z1) (hs : a.dstates ds = some d1) (flush : Int32) (k : M Int32) :
    strategyAfter (some r) (some (.tab ds)) flush need_more k a =
      .ok (Z_OK, setD a ds { d1 with status := d1.status, last_flush := if z1.avail_out = 0 then -1 else d1.last_flush }) := by
  unfold strategyAfter
  by_cases full : z1.avail_out = 0
  · simp [bind_app, pure_app, zrd_eq, hz, wrD_eq, hs, full, need_more, finish_started, finish_done, block_done]
  · have self : setD a ds { d1 with status := d1.status, last_flush := d1.last_flush } = a := setD_self hs
    simp [bind_app, pure_app, zrd_eq, hz, full, need_more, finish_started, finish_done, block_done, self]

/-- `strategyAfter` on `finish_started`. -/
theorem after_started {a : Heap} {r : ZStreamRef} {ds : Nat} {z1 : ZStream} {d1 : DeflateState}
    (hz : r.get a = some z1) (hs : a.dstates ds = some d1) (flush : Int32) (k : M Int32) :
    strategyAfter (some r) (some (.tab ds)) flush finish_started k a =
      .ok (Z_OK, setD a ds { d1 with status := FINISH_STATE, last_flush := if z1.avail_out = 0 then -1 else d1.last_flush }) := by
  unfold strategyAfter
  by_cases full : z1.avail_out = 0
  · simp [bind_app, pure_app, zrd_eq, hz, wrD_eq, hs, full, need_more, finish_started, finish_done, block_done,
      ZStreamRef.get_setD]
  · simp [bind_app, pure_app, zrd_eq, hz, wrD_eq, hs, full, need_more, finish_started, finish_done, block_done,
      ZStreamRef.get_setD]

/-- `strategyAfter` on `block_done`: the flush markers. -/
theorem after_block {a : Heap} {r : ZStreamRef} {ds : Nat} (flush : Int32) (k : M Int32) :
    strategyAfter (some r) (some (.tab ds)) flush block_done k a = markerTail (some r) (some (.tab ds)) flush k a := by
  unfold strategyAfter
  simp [bind_app, pure_app, need_more, finish_started, finish_done, block_done]

/-- `strategyAfter` on `finish_done`: `FINISH_STATE`, then the trailer. -/
theorem after_done {a : Heap} {r : ZStreamRef} {ds : Nat} {d1 : DeflateState}
    (hs : a.dstates ds = some d1) (flush : Int32) (k : M Int32) :
    strategyAfter (some r) (some (.tab ds)) flush finish_done k a =
      k (setD a ds { d1 with status := FINISH_STATE, last_flush := d1.last_flush }) := by
  unfold strategyAfter
  simp [bind_app, pure_app, wrD_eq, hs, need_more, finish_started, finish_done, block_done]

end Zlib.Deflate.Universal.Call
