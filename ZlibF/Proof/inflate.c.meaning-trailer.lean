import ZlibF.Proof.«inflate.c.meaning-loop»
import ZlibF.Proof.«inflate.c.meaning-format»

/-!
# inflate.c: the trailer and end modes keep the format meaning in the loop

Per-mode steps of the stream side (batch 2) against `LoopMatches`
(`inflate.c.meaning-loop`). `DONE` leaves with `Z_STREAM_END` and nothing
else changed.
-/

namespace Zlib.Inflate.Proofs.MeaningTrailer
open C Zlib.Inflate Zlib.Inflate.Proofs Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- `case DONE:` sets the return register and leaves; heap and every other
register are unchanged. -/
theorem inflate_DONE_run (c : Ctx) (l : IL) (h : Heap) :
    runX (inflate_DONE c) l h = .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }), h) := rfl

/-- No position inside the deflate body is represented in `DONE`. -/
theorem body_not_done {h : Heap} {s : InflateState} {pos : DeflatePos}
    (body : BodyMatches h s pos) (done : s.mode = DONE) : False := by
  obtain ⟨out, final, blockStage⟩ := pos
  cases blockStage with
  | boundary =>
    obtain ⟨mode | mode, _⟩ := body <;> rw [done] at mode <;> exact absurd mode (by decide)
  | storedHeader =>
    obtain ⟨mode, _⟩ := body
    rw [done] at mode
    exact absurd mode (by decide)
  | stored remaining =>
    obtain ⟨mode | mode, _⟩ := body <;> rw [done] at mode <;> exact absurd mode (by decide)
  | dynamicHeader header =>
    obtain ⟨dynamic, _⟩ := body
    rcases dynamic with ⟨mode, _⟩ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨mode, _⟩ | ⟨mode, _⟩⟩ <;>
      rw [done] at mode <;> exact absurd mode (by decide)
  | codes L D pending =>
    obtain ⟨_, _, _, modes⟩ := body
    cases pending with
    | none => rcases modes with mode | mode <;> rw [done] at mode <;> exact absurd mode (by decide)
    | lengthExtra _ => obtain ⟨mode, _⟩ := modes; rw [done] at mode; exact absurd mode (by decide)
    | distance _ => obtain ⟨mode, _⟩ := modes; rw [done] at mode; exact absurd mode (by decide)
    | distanceExtra _ _ => obtain ⟨mode, _⟩ := modes; rw [done] at mode; exact absurd mode (by decide)
    | copy _ _ => obtain ⟨mode, _⟩ := modes; rw [done] at mode; exact absurd mode (by decide)
    | literal _ => obtain ⟨mode, _⟩ := modes; rw [done] at mode; exact absurd mode (by decide)
  | finished =>
    obtain ⟨mode | mode, _⟩ := body <;> rw [done] at mode <;> exact absurd mode (by decide)

/-- In the loop, only the end stage is represented in `DONE`. -/
theorem loop_stage_done {h : Heap} {s : InflateState} {f : LoopFrame} {checked : List UInt8}
    {stage : WrapStage} (stageFacts : LoopStageMatches h s f checked stage) (done : s.mode = DONE) :
    ∃ out, stage = .done out := by
  rcases stage with bytes | header | ⟨header, ⟨out, final, pos⟩⟩ | ⟨header, out, bytes⟩ | out
  · obtain ⟨_, hi⟩ := stageFacts
    rw [done] at hi
    exact absurd hi (by decide)
  · have mode : s.mode = DICT := stageFacts
    rw [done] at mode
    exact absurd mode (by decide)
  · exact (body_not_done stageFacts.1 done).elim
  · obtain ⟨mode | mode, _⟩ := stageFacts <;> rw [done] at mode <;> exact absurd mode (by decide)
  · exact ⟨out, rfl⟩

/-- `case DONE:` in the loop: it leaves with `Z_STREAM_END`, and the loop
meaning holds for the registers with the return value reset. -/
theorem done_step {c : Ctx} {f : LoopFrame} {h : Heap} {l : IL} (loop : LoopMatches c f h l) :
    runX (inflate_DONE c) l h = .ok ((.error Ex.leave, { l with ret := Z_STREAM_END }), h) ∧
      LoopMatches c f h { { l with ret := Z_STREAM_END } with ret := Z_OK } := by
  refine ⟨inflate_DONE_run c l h, ?_⟩
  obtain ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, rest⟩ := loop
  have same : ({ { l with ret := Z_STREAM_END } with ret := Z_OK } : IL) = l := by
    cases l
    simp only at retOk ⊢
    rw [retOk]
  rw [same]
  exact ⟨zs, s, callOut, consumed, held, stage, st, hs, retOk, rest⟩

#print axioms loop_stage_done
#print axioms done_step

end Zlib.Inflate.Proofs.MeaningTrailer
