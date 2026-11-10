import ZlibF.Proof.«inflate.c.fast-causal-loop-rejected-word-body»
namespace Zlib.Inflate.Proofs.FastCommittedLoop
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec ZlibF.Spec.Public
open Zlib.Inflate.Proofs Zlib.Inffast.Spec Zlib.Inftrees
open Zlib.Inftrees.Spec.DecodeTableStability
set_option autoImplicit false
set_option maxRecDepth 8192

theorem WordReady.step_with_rejected_word {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap} {q : Zlib.Inffast.L}
    (state : WordReady p h q)
    (dstable : StableQuery DISTS ctx.distCodes ctx.distOff ctx.distWidth)
    (ltake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake LENS ctx.codes ctx.baseOff ctx.rootWidth)
    (dtake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake DISTS ctx.distCodes ctx.distOff ctx.distWidth) :
    ∃ result after, C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      ((fastLoopCond ctx result after = .ok ((false, result), after) ∧ WordRejectedExit p after result) ∨
       (fastLoopCond ctx result after = .ok ((true, result), after) ∧
         Nonempty (WordReady p after result) ∧ fastLoopMeasure ctx result < fastLoopMeasure ctx q)) := by
  obtain ⟨result, after, actual, semantic⟩ := state.body_with_rejected_word dstable ltake dtake
  obtain ⟨safetyResult, safetyHeap, safetyRun, safety⟩ := state.state.safety.step
  have same := Except.ok.inj (actual.symm.trans safetyRun)
  cases same
  refine ⟨result, after, actual, ?_⟩
  rcases safety with stopped | continuing
  · exact Or.inl ⟨stopped.1, stopped.2, semantic⟩
  · obtain ⟨condition, ready, measure⟩ := continuing
    have notBroken := fastLoopCond_true_not_broken condition
    rcases semantic with normal | eob | bad
    · obtain ⟨tracked, source, _currentJ⟩ := normal
      exact Or.inr ⟨condition, ⟨{state := {safety := ready, tracked := tracked}, source := source}⟩, measure⟩
    · obtain ⟨ended, _source⟩ := eob
      exact False.elim (by rw [ended.broke] at notBroken; cases notBroken)
    · obtain ⟨rejected, _source⟩ := bad
      have broke := rejected.broke
      exact False.elim (by rw [broke] at notBroken; cases notBroken)

/-- The actual finite fast loop preserves committed-token grammar and
raw Origin on arbitrary input. Final outcomes are a resumable grammar cut,
a real EOB with original Symbols, or actual BAD with the last universally rejected consumed word and its accepted prefix. The proof never assumes
Symbols, a future parser, an expected output or a callee specification. -/
theorem WordReady.run_with_rejected_word {ctx : FastLoopContext} {p : Parameters ctx} {h : Heap} {q : Zlib.Inffast.L}
    (state : WordReady p h q)
    (dstable : StableQuery DISTS ctx.distCodes ctx.distOff ctx.distWidth)
    (ltake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake LENS ctx.codes ctx.baseOff ctx.rootWidth)
    (dtake : Zlib.Inftrees.Proofs.QueryTakeSource.QueryTake DISTS ctx.distCodes ctx.distOff ctx.distWidth) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c) (fastLoopCond ctx) q) h = .ok (result, after) ∧
      WordRejectedExit p after result := by
  let Inv : Zlib.Inffast.L → Heap → Prop := fun current heap => Nonempty (WordReady p heap current)
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap => WordRejectedExit p heap current
  have step : ∀ current heap, Inv current heap →
      ∃ result after, Zlib.Inffast.inflate_fast_body ctx.c current heap = .ok (result, after) ∧
        ((∃ next heap2, fastLoopCond ctx result after = .ok ((false, next), heap2) ∧ Final next heap2) ∨
         (∃ next heap2, fastLoopCond ctx result after = .ok ((true, next), heap2) ∧
           Inv next heap2 ∧ fastLoopMeasure ctx next < fastLoopMeasure ctx current)) := by
    intro current heap ⟨ready⟩
    obtain ⟨result, after, actual, outcome⟩ := ready.step_with_rejected_word dstable ltake dtake
    refine ⟨result, after, actual, ?_⟩
    rcases outcome with stopped | continuing
    · exact Or.inl ⟨result, after, stopped.1, stopped.2⟩
    · exact Or.inr ⟨result, after, continuing.1, continuing.2.1, continuing.2.2⟩
  have fuelBound : fastLoopMeasure ctx q < fuel := by
    rcases state.state.safety with ⟨slow, bs, output, off, k, packet, invariant, buffers,
      codesGet, distGet, bits, leftEq, outEq, put, next, last, margin, out, get,
      write, size, current, beginLe, span, guard⟩
    apply Zlib.Inffast.Proofs.lt_fuel_of
    simp only [fastLoopMeasure, out]
    have width := UInt32.toNat_lt ctx.leftTotal
    omega
  obtain ⟨result, after, actual, final⟩ := Zlib.Inffast.Proofs.Wp.exists_eq
    (Zlib.Inffast.Proofs.Wp.cdoWhile Inv (fastLoopMeasure ctx) Final step ⟨state⟩ fuelBound)
  exact ⟨result, after, actual, final⟩

#print axioms WordReady.step_with_rejected_word
#print axioms WordReady.run_with_rejected_word
end Zlib.Inflate.Proofs.FastCommittedLoop
