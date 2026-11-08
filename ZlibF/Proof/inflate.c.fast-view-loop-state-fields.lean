import ZlibF.Proof.«inflate.c.fast-view-output-effect»
import ZlibF.Proof.«inflate.c.fast-view-loop-ready-invariant»
import ZlibF.Proof.«inflate.c.fast-view-body-output-effect»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- The three source-level fast-body effects preserve the decoder window.
The only mode transitions are end-of-block TYPE and diagnostic BAD. -/
theorem FastOutputEffect.window_mode
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z zNext : ZStream} {s sNext : InflateState}
    {slow : IL} {dest : BRef}
    (effect : FastOutputEffect before after r zs z s slow dest)
    (sourceState : before.istates zs = some s)
    (result : DefaultStateJ after r zs zNext sNext) :
    sNext.window = s.window ∧
      (sNext.mode = s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) := by
  rcases effect with ⟨array, heapEq, _⟩ | ⟨i, heapEq⟩ | heapEq
  · have stateEq : sNext = s := by
      have get := result.good.live.hs
      rw [heapEq, byte_view_put_istates] at get
      exact Option.some.inj (get.symm.trans sourceState)
    subst sNext
    exact ⟨rfl, Or.inl rfl⟩
  · have stateEq : sNext = { s with mode := BAD } := by
      have get := result.good.live.hs
      simp only [heapEq, badHeap, setI_istates_same] at get
      exact Option.some.inj get.symm
    subst sNext
    exact ⟨rfl, Or.inr (Or.inr rfl)⟩
  · have stateEq : sNext = { s with mode := TYPE } := by
      have get := result.good.live.hs
      simp only [heapEq, setI_istates_same] at get
      exact Option.some.inj get.symm
    subst sNext
    exact ⟨rfl, Or.inr (Or.inl rfl)⟩

/-- One actual body has a source-derived window and mode result on every exit. -/
theorem FastLoopReady.body_window_mode
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      ∀ zNext sNext, DefaultStateJ after ctx.r ctx.zs zNext sNext →
        sNext.window = ctx.s.window ∧
        (sNext.mode = ctx.s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) := by
  rcases ready with ⟨slow, bs, output, off, k, packet,
    invariant, buffers, codesGet, distGet, bitsBound,
    leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
    outPtr, outputGet, outputWrite, outputSize, current,
    beginLe, span, guard⟩
  obtain ⟨first, second, third, fourth, fifth, sixth, rest, rfl⟩ :=
    packet.six_unread inputMargin
  have left : slow.left ≠ 0 := by rw [leftEq]; exact ctx.leftNonzero
  have avail : 258 ≤ slow.left.toNat := by rw [leftEq]; exact ctx.avail
  have endPtr : ctx.c.end_ = .ref ctx.dest
      (ctx.oo + slow.left.toNat - 257) := by rw [leftEq]; exact ctx.endPtr
  obtain ⟨slowFinal, result, after, run, effect, _⟩ :=
    packet.fast_body_output_effect invariant buffers
      ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe
      ctx.lenMask ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  refine ⟨result, after, run, ?_⟩
  intro zNext sNext resultJ
  exact effect.window_mode invariant.good.live.hs resultJ

#print axioms FastLoopReady.body_window_mode

/-- The complete actual loop preserves its entry window and changes mode
only at the translated TYPE or BAD exits. -/
theorem FastLoopReady.run_window_mode
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      ∀ zNext sNext, DefaultStateJ after ctx.r ctx.zs zNext sNext →
        sNext.window = ctx.s.window ∧
        (sNext.mode = ctx.s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) := by
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopExit ctx heap current ∧
      ∀ zNext sNext, DefaultStateJ heap ctx.r ctx.zs zNext sNext →
        sNext.window = ctx.s.window ∧
        (sNext.mode = ctx.s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD)
  have step : ∀ current heap, FastLoopReady ctx heap current →
      ∃ result after, Zlib.Inffast.inflate_fast_body ctx.c current heap = .ok (result, after) ∧
        ((∃ next heap2, fastLoopCond ctx result after = .ok ((false, next), heap2) ∧
          Final next heap2) ∨
         (∃ next heap2, fastLoopCond ctx result after = .ok ((true, next), heap2) ∧
          FastLoopReady ctx heap2 next ∧
          fastLoopMeasure ctx next < fastLoopMeasure ctx current)) := by
    intro current heap readyNow
    obtain ⟨result, after, bodyRun, outcome⟩ := readyNow.step
    obtain ⟨sourceResult, sourceAfter, sourceRun, fields⟩ := readyNow.body_window_mode
    have same : (result, after) = (sourceResult, sourceAfter) :=
      Except.ok.inj (bodyRun.symm.trans sourceRun)
    cases same
    refine ⟨result, after, bodyRun, ?_⟩
    rcases outcome with stopped | continuing
    · exact Or.inl ⟨result, after, stopped.1, stopped.2, fields⟩
    · exact Or.inr ⟨result, after, continuing.1,
        continuing.2.1, continuing.2.2⟩
  have fuelBound : fastLoopMeasure ctx q < fuel := by
    rcases ready with ⟨slow, bs, output, off, k, packet,
      invariant, buffers, codesGet, distGet, bitsBound,
      leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin,
      outPtr, outputGet, outputWrite, outputSize, current,
      beginLe, span, guard⟩
    apply Zlib.Inffast.Proofs.lt_fuel_of
    simp only [fastLoopMeasure, outPtr]
    have width := UInt32.toNat_lt ctx.leftTotal
    omega
  obtain ⟨result, after, run, final⟩ :=
    Zlib.Inffast.Proofs.Wp.exists_eq
      (Zlib.Inffast.Proofs.Wp.cdoWhile
        (fun current heap => FastLoopReady ctx heap current)
        (fastLoopMeasure ctx) Final
        step ready fuelBound)
  exact ⟨result, after, run, final.1, final.2⟩

/-- The mode and window result is tied to a given successful actual loop run. -/
theorem FastLoopReady.window_mode_of_run
    {ctx : FastLoopContext} {h after : Heap}
    {q result : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q)
    (run : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, after)) :
    ∀ zNext sNext, DefaultStateJ after ctx.r ctx.zs zNext sNext →
      sNext.window = ctx.s.window ∧
      (sNext.mode = ctx.s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) := by
  obtain ⟨found, foundAfter, foundRun, _, fields⟩ := ready.run_window_mode
  have same : (result, after) = (found, foundAfter) :=
    Except.ok.inj (run.symm.trans foundRun)
  have equal : after = foundAfter := congrArg Prod.snd same
  rw [equal]
  exact fields

#print axioms FastLoopReady.run_window_mode
#print axioms FastLoopReady.window_mode_of_run
#print axioms FastOutputEffect.window_mode
end Zlib.Inflate.Proofs
