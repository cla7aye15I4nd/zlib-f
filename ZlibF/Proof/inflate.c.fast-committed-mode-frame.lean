import ZlibF.Proof.«inflate.c.fast-committed-scalar-frame»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- Actual fast token bodies may only change the decoder mode. -/
def FastModeFrame (before after : InflateState) : Prop :=
  after = {before with mode := after.mode}

theorem FastOutputEffect.mode_frame
    {before after : Heap} {r : ZStreamRef} {zs : Nat}
    {z zNext : ZStream} {s sNext : InflateState}
    {slow : IL} {dest : BRef}
    (effect : FastOutputEffect before after r zs z s slow dest)
    (source : DefaultStateJ before r zs z s)
    (final : DefaultStateJ after r zs zNext sNext) :
    FastModeFrame s sNext := by
  rcases effect with ⟨array, heapEq, _⟩ | ⟨i, heapEq⟩ | heapEq
  · subst after
    obtain ⟨streamEq, stateEq⟩ := source.same_records_of_byte_put final
    subst zNext; subst sNext
    simp [FastModeFrame]
  · have stateEq : sNext = {s with mode := BAD} := by
      have get := final.good.live.hs
      simp only [heapEq, badHeap, setI_istates_same] at get
      exact Option.some.inj get.symm
    have streamEq : zNext = {z with msg := .ref (.str i) 0} := by
      have get := final.good.live.hz
      rw [heapEq, badHeap, ZStreamRef.get_setI,
        ZStreamRef.get_put_same source.good.live.hz] at get
      exact Option.some.inj get.symm
    subst zNext; subst sNext
    simp [FastModeFrame]
  · have stateEq : sNext = {s with mode := TYPE} := by
      have get := final.good.live.hs
      simp only [heapEq, setI_istates_same] at get
      exact Option.some.inj get.symm
    have streamEq : zNext = z := by
      have get := final.good.live.hz
      rw [heapEq, ZStreamRef.get_setI] at get
      exact Option.some.inj (get.symm.trans source.good.live.hz)
    subst zNext; subst sNext
    simp [FastModeFrame]

theorem FastLoopReady.body_mode_frame
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after,
      C.run (Zlib.Inffast.inflate_fast_body ctx.c q) h = .ok (result, after) ∧
      ∀ zNext sNext, DefaultStateJ after ctx.r ctx.zs zNext sNext →
        FastModeFrame ctx.s sNext := by
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
      (ctx.oo + slow.left.toNat - 257) := by
    rw [leftEq]; exact ctx.endPtr
  obtain ⟨slowFinal, result, after, run, effect, _⟩ :=
    packet.fast_body_output_effect invariant buffers
      ctx.streamPtr ctx.statePtr ctx.mode ctx.whaveEq ctx.wsizeEq
      ctx.wnextEq ctx.windowEq ctx.lcodePtr codesGet ctx.lenSafe
      ctx.lenMask ctx.dcodePtr distGet ctx.distSafe ctx.distMask
      bitsBound left avail outPtr putPtr ctx.begPtr endPtr outputGet
      outputWrite outputSize current beginLe span guard
  refine ⟨result, after, run, ?_⟩
  intro zNext sNext currentJ
  exact effect.mode_frame invariant currentJ

/-- The real finite decoder loop retains the decoder representation and
allocator/checksum selectors on normal, TYPE and BAD exits. -/
theorem FastLoopReady.run_mode_frame
    {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
        (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopExit ctx after result ∧
      ∀ zNext sNext, DefaultStateJ after ctx.r ctx.zs zNext sNext →
        FastModeFrame ctx.s sNext := by
  let Final : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopExit ctx heap current ∧
      ∀ zNext sNext, DefaultStateJ heap ctx.r ctx.zs zNext sNext →
        FastModeFrame ctx.s sNext
  have step : ∀ current heap, FastLoopReady ctx heap current →
      ∃ result after, Zlib.Inffast.inflate_fast_body ctx.c current heap = .ok (result, after) ∧
        ((∃ next heap2, fastLoopCond ctx result after = .ok ((false, next), heap2) ∧
          Final next heap2) ∨
         (∃ next heap2, fastLoopCond ctx result after = .ok ((true, next), heap2) ∧
          FastLoopReady ctx heap2 next ∧
          fastLoopMeasure ctx next < fastLoopMeasure ctx current)) := by
    intro current heap readyNow
    obtain ⟨result, after, bodyRun, outcome⟩ := readyNow.step
    obtain ⟨sourceResult, sourceAfter, sourceRun, fields⟩ := readyNow.body_mode_frame
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

theorem FastLoopReady.mode_frame_of_run
    {ctx : FastLoopContext} {h after : Heap}
    {q result : Zlib.Inffast.L}
    (ready : FastLoopReady ctx h q)
    (run : C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c)
      (fastLoopCond ctx) q) h = .ok (result, after)) :
    ∀ zNext sNext, DefaultStateJ after ctx.r ctx.zs zNext sNext →
      FastModeFrame ctx.s sNext := by
  obtain ⟨found, foundAfter, foundRun, _, fields⟩ := ready.run_mode_frame
  have same : (result, after) = (found, foundAfter) :=
    Except.ok.inj (run.symm.trans foundRun)
  have equal : after = foundAfter := congrArg Prod.snd same
  rw [equal]
  exact fields


#print axioms FastOutputEffect.mode_frame
#print axioms FastLoopReady.body_mode_frame
#print axioms FastLoopReady.run_mode_frame
#print axioms FastLoopReady.mode_frame_of_run
end Zlib.Inflate.Proofs
