import ZlibF.Proof.«inflate.c.local-fast-loop-body»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

theorem fast_memory_readonly {r : ZStreamRef} {before after : Heap}
    (frame : FastMemoryMetaFrame r before after) :
    ∀ ref : BRef, Space.ro after ref = Space.ro before ref := by
  simp only [FastMemoryMetaFrame, fastMemoryMeta, Prod.mk.injEq] at frame
  intro ref
  cases ref <;> simp only [Space.ro, frame.1]

theorem fast_memory_live {r : ZStreamRef} {before after : Heap}
    (frame : FastMemoryMetaFrame r before after) : ∀ b, before.live b → after.live b := by
  simp only [FastMemoryMetaFrame, fastMemoryMeta, Prod.mk.injEq] at frame
  obtain ⟨_, _, _, _, _, _, live⟩ := frame
  intro b present
  rw [live]
  exact present

theorem fast_loop_true_not_broken {ctx : FastLoopContext} {q : Zlib.Inffast.L} {h : Heap}
    (condition : fastLoopCond ctx q h = .ok ((true, q), h)) : q.broke = false := by
  cases broken : q.broke
  · rfl
  · simp only [fastLoopCond, broken, Bool.true_eq, ↓reduceIte, pure_app] at condition
    cases condition

/-- The complete same-run summary of one actual fast loop. -/
def FastLoopSummary (cutoff : Nat) (ctx : FastLoopContext) (before : Heap)
    (startOff startBits : Nat) (result : Zlib.Inffast.L) (after : Heap) : Prop :=
  FastLoopExit cutoff ctx after result ∧
  FastLoopInputBudget ctx startOff startBits result ∧
  FastLoopOutputRange ctx after result ∧ FastLoopInputLimit ctx result ∧
  ByteViewSizes before after ∧
  BufferFrame before after (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
    [⟨.ref ctx.dest ctx.oo, ctx.leftTotal.toNat⟩] ∧
  FastMemoryMetaFrame ctx.r before after ∧
  (∀ zNext sNext, LocalStateJ after cutoff ctx.r ctx.zs zNext sNext →
    sNext.window = ctx.s.window ∧
    (sNext.mode = ctx.s.mode ∨ sNext.mode = TYPE ∨ sNext.mode = BAD) ∧
    (sNext.mode = BAD ∨ sNext.mode = TYPE ∨
      ∃ finish, result.out = .ref ctx.dest finish ∧ ctx.oo < finish))

/-- The actual fast loop terminates and retains its local representation,
physical input ledger, complete caller output frame and progress metadata.
Every iteration executes the translated parser and its proved effect rule. -/
theorem FastLoopReady.run_summary
    {cutoff : Nat} {ctx : FastLoopContext} {h : Heap} {q : Zlib.Inffast.L}
    {startOff startBits : Nat} (ready : FastLoopReady cutoff ctx h q)
    (account : FastLoopInputBudget ctx startOff startBits q) (notBroken : q.broke = false) :
    ∃ result after,
      C.run (cdoWhile (Zlib.Inffast.inflate_fast_body ctx.c) (fastLoopCond ctx) q) h = .ok (result, after) ∧
      FastLoopSummary cutoff ctx h startOff startBits result after := by
  obtain ⟨originalOutput, originalGet, originalWrite⟩ :
      ∃ array, Space.get h ctx.dest = some array ∧ Space.ro h ctx.dest = false := by
    rcases ready with ⟨_, _, output, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, get, write, _⟩
    exact ⟨output, get, write⟩
  let Inv : Zlib.Inffast.L → Heap → Prop := fun current heap =>
    FastLoopReady cutoff ctx heap current ∧ FastLoopInputBudget ctx startOff startBits current ∧
    ByteViewSizes h heap ∧
    BufferFrame h heap (fun b => StreamRoot ctx.r b ∨ b = ctx.zs)
      [⟨.ref ctx.dest ctx.oo, ctx.leftTotal.toNat⟩] ∧
    FastMemoryMetaFrame ctx.r h heap ∧ current.broke = false
  let Final : Zlib.Inffast.L → Heap → Prop := FastLoopSummary cutoff ctx h startOff startBits
  have step : ∀ current heap, Inv current heap →
      ∃ result after, Zlib.Inffast.inflate_fast_body ctx.c current heap = .ok (result, after) ∧
        ((∃ next heap2, fastLoopCond ctx result after = .ok ((false, next), heap2) ∧ Final next heap2) ∨
         (∃ next heap2, fastLoopCond ctx result after = .ok ((true, next), heap2) ∧
           Inv next heap2 ∧ fastLoopMeasure ctx next < fastLoopMeasure ctx current)) := by
    intro current heap currentInv
    obtain ⟨currentReady, oldBudget, oldSizes, oldFrame, oldMemory, unbroken⟩ := currentInv
    obtain ⟨result, after, observed⟩ := currentReady.observe
    obtain ⟨bodyRun, stopped | continuing⟩ := FastLoopReady.step_of_observed observed
    all_goals
      obtain ⟨budget, output, limit, sizes, frame, memoryFacts, fields⟩ := observed.metadata oldBudget unbroken
      have allMemory := oldMemory.trans memoryFacts
      have writeCurrent : Space.ro heap ctx.dest = false := (fast_memory_readonly oldMemory ctx.dest).trans originalWrite
      have writeAfter : Space.ro after ctx.dest = false := (fast_memory_readonly allMemory ctx.dest).trans originalWrite
      have allFrame := BufferFrame.singleton_trans_live oldFrame frame (fast_memory_live oldMemory)
        originalGet writeCurrent writeAfter
      have allSizes := oldSizes.trans sizes
      refine ⟨result, after, bodyRun, ?_⟩
    · exact Or.inl ⟨result, after, stopped.1, stopped.2, budget, output, limit, allSizes,
        allFrame, allMemory, fields⟩
    · exact Or.inr ⟨result, after, continuing.1,
        ⟨continuing.2.1, budget, allSizes, allFrame, allMemory,
          fast_loop_true_not_broken continuing.1⟩, continuing.2.2⟩
  have fuelBound : fastLoopMeasure ctx q < fuel := by
    rcases ready with ⟨slow, bs, output, off, k, packet, invariant, buffers, codesGet, distGet,
      bitsBound, leftEq, outEq, putPtr, nextPtr, lastPtr, inputMargin, outPtr, outputGet,
      outputWrite, outputSize, current, beginLe, span, guard⟩
    apply Zlib.Inffast.Proofs.lt_fuel_of
    simp only [fastLoopMeasure, outPtr]
    have width := UInt32.toNat_lt ctx.leftTotal
    omega
  have initial : Inv q h := ⟨ready, account, ByteViewSizes.refl h,
    BufferFrame.singleton_refl originalGet originalWrite,
    FastMemoryMetaFrame.refl ctx.r h, notBroken⟩
  obtain ⟨result, after, run, final⟩ := Zlib.Inffast.Proofs.Wp.exists_eq
    (Zlib.Inffast.Proofs.Wp.cdoWhile Inv (fastLoopMeasure ctx) Final step initial fuelBound)
  exact ⟨result, after, run, final⟩

end Zlib.Inflate.Local
