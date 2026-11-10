import ZlibF.Proof.«inflate.c.fast-view-break-refill-all-length-cases-invariant»
import ZlibF.Proof.«inflate.c.fast-view-break-no-pull-all-length-cases-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The actual first length-table selection either uses the held bits or
the two initial translated input pulls. The packet witnesses the latter. -/
def FastFirstLengthSelected
    (h : Heap) (q selected : Zlib.Inffast.L) : Prop :=
  selected = q ∨
    ∃ slow first second third fourth fifth sixth rest,
      FastInputPacket h slow
        (first :: second :: third :: fourth :: fifth :: sixth :: rest)
        q ∧
      selected = fastTwoPulls slow first second q

/-- Classification of the selected first length code. Each terminal or
invalid branch includes actual outer-loop execution and byte rollback. -/
def FastFirstLengthOutcome (ctx : FastLoopContext)
    (h : Heap) (q selected : Zlib.Inffast.L)
    (startOff : Nat) : Prop :=
  (FastRootEnd ctx.codes ctx.baseOff ctx.c selected ∧
    FastLoopRollback ctx h q startOff) ∨
  (FastRootInvalid ctx.codes ctx.baseOff ctx.c selected ∧
    FastLoopRollback ctx h q startOff) ∨
  (FastLinkedEnd h ctx.codes ctx.baseOff ctx.c selected ctx.codeRef ∧
    FastLoopRollback ctx h q startOff) ∨
  (FastLinkedInvalid h ctx.codes ctx.baseOff ctx.c selected ctx.codeRef ∧
    FastLoopRollback ctx h q startOff) ∨
  FastRootLeafContinues ctx.codes ctx.baseOff ctx.c selected ∨
  FastLinkedContinues h ctx.codes ctx.baseOff ctx.c selected
    ctx.codeRef

/-- Every actual fast-loop-ready first length lookup falls in one of the
source branches, regardless of whether it performs the initial refill. -/
theorem FastLoopReady.first_length_cases
    {ctx : FastLoopContext} {h : Heap}
    {q : Zlib.Inffast.L} {startOff startBits : Nat}
    (ready : FastLoopReady ctx h q)
    (account : FastInputAccount ctx startOff startBits q)
    (initialBits : startBits < 8) :
    ∃ selected,
      FastFirstLengthSelected h q selected ∧
      FastFirstLengthOutcome ctx h q selected startOff := by
  by_cases small : q.bits.toNat < 15
  · obtain ⟨slow, first, second, third, fourth, fifth,
      sixth, rest, packet, cases⟩ :=
      ready.two_pull_all_length_cases account initialBits small
    exact ⟨fastTwoPulls slow first second q,
      Or.inr ⟨slow, first, second, third, fourth, fifth,
        sixth, rest, packet, rfl⟩, cases⟩
  · have held : 15 ≤ q.bits.toNat := by omega
    exact ⟨q, Or.inl rfl,
      ready.no_pull_all_length_cases account initialBits held⟩

end Zlib.Inflate.Proofs
