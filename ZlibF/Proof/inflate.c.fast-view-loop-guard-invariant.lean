import ZlibF.Proof.«inflate.c.fast-view-body-rank-cursor-invariant»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
open Zlib.Inffast.Spec
set_option autoImplicit false

/-- The translated fast-loop continuation test is exactly the six-input-byte
and 258-output-byte margin check on caller byte views. -/
theorem fast_loop_cond_live_view
    {h : Heap} {c : Zlib.Inffast.Ctx} {l : Zlib.Inffast.L}
    {inputRef outputRef : BRef} {input output : Array UInt8}
    {inputOff inputHave outputOff outputLeft j : Nat}
    (notBroken : l.broke = false)
    (inPtr : l.in_ = .ref inputRef inputOff)
    (lastPtr : c.last = .ref inputRef
      (inputOff + inputHave - 5))
    (inputGet : Space.get h inputRef = some input)
    (inputBound : inputOff + inputHave ≤ input.size)
    (outPtr : l.out = .ref outputRef j)
    (endPtr : c.end_ = .ref outputRef
      (outputOff + outputLeft - 257))
    (outputGet : Space.get h outputRef = some output)
    (outputBound : outputOff + outputLeft ≤ output.size)
    (within : j ≤ outputOff + outputLeft)
    (avail : 258 ≤ outputLeft) :
    C.run (do
      if l.broke then pure (false, l)
      else if ← Ptr.lt l.in_ c.last then
        pure (← Ptr.lt l.out c.end_, l)
      else pure (false, l)) h =
      .ok ((decide (6 ≤ inputHave) &&
        decide (j + 258 ≤ outputOff + outputLeft), l), h) := by
  have inputFirst : inputOff ≤ input.size := by omega
  have inputLast : inputOff + inputHave - 5 ≤ input.size := by omega
  have outputFirst : j ≤ output.size := by omega
  have outputEnd : outputOff + outputLeft - 257 ≤ output.size := by omega
  have inputCompare : C.run (Ptr.lt l.in_ c.last) h =
      .ok (decide (inputOff < inputOff + inputHave - 5), h) := by
    rw [inPtr, lastPtr]
    exact Ptr.lt_ok inputGet inputFirst inputLast
  have outputCompare : C.run (Ptr.lt l.out c.end_) h =
      .ok (decide (j < outputOff + outputLeft - 257), h) := by
    rw [outPtr, endPtr]
    exact Ptr.lt_ok outputGet outputFirst outputEnd
  have inputFlag :
      decide (inputOff < inputOff + inputHave - 5) =
        decide (6 ≤ inputHave) := by
    simp only [decide_eq_decide]
    omega
  have outputFlag :
      decide (j < outputOff + outputLeft - 257) =
        decide (j + 258 ≤ outputOff + outputLeft) := by
    simp only [decide_eq_decide]
    omega
  simp only [notBroken, Bool.false_eq_true, ite_false]
  change (Ptr.lt l.in_ c.last >>= fun inputOkay =>
    if inputOkay then
      Ptr.lt l.out c.end_ >>= fun outputOkay => pure (outputOkay, l)
    else pure (false, l)) h =
      .ok ((decide (6 ≤ inputHave) &&
        decide (j + 258 ≤ outputOff + outputLeft), l), h)
  change (Ptr.lt l.in_ c.last) h =
    .ok (decide (inputOff < inputOff + inputHave - 5), h) at inputCompare
  rw [bind_app, inputCompare]
  by_cases enoughInput : 6 ≤ inputHave
  · have inputTrue : decide (inputOff < inputOff + inputHave - 5) = true := by
      rw [inputFlag]
      simp [enoughInput]
    simp only [inputTrue, ite_true]
    change (Ptr.lt l.out c.end_) h =
      .ok (decide (j < outputOff + outputLeft - 257), h) at outputCompare
    rw [bind_app, outputCompare, outputFlag]
    simp [enoughInput]
  · have inputFalse : decide (inputOff < inputOff + inputHave - 5) = false := by
      rw [inputFlag]
      simp [enoughInput]
    simp [inputFalse, enoughInput]

/-- A source `break` skips both pointer comparisons in the loop condition. -/
theorem fast_loop_cond_broken
    {h : Heap} {c : Zlib.Inffast.Ctx} {l : Zlib.Inffast.L}
    (broke : l.broke = true) :
    C.run (do
      if l.broke then pure (false, l)
      else if ← Ptr.lt l.in_ c.last then
        pure (← Ptr.lt l.out c.end_, l)
      else pure (false, l)) h = .ok ((false, l), h) := by
  simp [C.run, broke]

/-- Resolve the represented array behind a non-null caller input range. -/
theorem caller_range_ref_view
    {h : Heap} {r : ZStreamRef} {ref : BRef} {off n : Nat}
    (range : CallerRange h r (.ref ref off) n false) :
    ∃ input, Space.get h ref = some input ∧
      off + n ≤ input.size := by
  rcases range with null | ⟨⟨xs, bytes⟩, _, _⟩
  · cases null
  rcases bytes with empty | ⟨foundRef, foundOff, input,
      pointer, get, bound, _⟩
  · cases empty.1
  cases pointer
  exact ⟨input, get, bound⟩

/-- A synchronized fast packet and caller ranges discharge the two pointer
comparisons in the actual loop condition. -/
theorem FastInputPacket.fast_loop_cond_from_buffers
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {inputRef dest : BRef}
    {inputOff oo j : Nat}
    (packet : FastInputPacket h slow bs l)
    (buffers : DispatchBuffers h r slow bs)
    (notBroken : l.broke = false)
    (nextPtr : slow.next = .ref inputRef inputOff)
    (lastPtr : c.last = .ref inputRef
      (inputOff + slow.have_.toNat - 5))
    (outPtr : l.out = .ref dest j)
    (putPtr : slow.put = .ref dest oo)
    (endPtr : c.end_ = .ref dest
      (oo + slow.left.toNat - 257))
    (within : j ≤ oo + slow.left.toNat)
    (avail : 258 ≤ slow.left.toNat) :
    C.run (do
      if l.broke then pure (false, l)
      else if ← Ptr.lt l.in_ c.last then
        pure (← Ptr.lt l.out c.end_, l)
      else pure (false, l)) h =
      .ok ((decide (6 ≤ slow.have_.toNat) &&
        decide (j + 258 ≤ oo + slow.left.toNat), l), h) := by
  obtain ⟨input, inputGet, inputBound⟩ :=
    caller_range_ref_view (by simpa only [nextPtr] using buffers.input)
  obtain ⟨output, outputGet, _, outputBound⟩ :=
    fast_packet_output_view buffers putPtr rfl
  apply fast_loop_cond_live_view notBroken
    (packet.cursor.trans nextPtr) lastPtr inputGet inputBound
    outPtr endPtr outputGet outputBound within avail

end Zlib.Inflate.Proofs
