import ZlibF.Proof.«inflate.c.slow-distance»
import ZlibF.Proof.«inflate.c.byte-views»
import ZlibF.Math.InflateMatchCopy

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec
set_option autoImplicit false

/-- Actual do-while byte body in MATCH. -/
def matchCopyByte : X Unit := do
  let l ← get
  let b ← load8 l.from_
  store8 l.put b
  let p ← l.put.add 1
  let f ← l.from_.add 1
  set { l with put := p, from_ := f }

/-- The actual predecremented repeat condition after each copied byte. -/
def matchCopyCond : X Bool := do
  let l ← get
  let n := l.copy - 1
  set { l with copy := n }
  return n != 0

def matchCopyLoop : X Unit := xdoWhile matchCopyByte matchCopyCond

/-- One actual byte copy, for overlapping output or a distinct saved source.
The source pointer is advanced on the heap after the destination write. -/
theorem matchCopyByte_run {h : Heap} {l : IL} {dest source : BRef}
    {output saved : Array UInt8} {outOffset sourceOffset : Nat}
    (put : l.put = .ref dest outOffset) (fromPtr : l.from_ = .ref source sourceOffset)
    (outGet : Space.get h dest = some output) (write : Space.ro h dest = false)
    (sourceGet : Space.get h source = some (if source = dest then output else saved))
    (outBound : outOffset < output.size)
    (sourceBound : sourceOffset < (if source = dest then output else saved).size) :
    let value := (if source = dest then output else saved).getD sourceOffset 0
    let array := output.set! outOffset value
    runX matchCopyByte l h = .ok ((.ok (),
      { l with put := .ref dest (outOffset + 1), from_ := .ref source (sourceOffset + 1) }), Space.put h dest array) := by
  dsimp only
  let input := if source = dest then output else saved
  let value := input.getD sourceOffset 0
  let array := output.set! outOffset value
  let after := Space.put h dest array
  have cell : input[sourceOffset] = value := by
    unfold value
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem sourceBound, Option.getD_some]
  have read : load8 l.from_ h = .ok (value, h) := by
    rw [fromPtr]
    exact (Ptr.load_ok sourceGet sourceBound).trans (by rw [cell])
  have store : store8 l.put value h = .ok ((), after) := by
    rw [put]
    exact Ptr.store_ok outGet write outBound
  have destGet : Space.get after dest = some array := byte_view_get_put outGet write array
  have srcGet : Space.get after source = some (if source = dest then array else saved) := by
    by_cases same : source = dest
    · subst source
      simpa only [ite_true] using destGet
    · rw [if_neg same]
      rw [byte_view_get_put_ne h same array]
      simpa only [if_neg same] using sourceGet
  have nextOut : l.put.add 1 after = .ok (.ref dest (outOffset + 1), after) := by
    rw [put]
    exact Ptr.add_nat_ok destGet (by simp [array]; omega)
  have nextSource : l.from_.add 1 after = .ok (.ref source (sourceOffset + 1), after) := by
    rw [fromPtr]
    apply Ptr.add_nat_ok srcGet
    by_cases same : source = dest
    · simpa only [same, ite_true, array, Array.size_set!] using Nat.succ_le_of_lt sourceBound
    · simpa only [same, ite_false] using Nat.succ_le_of_lt sourceBound
  unfold matchCopyByte
  simp only [runX_bind, runX_get, runX_lift_ok read, runX_lift_ok store,
    runX_lift_ok nextOut, runX_lift_ok nextSource, runX_set]
  rfl

/-- Actual condition decrement and the precise unsigned remaining count. -/
theorem matchCopyCond_run (h : Heap) (l : IL) :
    runX matchCopyCond l h = .ok ((.ok (l.copy - 1 != 0), { l with copy := l.copy - 1 }), h) := by
  unfold matchCopyCond
  simp only [runX_bind, runX_get, runX_set, runX_pure]

/-- The remaining copy loop is finite. This statement covers every writable
byte view and both aliasing choices of the source. It gives the exact final
array, pointers and decremented count. -/
theorem matchCopyWhile_run {h : Heap} {l : IL} {dest source : BRef}
    {output saved : Array UInt8} {outOffset sourceOffset n : Nat}
    (put : l.put = .ref dest outOffset) (fromPtr : l.from_ = .ref source sourceOffset)
    (outGet : Space.get h dest = some output) (write : Space.ro h dest = false)
    (sourceGet : Space.get h source = some (if source = dest then output else saved))
    (outBound : outOffset + n ≤ output.size)
    (sourceBound : sourceOffset + n ≤ (if source = dest then output else saved).size)
    (count : l.copy.toNat = n + 1) :
    runX (xwhile matchCopyCond matchCopyByte) l h =
      .ok ((.ok (), { l with put := .ref dest (outOffset + n), from_ := .ref source (sourceOffset + n), copy := 0 }),
        Space.put h dest (ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved n sourceOffset outOffset output)) := by
  let result := ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved n sourceOffset outOffset output
  let finalRegs := { l with put := .ref dest (outOffset + n), from_ := .ref source (sourceOffset + n), copy := 0 }
  let P : Nat → IL → Heap → Prop := fun k current heap =>
    k ≤ n ∧ ∃ array f o,
      heap = Space.put h dest array ∧ array.size = output.size ∧
      current = { l with put := .ref dest o, from_ := .ref source f, copy := UInt32.ofNat (k + 1) } ∧
      f + k = sourceOffset + n ∧ o + k = outOffset + n ∧
      f + k ≤ (if source = dest then array else saved).size ∧ o + k ≤ array.size ∧
      ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved k f o array = result
  let Q : Except Ex Unit → IL → Heap → Prop := fun outcome current heap =>
    outcome = .ok () ∧ current = finalRegs ∧ heap = Space.put h dest result
  have nSmall : n + 1 < 2 ^ 32 := by rw [← count]; exact UInt32.toNat_lt _
  have decrement : ∀ k, UInt32.ofNat (k + 1) - 1 = UInt32.ofNat k := by
    intro k
    change UInt32.ofNat (k + 1) - UInt32.ofNat 1 = _
    rw [← UInt32.ofNat_sub (a := k + 1) (b := 1) (by omega)]
    simp only [Nat.add_sub_cancel]
  have sourceAfter : ∀ array, Space.get (Space.put h dest array) source = some (if source = dest then array else saved) := by
    intro array
    by_cases same : source = dest
    · subst source
      simpa only [ite_true] using byte_view_get_put outGet write array
    · rw [if_neg same, byte_view_get_put_ne h same array]
      simpa only [if_neg same] using sourceGet
  have step : ∀ k current heap, P (k + 1) current heap →
      ∃ testRegs testHeap, runX matchCopyCond current heap = .ok ((.ok true, testRegs), testHeap) ∧
        ∃ outcome next heap', runX (do matchCopyByte; pure false : X Bool) testRegs testHeap = .ok ((outcome, next), heap') ∧
          (match outcome with
          | .ok true => Q (.ok ()) next heap'
          | .ok false => P k next heap'
          | .error e => Q (.error e) next heap') := by
    rintro k current heap ⟨bound, array, f, o, heapEq, size, shape, fromEnd, outEnd, fromFit, outFit, arrayEq⟩
    subst heap
    let prepared := { current with copy := UInt32.ofNat (k + 1) }
    have positive : (UInt32.ofNat (k + 1) != 0) = true := by
      have natEq : (UInt32.ofNat (k + 1)).toNat = k + 1 := by rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
      simp only [bne_iff_ne]
      intro zero
      rw [zero] at natEq
      change 0 = k + 1 at natEq
      omega
    have cond : runX matchCopyCond current (Space.put h dest array) =
        .ok ((.ok true, prepared), Space.put h dest array) := by
      rw [matchCopyCond_run]
      simp only [shape, decrement, positive, prepared]
    let value := (if source = dest then array else saved).getD f 0
    let nextArray := array.set! o value
    let next := { prepared with put := .ref dest (o + 1), from_ := .ref source (f + 1) }
    have get : Space.get (Space.put h dest array) dest = some array := byte_view_get_put outGet write array
    have ro : Space.ro (Space.put h dest array) dest = false := by rw [byte_view_ro_put]; exact write
    have body := matchCopyByte_run (h := Space.put h dest array) (l := prepared)
      (outOffset := o) (sourceOffset := f) (output := array) (saved := saved)
      (by dsimp only [prepared]; rw [shape]) (by dsimp only [prepared]; rw [shape]) get ro (sourceAfter array) (by omega) (by omega)
    refine ⟨prepared, Space.put h dest array, cond, .ok false, next,
      Space.put h dest nextArray, ?_, by omega, nextArray, f + 1, o + 1, rfl, by simpa [nextArray] using size, ?_, by omega, by omega, ?_, ?_, ?_⟩
    · rw [runX_bind, body]
      simp only [runX_pure, byte_view_put_put outGet write]
      rfl
    · dsimp only [next, prepared]
      rw [shape]
    · by_cases same : source = dest
      · simp only [same, ite_true, nextArray, Array.size_set!] at fromFit ⊢
        omega
      · have bound : f + (k + 1) ≤ saved.size := by simpa [same] using fromFit
        simp only [same, ite_false]
        omega
    · simpa only [nextArray, Array.size_set!, Nat.add_assoc, Nat.add_comm 1 k] using outFit
    · change ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved k (f + 1) (o + 1)
        (array.set! o ((if source = dest then array else saved).getD f 0)) = result
      simpa only [ZlibF.Math.InflateMatchCopy.copy, decide_eq_true_eq] using arrayEq
  have stop : ∀ current heap, P 0 current heap → ∃ testRegs testHeap,
      runX matchCopyCond current heap = .ok ((.ok false, testRegs), testHeap) ∧ Q (.ok ()) testRegs testHeap := by
    rintro current heap ⟨_, array, f, o, heapEq, _, shape, fromEnd, outEnd, _, _, arrayEq⟩
    simp only [Nat.add_zero] at fromEnd outEnd
    have eqArray : array = result := arrayEq
    subst array
    refine ⟨finalRegs, Space.put h dest result, ?_, rfl, rfl, rfl⟩
    rw [heapEq, matchCopyCond_run]
    simp only [shape, decrement, show UInt32.ofNat 0 = 0 from rfl, bne_self_eq_false, fromEnd, outEnd, finalRegs]
  have copyEq : l.copy = UInt32.ofNat (n + 1) := by rw [← count]; simp
  have initial : P n l h := by
    refine ⟨by omega, output, sourceOffset, outOffset, ?_, rfl, ?_, rfl, rfl, sourceBound, outBound, rfl⟩
    · exact (byte_view_put_self outGet write).symm
    · rw [← put, ← fromPtr, ← copyEq]
  obtain ⟨outcome, regs, after, run, resultEq, regsEq, heapEq⟩ :=
    xwhileBrk_run P Q step stop initial (by unfold fuel; omega)
  subst outcome regs after
  exact run

/-- The full actual MATCH do-while copies exactly n positive bytes and
terminates with copy zero. Aliasing output reads observe earlier writes.
No separate-block restriction is imposed on caller byte views. -/
theorem matchCopyLoop_run {h : Heap} {l : IL} {dest source : BRef}
    {output saved : Array UInt8} {outOffset sourceOffset n : Nat}
    (put : l.put = .ref dest outOffset) (fromPtr : l.from_ = .ref source sourceOffset)
    (outGet : Space.get h dest = some output) (write : Space.ro h dest = false)
    (sourceGet : Space.get h source = some (if source = dest then output else saved))
    (outBound : outOffset + n ≤ output.size)
    (sourceBound : sourceOffset + n ≤ (if source = dest then output else saved).size)
    (count : l.copy.toNat = n) (positive : 0 < n) :
    runX matchCopyLoop l h =
      .ok ((.ok (), { l with put := .ref dest (outOffset + n), from_ := .ref source (sourceOffset + n), copy := 0 }),
        Space.put h dest (ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved n sourceOffset outOffset output)) := by
  let value := (if source = dest then output else saved).getD sourceOffset 0
  let array := output.set! outOffset value
  let after := Space.put h dest array
  let regs := { l with put := .ref dest (outOffset + 1), from_ := .ref source (sourceOffset + 1) }
  have first := matchCopyByte_run put fromPtr outGet write sourceGet (by omega) (by omega)
  have arrayGet : Space.get after dest = some array := byte_view_get_put outGet write array
  have arrayWrite : Space.ro after dest = false := by rw [byte_view_ro_put]; exact write
  have getSource : Space.get after source = some (if source = dest then array else saved) := by
    by_cases same : source = dest
    · subst source
      simpa only [ite_true] using arrayGet
    · rw [if_neg same, byte_view_get_put_ne h same array]
      simpa only [if_neg same] using sourceGet
  have sourceFit : sourceOffset + 1 + (n - 1) ≤ (if source = dest then array else saved).size := by
    by_cases same : source = dest
    · simp only [same, ite_true, array, Array.size_set!] at sourceBound ⊢
      omega
    · simp only [same, ite_false] at sourceBound ⊢
      omega
  have rest := matchCopyWhile_run (h := after) (l := regs) (n := n - 1)
    (dest := dest) (source := source) (output := array) (saved := saved)
    rfl rfl arrayGet arrayWrite getSource (by simp only [array, Array.size_set!]; omega) sourceFit
    (by change l.copy.toNat = n - 1 + 1; omega)
  have nEq : n = (n - 1) + 1 := by omega
  have arrayEq : ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved (n - 1)
      (sourceOffset + 1) (outOffset + 1) array =
      ZlibF.Math.InflateMatchCopy.copy (decide (source = dest)) saved n sourceOffset outOffset output := by
    conv => rhs; rw [nEq]
    simp only [ZlibF.Math.InflateMatchCopy.copy, decide_eq_true_eq, array, value]
  unfold matchCopyLoop xdoWhile
  rw [runX_bind, first]
  simp only []
  rw [rest]
  simp only [after, byte_view_put_put outGet write, arrayEq]
  have outEnd : outOffset + 1 + (n - 1) = outOffset + n := by omega
  have fromEnd : sourceOffset + 1 + (n - 1) = sourceOffset + n := by omega
  simp only [regs, outEnd, fromEnd]

/-- Complete MATCH source with only its literal copy loop factored out. -/
def matchCase (c : Ctx) : X Unit := do
  let l ← get
  -- if (left == 0) goto inf_leave;
  if l.left == 0 then throw Ex.leave
  -- copy = out - left;
  let mut copy := l.out_ - l.left
  let mut from_ : BPtr := l.from_
  let s ← ldInflateState c.st
  -- if (state->offset > copy) { /* copy from window */
  if s.offset > copy then
    -- copy = state->offset - copy;
    copy := s.offset - copy
    -- if (copy > state->whave) { if (state->sane) { ...BAD; break; } }
    if copy > s.whave then
      if s.sane != 0 then
        badMode c "invalid distance too far back"
        return
    -- if (copy > state->wnext) { copy -= state->wnext; from = state->window + (state->wsize - copy); }
    if copy > s.wnext then
      copy := copy - s.wnext
      from_ ← s.window.add ((s.wsize - copy).toNat : Int)
    else
      -- else from = state->window + (state->wnext - copy);
      from_ ← s.window.add ((s.wnext - copy).toNat : Int)
    -- if (copy > state->length) copy = state->length;
    if copy > s.length then copy := s.length
  else
    -- from = put - state->offset; copy = state->length;
    from_ ← l.put.add (-(s.offset.toNat : Int))
    copy := s.length
  -- if (copy > left) copy = left;
  if copy > l.left then copy := l.left
  -- left -= copy; state->length -= copy;
  set { l with left := l.left - copy, copy := copy, from_ := from_ }
  wrS c.st fun s => { s with length := s.length - copy }
  -- do { *put++ = *from++; } while (--copy);
  matchCopyLoop
  -- if (state->length == 0) state->mode = LEN;
  if (← rdS c.st (·.length)) == 0 then setMode c.st LEN

theorem inflate_MATCH_copy_cut (c : Ctx) : inflate_MATCH c = matchCase c := rfl

end Zlib.Inflate.Proofs
