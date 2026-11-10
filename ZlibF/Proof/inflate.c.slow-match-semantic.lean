import ZlibF.Proof.«inflate.c.match-source»
import ZlibF.Math.LZ77Copy
import ZlibF.Math.LZ77History

namespace Zlib.Inflate.Proofs.SlowMatchSemanticPath
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec
open Zlib.Inflate.Proofs Zlib.Inffast.Proofs
open ZlibF.Math.InflateMatchCopy ZlibF.Math.LZ77Copy
set_option autoImplicit false

/-- The actual slow overlapping byte loop has the standard array copier. -/
theorem copy_output_eq (saved : Array UInt8) :
    ∀ n source dest output, copy true saved n source dest output = cpyN n source dest output
  | 0, _, _, _ => rfl
  | n + 1, source, dest, output => by
    rw [copy_succ, cpyN]
    exact copy_output_eq saved n (source + 1) (dest + 1) _

/-- The actual slow saved-source byte loop has the fixed array copier. -/
theorem copy_saved_eq (saved : Array UInt8) :
    ∀ n source dest output, copy false saved n source dest output = blitN saved n source dest output
  | 0, _, _, _ => rfl
  | n + 1, source, dest, output => by
    rw [copy_succ, blitN]
    exact copy_saved_eq saved n (source + 1) (dest + 1) _

/-- An actual MATCH emit segment with an overlapping current-output
source appends exactly the independent copyBack bytes. -/
theorem matchEmit_output_semantics
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {dest : BRef} {output : Array UInt8} {off count dist : Nat} {amount : UInt32}
    (E : Env c h r zs z s) (put : l.put = .ref dest off)
    (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (positive : 0 < amount.toNat) (countFit : count ≤ off) (distance : 0 < dist)
    (inOutput : dist ≤ count) (room : off + amount.toNat ≤ output.size)
    (dict : List UInt8) :
    ∃ regs after array,
      runX (matchEmit c amount (.ref dest (off - dist))) l h = .ok ((.ok (), regs), after) ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      after.istates zs = some (matchEmitState s amount) ∧
      writtenBytes array (off + amount.toNat) (count + amount.toNat) =
        copyBack dict dist amount.toNat (writtenBytes output off count) := by
  let array := copy true output amount.toNat (off - dist) off output
  let regs := {l with left := l.left - amount, copy := (0 : UInt32), put := .ref dest (off + amount.toNat), from_ := .ref dest (off - dist + amount.toNat)}
  let after := setI (Space.put h dest array) zs (matchEmitState s amount)
  have sourceGet : Space.get h dest = some (if dest = dest then output else output) := by
    simpa only [ite_true] using get
  have run := matchEmit_run (source := dest) (saved := output) E put get write sourceGet
    room (by simpa only [ite_true] using (show off - dist + amount.toNat ≤ output.size by omega)) positive
  have actual : runX (matchEmit c amount (.ref dest (off - dist))) l h = .ok ((.ok (), regs), after) := by
    simpa only [decide_true] using run
  refine ⟨regs, after, array, actual, ?_, copy_size true output _ _ _ _, by simp [after], ?_⟩
  · rw [byte_view_get_setI]
    exact byte_view_get_put get write array
  · dsimp only [array]
    rw [copy_output_eq]
    exact output_copy_refines_lz77 dict output off count dist amount.toNat countFit distance inOutput room

/-- A saved-window segment of the actual slow loop agrees with the
independent growing-history copy until its source reaches current output. -/
theorem matchEmit_saved_semantics
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {dest source : BRef} {output saved : Array UInt8}
    {off count sourceOffset dist : Nat} {amount : UInt32}
    (E : Env c h r zs z s) (put : l.put = .ref dest off)
    (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (savedGet : Space.get h source = some saved) (different : source ≠ dest)
    (positive : 0 < amount.toNat) (countFit : count ≤ off)
    (inWindow : count < dist) (dict : List UInt8) (available : dist ≤ dict.length + count)
    (segment : amount.toNat ≤ dist - count) (room : off + amount.toNat ≤ output.size)
    (savedFit : sourceOffset + amount.toNat ≤ saved.size)
    (contents : ∀ i, i < amount.toNat → saved.getD (sourceOffset + i) 0 =
      dict.getD (dict.length + count - dist + i) 0) :
    ∃ regs after array,
      runX (matchEmit c amount (.ref source sourceOffset)) l h = .ok ((.ok (), regs), after) ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      after.istates zs = some (matchEmitState s amount) ∧
      writtenBytes array (off + amount.toNat) (count + amount.toNat) =
        copyBack dict dist amount.toNat (writtenBytes output off count) := by
  let array := copy false saved amount.toNat sourceOffset off output
  let regs := {l with left := l.left - amount, copy := (0 : UInt32), put := .ref dest (off + amount.toNat), from_ := .ref source (sourceOffset + amount.toNat)}
  let after := setI (Space.put h dest array) zs (matchEmitState s amount)
  have sourceGet : Space.get h source = some (if source = dest then output else saved) := by
    simpa only [ite_eq_right different] using savedGet
  have run := matchEmit_run E put get write sourceGet room
    (by simpa only [ite_eq_right different] using savedFit) positive
  have actual : runX (matchEmit c amount (.ref source sourceOffset)) l h = .ok ((.ok (), regs), after) := by
    simpa only [different, decide_false] using run
  refine ⟨regs, after, array, actual, ?_, copy_size false saved _ _ _ _, by simp [after], ?_⟩
  · rw [byte_view_get_setI]
    exact byte_view_get_put get write array
  · dsimp only [array]
    rw [copy_saved_eq]
    exact window_copy_refines_lz77 dict output saved off count sourceOffset dist amount.toNat
      countFit inWindow available segment room savedFit contents

/-- Actual MATCH chooses and emits the same positive current-output
segment as independent copyBack, including an output-limited partial match. -/
theorem inflate_MATCH_output_semantics
    {c : Ctx} {h : Heap} {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    {l : IL} {dest : BRef} {output : Array UInt8} {off count : Nat}
    (E : Env c h r zs z s) (put : l.put = .ref dest off)
    (get : Space.get h dest = some output) (write : Space.ro h dest = false)
    (left : 0 < l.left.toNat) (length : 0 < s.length.toNat)
    (distance : 0 < s.offset.toNat) (countFit : count ≤ off)
    (countBound : l.left.toNat ≤ l.out_.toNat)
    (countEq : count = l.out_.toNat - l.left.toNat)
    (inOutput : s.offset.toNat ≤ count) (room : off + l.left.toNat ≤ output.size)
    (dict : List UInt8) :
    ∃ regs after array amount,
      runX (inflate_MATCH c) l h = .ok ((.ok (), regs), after) ∧
      amount = (if s.length > l.left then l.left else s.length) ∧
      0 < amount.toNat ∧ amount.toNat ≤ l.left.toNat ∧ amount.toNat ≤ s.length.toNat ∧
      Space.get after dest = some array ∧ array.size = output.size ∧
      after.istates zs = some (matchEmitState s amount) ∧
      writtenBytes array (off + amount.toNat) (count + amount.toNat) =
        copyBack dict s.offset.toNat amount.toNat (writtenBytes output off count) := by
  let amount := if s.length > l.left then l.left else s.length
  have bounds : 0 < amount.toNat ∧ amount.toNat ≤ l.left.toNat ∧ amount.toNat ≤ s.length.toNat := by
    dsimp only [amount]
    split <;> simp only [UInt32.lt_iff_toNat_lt] at * <;> omega
  have leftNe : l.left ≠ 0 := by intro zero; rw [zero] at left; contradiction
  have subCount : (l.out_ - l.left).toNat = count := by
    rw [UInt32.toNat_sub_of_le _ _ countBound, countEq]
  have branch : ¬ s.offset > l.out_ - l.left := by
    simp only [UInt32.lt_iff_toNat_lt, subCount]
    omega
  have address : l.put.add (-(s.offset.toNat : Int)) h =
      .ok (.ref dest (off - s.offset.toNat), h) := by
    rw [put]
    exact Ptr.sub_nat_ok get (by omega) (by omega)
  obtain ⟨regs, after, array, emit, getAfter, size, state, bytes⟩ :=
    matchEmit_output_semantics E put get write bounds.1 countFit distance inOutput
      (by omega) dict
  refine ⟨regs, after, array, amount, ?_, rfl, bounds.1, bounds.2.1, bounds.2.2,
    getAfter, size, state, bytes⟩
  rw [inflate_MATCH_select_cut, matchSelect_output_cut E l leftNe branch address]
  exact emit

#print axioms copy_output_eq
#print axioms copy_saved_eq
#print axioms matchEmit_output_semantics
#print axioms matchEmit_saved_semantics
#print axioms inflate_MATCH_output_semantics
end Zlib.Inflate.Proofs.SlowMatchSemanticPath
