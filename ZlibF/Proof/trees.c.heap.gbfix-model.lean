import ZlibF.Proof.«trees.c.heap.gbfix»
import ZlibF.Math.HuffmanRepairModel

/-! # The actual count-repair loop follows the pure repair model exactly -/

namespace Zlib.Trees.Proofs
open C Zlib.Trees
set_option autoImplicit false

theorem deepestX_repair (c : Nat → Nat) (b : Nat) : deepestX c b = HuffmanAbstract.deepest c b := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [deepestX, HuffmanAbstract.deepest, ih]

/-- The exact count update already proved for one source round agrees
with the model used by the pure rank/repair argument. -/
theorem fixStep_repair (L : Nat) (c : Nat → Nat) : fixStep L c = HuffmanAbstract.repairStep L c := by
  unfold fixStep HuffmanAbstract.repairStep
  rw [deepestX_repair]
  rfl

theorem fixIter_repair (L M : Nat) (c : Nat → Nat) : fixIter L M c = HuffmanAbstract.repairIter L M c := by
  induction M generalizing c with
  | zero => rfl
  | succ M ih => simp only [fixIter, HuffmanAbstract.repairIter, fixStep_repair, ih]

/-- The complete actual overflow loop executes exactly R+1 pure repair
steps on its real count array. Its source execution theorem discharges the
model relation; no called-function contract is a premise. -/
theorem ws_gbFixLoop_repair_model {h0 : Heap} {id : Nat} (e1 : DeflateState) (ml : Int32)
    (L NL R : Nat) (hmlv : ml.toInt = L) (hL1 : 1 ≤ L) (hL15 : L ≤ 15)
    (hNL : NL ≤ 2 ^ L) (hNL2 : NL ≤ 1000) (ov : Int32) (c0 : Nat → Nat) (e : DeflateState)
    (initial : FixInvX L NL (R + 1) ov c0 e1 e) :
    WS h0 id (cdoWhile (σ := Int32) (gbFix (Sp id) ml)
      (fun overflow => pure (decide (overflow.toInt > 0), overflow)) ov) e
      (fun o result => FixInvX L NL 0 o (HuffmanAbstract.repairIter L (R + 1) c0) e1 result) := by
  simpa only [fixIter_repair] using ws_gbFixLoop e1 ml L NL R hmlv hL1 hL15 hNL hNL2 ov c0 e initial

end Zlib.Trees.Proofs
