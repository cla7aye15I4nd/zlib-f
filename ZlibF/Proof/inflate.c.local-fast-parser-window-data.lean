import ZlibF.Proof.«inflate.c.local-fast-state»
import ZlibF.Proof.«inflate.c.fast-view-match-result»
import ZlibF.Proof.«inflate.c.caller-buffers»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A valid fast distance that reaches the window resolves to the live
private window block already required by `Good`. -/
theorem fast_window_data_of_local_good
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {l : Zlib.Inffast.L}
    (good : LocalGood h cutoff r zs z s)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (windowEq : c.window = s.window)
    {dest : BRef}
    (privateWindow : ∀ w,
      s.window = .ref (.blk w) 0 → dest ≠ .blk w)
    (windowBranch : l.dist > l.op)
    (validBack : ¬ l.dist - l.op > c.whave) :
    ∃ (window : BRef) (saved : Array UInt8) (woff : Nat),
      window ≠ dest ∧
      c.window = .ref window woff ∧
      Space.get h window = some saved ∧
      woff + c.wsize.toNat ≤ saved.size := by
  have positive : 0 < (l.dist - l.op).toNat := by
    have distGt := UInt32.lt_iff_toNat_lt.mp windowBranch
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by omega)]
    omega
  have backLeWhave : (l.dist - l.op).toNat ≤ c.whave.toNat := by
    by_cases hle : (l.dist - l.op).toNat ≤ c.whave.toNat
    · exact hle
    · have hgt : c.whave.toNat < (l.dist - l.op).toNat := by
        omega
      exact False.elim (validBack (UInt32.lt_iff_toNat_lt.mpr hgt))
  have wsizePositive : 0 < s.wsize.toNat := by
    have hv := good.inv.win.hv
    rw [← whaveEq, ← wsizeEq] at hv
    have positiveC : 0 < c.wsize.toNat := by omega
    simpa only [wsizeEq] using positiveC
  rcases good.inv.win.block with null | ⟨w, saved, win, get, _, sz⟩
  · have zero := good.inv.win.nullws null
    rw [zero] at wsizePositive
    simp at wsizePositive
  · have sizeEq : s.wsize.toNat = 2 ^ s.wbits.toNat := by
      rcases good.inv.win.ws with zero | size
      · omega
      · exact size
    refine ⟨.blk w, saved, 0, ?_, ?_, ?_, ?_⟩
    · exact (privateWindow w win).symm
    · rw [windowEq]
      exact win
    · exact get
    · simp only [Nat.zero_add, wsizeEq, sizeEq, sz, Nat.le_refl]

/-- Public caller storage supplies the private-window separation used by
the fast match theorem, including shared but disjoint input/output storage. -/
theorem fast_window_data_of_local_caller
    {h : Heap} {cutoff : Nat} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {l : Zlib.Inffast.L}
    {slow : IL} {dest : BRef} {oo : Nat}
    (good : LocalGood h cutoff r zs z s)
    (range : CallerRange h r slow.put slow.left.toNat true)
    (outputPtr : slow.put = .ref dest oo)
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (windowEq : c.window = s.window) :
    l.dist > l.op →
    ¬ l.dist - l.op > c.whave →
      ∃ (window : BRef) (saved : Array UInt8) (woff : Nat),
        window ≠ dest ∧
        c.window = .ref window woff ∧
        Space.get h window = some saved ∧
        woff + c.wsize.toNat ≤ saved.size := by
  intro branch validBack
  exact fast_window_data_of_local_good good whaveEq wsizeEq
    windowEq (callerRange_private_window good range outputPtr)
    branch validBack

end Zlib.Inflate.Local
