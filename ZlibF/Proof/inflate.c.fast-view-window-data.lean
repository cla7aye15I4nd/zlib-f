import ZlibF.Proof.«inflate.c.fast-view-match-result»
import ZlibF.Proof.«inflate.c.caller-buffers»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A valid fast distance that reaches the window resolves to the live
private window block already required by `Good`. -/
theorem fast_window_data_of_good
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {l : Zlib.Inffast.L}
    (good : Good h r zs z s)
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
theorem fast_window_data_of_caller
    {h : Heap} {r : ZStreamRef} {zs : Nat}
    {z : ZStream} {s : InflateState}
    {c : Zlib.Inffast.Ctx} {l : Zlib.Inffast.L}
    {slow : IL} {dest : BRef} {oo : Nat}
    (good : Good h r zs z s)
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
  exact fast_window_data_of_good good whaveEq wsizeEq
    windowEq (callerRange_private_window good range outputPtr)
    branch validBack

/-- The live stream and the public caller range discharge the window
geometry and separation premises of the complete fast match theorem. -/
theorem FastInputPacket.copyMatch_view_of_good
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (good : Good h r zs z s)
    (streamPtr : c.strm = some r)
    (statePtr : c.state = some (.tab zs))
    (whaveEq : c.whave = s.whave)
    (wsizeEq : c.wsize = s.wsize)
    (wnextEq : c.wnext = s.wnext)
    (windowEq : c.window = s.window)
    (sane : s.sane ≠ 0)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (length : 3 ≤ l.len.toNat)
    {dest : BRef} {output : Array UInt8} {oo j : Nat}
    (range : CallerRange h r slow.put slow.left.toNat true)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j) :
    ∃ result after,
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result.againD = l.againD ∧
      result.againL = l.againL ∧
      ((result.broke = true ∧
        ∃ i, after = setI
          (r.put h { z with msg := .ref (.str i) 0 }) zs
          { s with mode := BAD } ∧
          Space.get after dest = some output ∧
          Space.ro after dest = false) ∨
       (result.broke = l.broke ∧
        ∃ array,
          result.out = .ref dest (j + l.len.toNat) ∧
          Space.get after dest = some array ∧
          array.size = output.size ∧
          Space.ro after dest = false)) := by
  have whaveBound : c.whave.toNat ≤ c.wsize.toNat := by
    rw [whaveEq, wsizeEq]
    exact good.inv.win.hv
  have wnextBound : c.wnext.toNat ≤ c.wsize.toNat := by
    rw [wnextEq, wsizeEq]
    rcases good.inv.win.wn with lt | zero
    · omega
    · omega
  have wsizeBound : c.wsize.toNat ≤ 32768 := by
    rw [wsizeEq]
    have pow := Nat.pow_le_pow_right
      (by decide : 0 < 2) good.inv.win.wbits
    rcases good.inv.win.ws with zero | size
    · omega
    · omega
  exact packet.copyMatch_view good streamPtr statePtr sane
    separate left length whaveBound wnextBound wsizeBound
    outPtr outputPtr outputGet outputWrite outputSize
    outputRoom produced
    (fast_window_data_of_caller good range outputPtr
      whaveEq wsizeEq windowEq)

end Zlib.Inflate.Proofs
