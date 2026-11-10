import ZlibF.Proof.«inflate.c.fast-view-window-two»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem wrappedTwoCond_eq_inline :
    Zlib.Inffast.Proofs.cond3 =
      (fun l : Zlib.Inffast.L =>
        (pure (l.len > 2, l) : M (Bool × Zlib.Inffast.L))) := rfl

private theorem wrappedTwoBody_eq_inline :
    Zlib.Inffast.Proofs.body3 =
      (fun l : Zlib.Inffast.L => do
        let l ← Zlib.Inffast.copy1 l
        let l ← Zlib.Inffast.copy1 l
        let l ← Zlib.Inffast.copy1 l
        pure { l with len := l.len - 3 }) := rfl

/-- The wrapped branch of translated `copyMatch` copies the end of the
window and completes the match at its start. -/
theorem FastInputPacket.copyMatch_window_wrapped_two_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (windowBranch : l.dist > l.op)
    (validBack : ¬ l.dist - l.op > c.whave)
    (nonZero : c.wnext ≠ 0)
    (wrap : c.wnext < l.dist - l.op)
    (backSize : (l.dist - l.op).toNat ≤ c.wsize.toNat)
    (sumFits : c.wsize.toNat + c.wnext.toNat < 2 ^ 32)
    (mixed : l.dist - l.op - c.wnext < l.len)
    (middle : ¬ c.wnext < l.len - (l.dist - l.op - c.wnext))
    {window dest : BRef} (different : window ≠ dest)
    {saved output : Array UInt8} {woff oo j : Nat}
    (windowPtr : c.window = .ref window woff)
    (windowGet : Space.get h window = some saved)
    (windowSize : woff + c.wsize.toNat ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + l.len.toNat ≤ oo + slow.left.toNat) :
    ∃ result after,
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result = { l with
        from_ := .ref window
          (woff + (l.len.toNat -
            (l.dist - l.op - c.wnext).toNat)),
        out := .ref dest (j + l.len.toNat),
        op := 0,
        len := UInt32.ofNat
          ((l.len.toNat -
            (l.dist - l.op - c.wnext).toNat) % 3) } ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.blitN saved
          (l.len.toNat - (l.dist - l.op - c.wnext).toNat)
          woff (j + (l.dist - l.op - c.wnext).toNat)
          (Zlib.Inffast.Proofs.blitN saved
            (l.dist - l.op - c.wnext).toNat
            (woff + (c.wsize.toNat + c.wnext.toNat -
              (l.dist - l.op).toNat)) j output)) ∧
      Space.ro after dest = false := by
  let back := l.dist - l.op
  let last := back - c.wnext
  let n := l.len.toNat - last.toNat
  have backBound : back.toNat ≤ c.wsize.toNat := backSize
  have wrapNat : c.wnext.toNat < back.toNat :=
    UInt32.lt_iff_toNat_lt.mp wrap
  have lastNat : last.toNat = back.toNat - c.wnext.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub (by omega)
  have mixedNat : last.toNat < l.len.toNat :=
    UInt32.lt_iff_toNat_lt.mp mixed
  have positive : 1 ≤ last.toNat := by rw [lastNat]; omega
  have remaining : 1 ≤ n := by dsimp [n]; omega
  have lenCount : l.len.toNat = last.toNat + n := by
    dsimp [n]; omega
  have nCount : (l.len - last).toNat = n := by
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by omega)]
  have middleNat : n ≤ c.wnext.toNat := by
    have hnot := middle
    have hcontra : ¬ c.wnext.toNat < (l.len - last).toNat := by
      intro hlt
      exact hnot (UInt32.lt_iff_toNat_lt.mpr hlt)
    omega
  have sumNat : (c.wsize + c.wnext).toNat =
      c.wsize.toNat + c.wnext.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_add sumFits
  have startNat : (c.wsize + c.wnext - back).toNat =
      c.wsize.toNat + c.wnext.toNat - back.toNat := by
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by rw [sumNat]; omega), sumNat]
  let start := woff +
    (c.wsize.toNat + c.wnext.toNat - back.toNat)
  have addRun : OkOn h
      (Ptr.add c.window (c.wsize + c.wnext - back).toNat)
      (.ref window start) := by
    rw [windowPtr, startNat]
    exact Ptr.add_nat_ok windowGet (by omega)
  let atWindow : Zlib.Inffast.L := { l with
    op := last, from_ := .ref window start }
  have packetWindow : FastInputPacket h slow bs atWindow :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨result, after, copied, heap1, twoRun,
      copyRun, copiedLen, resultPacket, twoEq,
      twoBytes, twoWrite⟩ :=
    packetWindow.window_then_window_view (m := last.toNat) (n := n)
      separate left rfl (by simpa only [atWindow] using lenCount)
      positive remaining different (by rfl) windowPtr windowGet
      (by dsimp [start]; omega)
      (by omega)
      (by simpa only [atWindow] using outPtr)
      outputPtr outputGet outputWrite outputSize
      (by omega : oo ≤ j ∧
        j + last.toNat + n ≤ oo + slow.left.toNat)
  have exactResult : result = { l with
      from_ := .ref window
        (woff + (l.len.toNat - last.toNat)),
      out := .ref dest (j + l.len.toNat),
      op := 0,
      len := UInt32.ofNat ((l.len.toNat - last.toNat) % 3) } := by
    rw [twoEq]
    simp only [atWindow]
    have count' : l.len.toNat = last.toNat + n := lenCount
    congr 1 <;> congr 1 <;> omega
  have run : Zlib.Inffast.copyMatch c l h =
      .ok (result, after) := by
    unfold Zlib.Inffast.copyMatch
    simp [windowBranch, validBack, nonZero, wrap]
    change Ptr.add c.window (c.wsize + c.wnext - back).toNat h =
      .ok (.ref window start, h) at addRun
    rw [addRun]
    have mixed' : l.dist - l.op - c.wnext < l.len := mixed
    simp only [mixed', ite_true]
    change Zlib.Inffast.copyOp
      { atWindow with len := atWindow.len - atWindow.op } h =
      .ok (copied, heap1) at copyRun
    simp only [bind_app]
    rw [copyRun]
    have noMore : ¬ c.wnext < copied.len := by
      rw [copiedLen]
      exact middle
    simp only [noMore, ite_false]
    have tailRun : C.run (Zlib.Inffast.Proofs.tailW
        { copied with from_ := c.window }) heap1 =
        .ok (result, after) := by
      change (Zlib.Inffast.copyOp
        { atWindow with len := atWindow.len - atWindow.op } >>=
        fun copied => Zlib.Inffast.Proofs.tailW
          { copied with from_ := c.window }) h = _ at twoRun
      simp only [bind_app, copyRun] at twoRun
      exact twoRun
    simp only [Zlib.Inffast.Proofs.tailW,
      Zlib.Inffast.Proofs.tailIf, C.run, bind_app] at tailRun
    rw [wrappedTwoCond_eq_inline, wrappedTwoBody_eq_inline] at tailRun
    simpa using tailRun
  exact ⟨result, after, run, resultPacket,
    by simpa only [last] using exactResult,
    by simpa only [start, back, last, n] using twoBytes,
    twoWrite⟩

end Zlib.Inflate.Proofs
