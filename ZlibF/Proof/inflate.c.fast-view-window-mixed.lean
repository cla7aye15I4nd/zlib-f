import ZlibF.Proof.«inflate.c.fast-view-window»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem fastCond_eq_inline_mixed :
    Zlib.Inffast.Proofs.cond3 =
      (fun l : Zlib.Inffast.L =>
        (pure (l.len > 2, l) : M (Bool × Zlib.Inffast.L))) := rfl

private theorem fastBody_eq_inline_mixed :
    Zlib.Inffast.Proofs.body3 =
      (fun l : Zlib.Inffast.L => do
        let l ← Zlib.Inffast.copy1 l
        let l ← Zlib.Inffast.copy1 l
        let l ← Zlib.Inffast.copy1 l
        pure { l with len := l.len - 3 }) := rfl

/-- The no-wrap window branch of translated `copyMatch` when the match
crosses from the window into already produced output. -/
theorem FastInputPacket.copyMatch_window_nowrap_mixed_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (windowBranch : l.dist > l.op)
    (validBack : ¬ l.dist - l.op > c.whave)
    (noWrap : c.wnext = 0)
    (backSize : (l.dist - l.op).toNat ≤ c.wsize.toNat)
    (mixed : l.dist - l.op < l.len)
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
      j + l.len.toNat ≤ oo + slow.left.toNat)
    (produced : l.op.toNat ≤ j) :
    ∃ result after,
      C.run (Zlib.Inffast.copyMatch c l) h =
        .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result = { l with
        from_ := .ref dest (j + l.len.toNat - l.dist.toNat),
        out := .ref dest (j + l.len.toNat),
        op := 0,
        len := UInt32.ofNat
          ((l.len.toNat - (l.dist - l.op).toNat) % 3) } ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.cpyN
          (l.len.toNat - (l.dist - l.op).toNat)
          (j + (l.dist - l.op).toNat - l.dist.toNat)
          (j + (l.dist - l.op).toNat)
          (Zlib.Inffast.Proofs.blitN saved
            (l.dist - l.op).toNat
            (woff + (c.wsize.toNat - (l.dist - l.op).toNat))
            j output)) ∧
      Space.ro after dest = false := by
  let back := l.dist - l.op
  let n := l.len.toNat - back.toNat
  have backNat : back.toNat = l.dist.toNat - l.op.toNat := by
    exact Zlib.Inffast.Proofs.u32_toNat_sub
      (by have := UInt32.lt_iff_toNat_lt.mp windowBranch; omega)
  have backNat' : (l.dist - l.op).toNat =
      l.dist.toNat - l.op.toNat := backNat
  have positive : 1 ≤ back.toNat := by
    rw [backNat]
    have := UInt32.lt_iff_toNat_lt.mp windowBranch
    omega
  have remaining : 1 ≤ n := by
    have := UInt32.lt_iff_toNat_lt.mp mixed
    have backEq : back.toNat = (l.dist - l.op).toNat := rfl
    change 1 ≤ l.len.toNat - back.toNat
    omega
  have lenCount : l.len.toNat = back.toNat + n := by
    dsimp [n]
    omega
  have startNat : (c.wsize - back).toNat =
      c.wsize.toNat - back.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub backSize
  let start := woff + (c.wsize.toNat - back.toNat)
  have addRun : OkOn h
      (Ptr.add c.window (c.wsize - back).toNat)
      (.ref window start) := by
    rw [windowPtr, startNat]
    have backBound : back.toNat ≤ c.wsize.toNat := backSize
    exact Ptr.add_nat_ok windowGet (by omega)
  let atWindow : Zlib.Inffast.L := { l with
    op := back, from_ := .ref window start }
  have packetWindow : FastInputPacket h slow bs atWindow :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  have distance : l.dist.toNat ≤ j + back.toNat := by
    rw [backNat]
    omega
  obtain ⟨result, after, mixedRun, resultPacket,
      mixedEq, mixedBytes, mixedWrite⟩ :=
    packetWindow.window_then_output_view (m := back.toNat) (n := n)
      separate left rfl (by simpa only [atWindow] using lenCount)
      positive remaining different (by rfl) windowGet
      (by
        have backBound : back.toNat ≤ c.wsize.toNat := backSize
        dsimp [start]
        omega)
      (by simpa only [atWindow] using outPtr)
      outputPtr outputGet outputWrite outputSize
      (by omega : oo ≤ j ∧ j + back.toNat + n ≤ oo + slow.left.toNat)
      (by simpa only [atWindow] using distance)
  have exactResult : result = { l with
      from_ := .ref dest (j + l.len.toNat - l.dist.toNat),
      out := .ref dest (j + l.len.toNat),
      op := 0,
      len := UInt32.ofNat
        ((l.len.toNat - (l.dist - l.op).toNat) % 3) } := by
    rw [mixedEq]
    simp only [atWindow]
    have backEq : back.toNat = (l.dist - l.op).toNat := rfl
    have lenCount' : l.len.toNat =
        (l.dist - l.op).toNat + n := lenCount
    have distance' : l.dist.toNat ≤ j +
        (l.dist - l.op).toNat := distance
    congr 1 <;> rw [backEq, lenCount'] <;> congr 1 <;> omega
  have run : Zlib.Inffast.copyMatch c l h =
      .ok (result, after) := by
    unfold Zlib.Inffast.copyMatch
    simp [windowBranch, validBack, noWrap]
    change Ptr.add c.window (c.wsize - back).toNat h =
      .ok (.ref window start, h) at addRun
    rw [addRun]
    have mixed' : l.dist - l.op < l.len := mixed
    simp only [mixed', ite_true]
    simp only [Zlib.Inffast.Proofs.tailW,
      Zlib.Inffast.Proofs.tailIf, C.run, bind_app] at mixedRun
    rw [fastCond_eq_inline_mixed, fastBody_eq_inline_mixed] at mixedRun
    simpa [atWindow, back] using mixedRun
  exact ⟨result, after, run, resultPacket, exactResult,
    by simpa only [start, back, n] using mixedBytes,
    mixedWrite⟩

end Zlib.Inflate.Proofs
