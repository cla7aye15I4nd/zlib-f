import ZlibF.Proof.«inflate.c.fast-view-window-wrapped-two»
import ZlibF.Proof.«inflate.c.fast-view-window-mixed»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem wrappedThreeCond_eq_inline :
    Zlib.Inffast.Proofs.cond3 =
      (fun l : Zlib.Inffast.L =>
        (pure (l.len > 2, l) : M (Bool × Zlib.Inffast.L))) := rfl

private theorem wrappedThreeBody_eq_inline :
    Zlib.Inffast.Proofs.body3 =
      (fun l : Zlib.Inffast.L => do
        let l ← Zlib.Inffast.copy1 l
        let l ← Zlib.Inffast.copy1 l
        let l ← Zlib.Inffast.copy1 l
        pure { l with len := l.len - 3 }) := rfl

/-- The wrapped branch of translated `copyMatch` copies from the window
end, then its start, then from already produced output. -/
theorem FastInputPacket.copyMatch_window_wrapped_three_view
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
    (third : c.wnext < l.len - (l.dist - l.op - c.wnext))
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
          (Zlib.Inffast.Proofs.blitN saved c.wnext.toNat woff
            (j + (l.dist - l.op - c.wnext).toNat)
            (Zlib.Inffast.Proofs.blitN saved
              (l.dist - l.op - c.wnext).toNat
              (woff + (c.wsize.toNat + c.wnext.toNat -
                (l.dist - l.op).toNat)) j output))) ∧
      Space.ro after dest = false := by
  let back := l.dist - l.op
  let last := back - c.wnext
  let n := l.len.toNat - back.toNat
  have backNat : back.toNat = l.dist.toNat - l.op.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub
      (by have := UInt32.lt_iff_toNat_lt.mp windowBranch; omega)
  have backBound : back.toNat ≤ c.wsize.toNat := backSize
  have wrapNat : c.wnext.toNat < back.toNat :=
    UInt32.lt_iff_toNat_lt.mp wrap
  have lastNat : last.toNat = back.toNat - c.wnext.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub (by omega)
  have mixedNat : last.toNat < l.len.toNat :=
    UInt32.lt_iff_toNat_lt.mp mixed
  have firstPositive : 1 ≤ last.toNat := by rw [lastNat]; omega
  have firstLen : (l.len - last).toNat =
      l.len.toNat - last.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub (by omega)
  have thirdNat : c.wnext.toNat < l.len.toNat - last.toNat := by
    have h := UInt32.lt_iff_toNat_lt.mp third
    rw [firstLen] at h
    exact h
  have nPositive : 1 ≤ n := by dsimp [n]; omega
  have lenCount : l.len.toNat = last.toNat + c.wnext.toNat + n := by
    dsimp [n]
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
  let before : Zlib.Inffast.L := { l with
    op := last, len := l.len - last,
    from_ := .ref window start }
  have packetBefore : FastInputPacket h slow bs before :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨copied, heap1, copyRun, packet1, _, _, _, copyBytes,
      copyWritable, copySource, copyEq⟩ :=
    packetBefore.copyOp_distinct_view separate left different
      (by rfl) windowGet
      (by dsimp [before, start]; rw [lastNat]; omega)
      (by simpa only [before] using outPtr)
      outputPtr outputGet outputWrite outputSize
      (by dsimp [before]; rw [lastNat]; omega)
      (by dsimp [before]; exact firstPositive)
  let intermediate := Zlib.Inffast.Proofs.blitN saved
    last.toNat start j output
  have intermediateGet : Space.get heap1 dest = some intermediate := by
    have beforeOp : before.op.toNat = last.toNat := rfl
    simpa only [copyOtherBytes_eq_blitN, beforeOp]
      using copyBytes
  have intermediateSize : intermediate.size = output.size :=
    Zlib.Inffast.Proofs.blitN_size saved last.toNat start j output
  have copiedOut : copied.out = .ref dest (j + last.toNat) := by
    rw [copyEq]
  have copiedDist : copied.dist = l.dist := by
    rw [copyEq]
  have copiedLen : copied.len.toNat =
      c.wnext.toNat + n := by
    rw [copyEq]
    simp only [before]
    rw [firstLen]
    omega
  let second : Zlib.Inffast.L := { copied with
    op := c.wnext, from_ := c.window }
  have packetSecond : FastInputPacket heap1 slow bs second :=
    ⟨packet1.source, packet1.cursor, packet1.hold, packet1.bits⟩
  have distance : l.dist.toNat ≤
      j + last.toNat + c.wnext.toNat := by
    have lastEq : last.toNat + c.wnext.toNat = back.toNat := by
      rw [lastNat]
      omega
    omega
  have wnextPositive : 1 ≤ c.wnext.toNat := by
    have hnot : c.wnext.toNat ≠ 0 := by
      intro hz
      apply nonZero
      apply UInt32.toNat_inj.mp
      simpa using hz
    omega
  obtain ⟨result, after, secondRun, resultPacket,
      secondEq, secondBytes, secondWrite⟩ :=
    packetSecond.window_then_output_view
      (m := c.wnext.toNat) (n := n) (fo := woff)
      separate left rfl copiedLen
      wnextPositive
      nPositive different (by simp [second, windowPtr])
      copySource
      (by omega)
      (by simp [second, copiedOut])
      outputPtr intermediateGet copyWritable
      (by rw [intermediateSize]; exact outputSize)
      (by omega : oo ≤ j + last.toNat ∧
        j + last.toNat + c.wnext.toNat + n ≤
          oo + slow.left.toNat)
      (by simpa only [second, copiedDist] using distance)
  have exactResult : result = { l with
      from_ := .ref dest (j + l.len.toNat - l.dist.toNat),
      out := .ref dest (j + l.len.toNat), op := 0,
      len := UInt32.ofNat (n % 3) } := by
    rw [secondEq]
    simp only [second, copyEq, before]
    have lastEq : last.toNat + c.wnext.toNat = back.toNat := by
      rw [lastNat]; omega
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
    change Zlib.Inffast.copyOp before h =
      .ok (copied, heap1) at copyRun
    simp only [bind_app]
    rw [copyRun]
    have copiedLenWord : copied.len = l.len - last := by
      rw [copyEq]
    have more : c.wnext < copied.len := by
      rw [copiedLenWord]
      exact third
    simp only [more, ite_true]
    simp only [Zlib.Inffast.Proofs.tailW,
      Zlib.Inffast.Proofs.tailIf, C.run, bind_app] at secondRun
    rw [wrappedThreeCond_eq_inline,
      wrappedThreeBody_eq_inline] at secondRun
    simpa [second, before] using secondRun
  have exactBytes : Space.get after dest = some
      (Zlib.Inffast.Proofs.cpyN
        (l.len.toNat - (l.dist - l.op).toNat)
        (j + (l.dist - l.op).toNat - l.dist.toNat)
        (j + (l.dist - l.op).toNat)
        (Zlib.Inffast.Proofs.blitN saved c.wnext.toNat woff
          (j + (l.dist - l.op - c.wnext).toNat)
          (Zlib.Inffast.Proofs.blitN saved
            (l.dist - l.op - c.wnext).toNat
            (woff + (c.wsize.toNat + c.wnext.toNat -
              (l.dist - l.op).toNat)) j output))) := by
    dsimp [second] at secondBytes
    rw [copiedDist] at secondBytes
    have prefixPos : j + last.toNat + c.wnext.toNat =
        j + back.toNat := by rw [lastNat]; omega
    rw [prefixPos] at secondBytes
    simpa only [n, back, last, start, intermediate] using secondBytes
  exact ⟨result, after, run, resultPacket,
    by simpa only [n, back] using exactResult,
    exactBytes,
    secondWrite⟩

end Zlib.Inflate.Proofs
