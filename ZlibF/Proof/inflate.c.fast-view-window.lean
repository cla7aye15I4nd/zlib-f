import ZlibF.Proof.«inflate.c.fast-view-window-output»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

private theorem fastCond_eq_inline :
    Zlib.Inffast.Proofs.cond3 =
      (fun l : Zlib.Inffast.L =>
        (pure (l.len > 2, l) : M (Bool × Zlib.Inffast.L))) := rfl

private theorem fastBody_eq_inline :
    Zlib.Inffast.Proofs.body3 =
      (fun l : Zlib.Inffast.L => do
        let l ← Zlib.Inffast.copy1 l
        let l ← Zlib.Inffast.copy1 l
        let l ← Zlib.Inffast.copy1 l
        pure { l with len := l.len - 3 }) := rfl

/-- The no-wrap window branch of the translated `copyMatch` when the entire
match is available contiguously in the current window. -/
theorem FastInputPacket.copyMatch_window_nowrap_short_view
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
    (wholeWindow : l.len.toNat ≤ (l.dist - l.op).toNat)
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
          (woff + (c.wsize.toNat - (l.dist - l.op).toNat)
            + l.len.toNat),
        out := .ref dest (j + l.len.toNat),
        op := l.dist - l.op,
        len := UInt32.ofNat (l.len.toNat % 3) } ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.blitN saved l.len.toNat
          (woff + (c.wsize.toNat - (l.dist - l.op).toNat))
          j output) ∧
      Space.ro after dest = false := by
  let back := l.dist - l.op
  have backBound : back.toNat ≤ c.wsize.toNat := backSize
  have wholeWindow' : l.len.toNat ≤ back.toNat := wholeWindow
  have startNat : (c.wsize - back).toNat =
      c.wsize.toNat - back.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub backBound
  let start := woff + (c.wsize.toNat - back.toNat)
  have addRun : OkOn h
      (Ptr.add c.window (c.wsize - back).toNat)
      (.ref window start) := by
    rw [windowPtr, startNat]
    exact Ptr.add_nat_ok windowGet (by omega)
  let atWindow : Zlib.Inffast.L := { l with
    op := back, from_ := .ref window start }
  have packetWindow : FastInputPacket h slow bs atWindow :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨result, after, tailRun, resultPacket,
      tailEq, tailBytes, tailWrite⟩ :=
    packetWindow.tailW_view (n := l.len.toNat) rfl
      separate left (by rfl) windowGet
      (by dsimp [start]; omega)
      (by simp [atWindow, outPtr]) outputPtr outputGet
      outputWrite outputSize outputRoom
  have exactResult : result = { l with
      from_ := .ref window
        (woff + (c.wsize.toNat - (l.dist - l.op).toNat)
          + l.len.toNat),
      out := .ref dest (j + l.len.toNat),
      op := l.dist - l.op,
      len := UInt32.ofNat (l.len.toNat % 3) } := by
    rw [tailEq]
  have bytes : Space.get after dest = some
      (Zlib.Inffast.Proofs.blitN saved l.len.toNat start j output) := by
    simpa [different] using tailBytes
  have run : Zlib.Inffast.copyMatch c l h =
      .ok (result, after) := by
    have noCopy : ¬ back < l.len := by
      intro smaller
      have size := UInt32.lt_iff_toNat_lt.mp smaller
      omega
    have noCopy' : ¬ l.dist - l.op < l.len := noCopy
    unfold Zlib.Inffast.copyMatch
    simp [windowBranch, validBack, noWrap]
    change Ptr.add c.window (c.wsize - back).toNat h =
      .ok (.ref window start, h) at addRun
    rw [addRun]
    simp only [noCopy', ite_false]
    simp only [Zlib.Inffast.Proofs.tailW,
      Zlib.Inffast.Proofs.tailIf, C.run, bind_app] at tailRun
    rw [fastCond_eq_inline, fastBody_eq_inline] at tailRun
    simpa [atWindow] using tailRun
  exact ⟨result, after, run, resultPacket, exactResult,
    by simpa only [start, back] using bytes, tailWrite⟩

end Zlib.Inflate.Proofs
