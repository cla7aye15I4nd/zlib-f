import ZlibF.Proof.«inflate.c.local-fast-state»
import ZlibF.Proof.«inflate.c.local-fast-copy-window-tail-invariant»
import ZlibF.Proof.«inflate.c.fast-view-window-tail-invariant»
import ZlibF.Proof.«inflate.c.fast-view-window»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- A whole match copied from the no-wrap window retains the default
state, exact bytes, and caller output frame. -/
theorem FastInputPacket.copyMatch_window_nowrap_short_local_state
    {cutoff : Nat}
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx}
    {r : ZStreamRef} {zs : Nat} {z : ZStream} {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : LocalStateJ h cutoff r zs z s)
    (buffers : DispatchBuffers h r slow bs)
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
      LocalStateJ after cutoff r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
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
      Space.ro after dest = false ∧
      after = Space.put h dest
        (Zlib.Inffast.Proofs.blitN saved l.len.toNat
          (woff + (c.wsize.toNat - (l.dist - l.op).toNat))
          j output) ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
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
      resultInvariant, resultBuffers, sizes, tailEq,
      tailBytes, tailWrite, tailHeap, frame⟩ :=
    Zlib.Inflate.Local.FastInputPacket.tailW_local_state packetWindow invariant buffers
      (n := l.len.toNat) rfl left
      (by rfl) windowGet (by dsimp [start]; omega)
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
  have noCopy : ¬ back < l.len := by
    intro smaller
    have size := UInt32.lt_iff_toNat_lt.mp smaller
    omega
  have run : Zlib.Inffast.copyMatch c l h =
      .ok (result, after) := by
    unfold Zlib.Inffast.copyMatch
    simp [windowBranch, validBack, noWrap]
    change Ptr.add c.window (c.wsize - back).toNat h =
      .ok (.ref window start, h) at addRun
    rw [addRun]
    have noCopy' : ¬ l.dist - l.op < l.len := noCopy
    simp only [noCopy', ite_false]
    simp only [Zlib.Inffast.Proofs.tailW,
      Zlib.Inffast.Proofs.tailIf, C.run, bind_app] at tailRun
    have condEq : Zlib.Inffast.Proofs.cond3 =
        (fun l : Zlib.Inffast.L =>
          (pure (l.len > 2, l) : M (Bool × Zlib.Inffast.L))) := rfl
    have bodyEq : Zlib.Inffast.Proofs.body3 =
        (fun l : Zlib.Inffast.L => do
          let l ← Zlib.Inffast.copy1 l
          let l ← Zlib.Inffast.copy1 l
          let l ← Zlib.Inffast.copy1 l
          pure { l with len := l.len - 3 }) := rfl
    rw [condEq, bodyEq] at tailRun
    simpa [atWindow] using tailRun
  exact ⟨result, after, run, resultPacket, resultInvariant,
    resultBuffers, sizes, exactResult,
    by simpa [start, back, different] using tailBytes, tailWrite,
    by simpa [start, back, different] using tailHeap, frame⟩

#print axioms FastInputPacket.copyMatch_window_nowrap_short_local_state
end Zlib.Inflate.Local
