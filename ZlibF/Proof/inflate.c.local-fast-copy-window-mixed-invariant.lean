import ZlibF.Proof.«inflate.c.local-fast-state»
import ZlibF.Proof.«inflate.c.local-fast-copy-window-output-invariant»
import ZlibF.Proof.«inflate.c.fast-view-window-output-invariant»
import ZlibF.Proof.«inflate.c.fast-view-window-mixed»

namespace Zlib.Inflate.Local
open C Zlib.Inflate Zlib.Inflate.Spec Zlib.Inflate.Proofs ZlibF.Spec.Public
set_option autoImplicit false

/-- The no-wrap mixed window/output branch of translated `copyMatch`
retains the default state, exact bytes and the caller output frame. -/
theorem FastInputPacket.copyMatch_window_nowrap_mixed_local_state
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
      LocalStateJ after cutoff r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
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
      Space.ro after dest = false ∧
      after = Space.put h dest
        (Zlib.Inffast.Proofs.cpyN
          (l.len.toNat - (l.dist - l.op).toNat)
          (j + (l.dist - l.op).toNat - l.dist.toNat)
          (j + (l.dist - l.op).toNat)
          (Zlib.Inffast.Proofs.blitN saved
            (l.dist - l.op).toNat
            (woff + (c.wsize.toNat - (l.dist - l.op).toNat))
            j output)) ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  let back := l.dist - l.op
  let n := l.len.toNat - back.toNat
  have backNat : back.toNat = l.dist.toNat - l.op.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub
      (by have := UInt32.lt_iff_toNat_lt.mp windowBranch; omega)
  have positive : 1 ≤ back.toNat := by
    rw [backNat]
    have := UInt32.lt_iff_toNat_lt.mp windowBranch
    omega
  have remaining : 1 ≤ n := by
    have mixedNat := UInt32.lt_iff_toNat_lt.mp mixed
    change back.toNat < l.len.toNat at mixedNat
    change 1 ≤ l.len.toNat - back.toNat
    omega
  have lenCount : l.len.toNat = back.toNat + n := by
    dsimp [n]
    omega
  have startNat : (c.wsize - back).toNat =
      c.wsize.toNat - back.toNat :=
    Zlib.Inffast.Proofs.u32_toNat_sub backSize
  have backBound : back.toNat ≤ c.wsize.toNat := backSize
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
  have distance : l.dist.toNat ≤ j + back.toNat := by
    rw [backNat]
    omega
  obtain ⟨result, after, mixedRun, resultPacket,
      resultInvariant, resultBuffers, sizes, mixedEq,
      mixedBytes, mixedWrite, mixedHeap, frame⟩ :=
    Zlib.Inflate.Local.FastInputPacket.window_then_output_local_state packetWindow
      invariant buffers left (m := back.toNat) (n := n)
      rfl (by simpa only [atWindow] using lenCount)
      positive remaining different (by rfl) windowGet
      (by dsimp [start]; omega)
      (by simpa only [atWindow] using outPtr)
      outputPtr outputGet outputWrite outputSize
      (by omega : oo ≤ j ∧
        j + back.toNat + n ≤ oo + slow.left.toNat)
      (by simpa only [atWindow] using distance)
  have exactResult : result = { l with
      from_ := .ref dest (j + l.len.toNat - l.dist.toNat),
      out := .ref dest (j + l.len.toNat),
      op := 0,
      len := UInt32.ofNat
        ((l.len.toNat - (l.dist - l.op).toNat) % 3) } := by
    rw [mixedEq]
    simp only [atWindow]
    have lenCount' : l.len.toNat =
        (l.dist - l.op).toNat + n := lenCount
    have distance' : l.dist.toNat ≤ j +
        (l.dist - l.op).toNat := distance
    congr 1 <;> rw [lenCount'] <;> congr 1 <;> omega
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
    have condEq : Zlib.Inffast.Proofs.cond3 =
        (fun l : Zlib.Inffast.L =>
          (pure (l.len > 2, l) : M (Bool × Zlib.Inffast.L))) := rfl
    have bodyEq : Zlib.Inffast.Proofs.body3 =
        (fun l : Zlib.Inffast.L => do
          let l ← Zlib.Inffast.copy1 l
          let l ← Zlib.Inffast.copy1 l
          let l ← Zlib.Inffast.copy1 l
          pure { l with len := l.len - 3 }) := rfl
    rw [condEq, bodyEq] at mixedRun
    simpa [atWindow, back] using mixedRun
  exact ⟨result, after, run, resultPacket, resultInvariant,
    resultBuffers, sizes, exactResult,
    by simpa only [start, back, n] using mixedBytes,
    mixedWrite,
    by simpa only [start, back, n] using mixedHeap, frame⟩

#print axioms FastInputPacket.copyMatch_window_nowrap_mixed_local_state
end Zlib.Inflate.Local
