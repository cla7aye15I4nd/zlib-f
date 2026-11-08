import ZlibF.Proof.«inflate.c.fast-view-window-wrapped»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A wrapped match copies the tail of the window, then continues at the
start of that same window. This follows the translated `copyOp` call and the
same tail loop used by `copyMatch`. -/
theorem FastInputPacket.window_then_window_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx} {m n : Nat}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (opCount : l.op.toNat = m)
    (lenCount : l.len.toNat = m + n)
    (positive : 1 ≤ m) (remaining : 1 ≤ n)
    {window dest : BRef} (different : window ≠ dest)
    {saved output : Array UInt8} {fo woff oo j : Nat}
    (fromPtr : l.from_ = .ref window fo)
    (windowPtr : c.window = .ref window woff)
    (windowGet : Space.get h window = some saved)
    (windowRoom : fo + m ≤ saved.size)
    (windowStartRoom : woff + n ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧
      j + m + n ≤ oo + slow.left.toNat) :
    ∃ result after copied heap1,
      C.run (do
        let before := { l with len := l.len - l.op }
        let copied ← Zlib.Inffast.copyOp before
        Zlib.Inffast.Proofs.tailW { copied with from_ := c.window }) h =
          .ok (result, after) ∧
      C.run (Zlib.Inffast.copyOp { l with len := l.len - l.op }) h =
        .ok (copied, heap1) ∧
      copied.len = l.len - l.op ∧
      FastInputPacket after slow bs result ∧
      result = { l with
        from_ := .ref window (woff + n),
        out := .ref dest (j + m + n),
        op := 0,
        len := UInt32.ofNat (n % 3) } ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.blitN saved n woff (j + m)
          (Zlib.Inffast.Proofs.blitN saved m fo j output)) ∧
      Space.ro after dest = false := by
  let before : Zlib.Inffast.L := { l with len := l.len - l.op }
  have packetBefore : FastInputPacket h slow bs before :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨copied, heap1, copyRun, packet1, _, _, _, copyBytes,
      copyWritable, copySource, copyEq⟩ :=
    packetBefore.copyOp_distinct_view separate left different
      fromPtr windowGet
      (by dsimp [before]; rw [opCount]; exact windowRoom)
      outPtr outputPtr outputGet outputWrite outputSize
      (by dsimp [before]; rw [opCount]; omega)
      (by dsimp [before]; rw [opCount]; exact positive)
  have lenAfter : (l.len - l.op).toNat = n := by
    rw [Zlib.Inffast.Proofs.u32_toNat_sub (by omega)]
    omega
  have copyCount : copied.len.toNat = n := by
    rw [copyEq]
    simpa only [before] using lenAfter
  have copiedOut : copied.out = .ref dest (j + m) := by
    rw [copyEq]
    simp [before, opCount]
  let intermediate := Zlib.Inffast.Proofs.blitN saved m fo j output
  have intermediateGet : Space.get heap1 dest = some intermediate := by
    have beforeOp : before.op.toNat = m := by
      simpa [before] using opCount
    simpa only [copyOtherBytes_eq_blitN, beforeOp]
      using copyBytes
  have intermediateSize : intermediate.size = output.size :=
    Zlib.Inffast.Proofs.blitN_size saved m fo j output
  let tailStart : Zlib.Inffast.L := { copied with from_ := c.window }
  have packetTail : FastInputPacket heap1 slow bs tailStart :=
    ⟨packet1.source, packet1.cursor, packet1.hold, packet1.bits⟩
  obtain ⟨result, after, tailRun, resultPacket,
      tailEq, tailBytes, tailWritable⟩ :=
    packetTail.tailW_view (n := n) copyCount separate left
      (by simp [tailStart, windowPtr]) copySource windowStartRoom
      (by simp [tailStart, copiedOut]) outputPtr
      intermediateGet copyWritable
      (by rw [intermediateSize]; exact outputSize)
      (by omega : oo ≤ j + m ∧
        j + m + n ≤ oo + slow.left.toNat)
  have bytes : Space.get after dest = some
      (Zlib.Inffast.Proofs.blitN saved n woff (j + m)
        intermediate) := by
    simpa [different] using tailBytes
  have resultEq : result = { l with
      from_ := .ref window (woff + n),
      out := .ref dest (j + m + n), op := 0,
      len := UInt32.ofNat (n % 3) } := by
    rw [tailEq]
    simp [tailStart, copyEq, before, opCount]
  have run : C.run (do
      let before := { l with len := l.len - l.op }
      let copied ← Zlib.Inffast.copyOp before
      Zlib.Inffast.Proofs.tailW { copied with from_ := c.window }) h =
        .ok (result, after) := by
    change Zlib.Inffast.copyOp before h =
      .ok (copied, heap1) at copyRun
    change (Zlib.Inffast.copyOp before >>= fun copied =>
      Zlib.Inffast.Proofs.tailW { copied with from_ := c.window }) h = _
    simp only [bind_app, copyRun]
    exact tailRun
  exact ⟨result, after, copied, heap1, run, copyRun,
    by rw [copyEq], resultPacket, resultEq,
    bytes, tailWritable⟩

end Zlib.Inflate.Proofs
