import ZlibF.Proof.«inflate.c.fast-view-direct»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A source-identical mixed match suffix: copy a positive prefix from the
window, then continue the remaining match from already produced output. -/
theorem FastInputPacket.window_then_output_view
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {m n : Nat}
    (packet : FastInputPacket h slow bs l)
    (separate : Separate slow.next slow.have_.toNat
      slow.put slow.left.toNat)
    (left : slow.left ≠ 0)
    (opCount : l.op.toNat = m)
    (lenCount : l.len.toNat = m + n)
    (positive : 1 ≤ m) (remaining : 1 ≤ n)
    {window dest : BRef} (different : window ≠ dest)
    {saved output : Array UInt8} {fo oo j : Nat}
    (fromPtr : l.from_ = .ref window fo)
    (windowGet : Space.get h window = some saved)
    (windowRoom : fo + m ≤ saved.size)
    (outPtr : l.out = .ref dest j)
    (outputPtr : slow.put = .ref dest oo)
    (outputGet : Space.get h dest = some output)
    (outputWrite : Space.ro h dest = false)
    (outputSize : oo + slow.left.toNat ≤ output.size)
    (outputRoom : oo ≤ j ∧ j + m + n ≤ oo + slow.left.toNat)
    (distance : l.dist.toNat ≤ j + m) :
    ∃ result after,
      C.run (do
        let before := { l with len := l.len - l.op }
        let copied ← Zlib.Inffast.copyOp before
        let from_ ← Zlib.Inffast.subn copied.out copied.dist
        Zlib.Inffast.Proofs.tailW { copied with from_ }) h =
          .ok (result, after) ∧
      FastInputPacket after slow bs result ∧
      result = { l with
        from_ := .ref dest (j + m - l.dist.toNat + n),
        out := .ref dest (j + m + n),
        op := 0,
        len := UInt32.ofNat (n % 3) } ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.cpyN n
          (j + m - l.dist.toNat) (j + m)
          (Zlib.Inffast.Proofs.blitN saved m fo j output)) ∧
      Space.ro after dest = false := by
  let before : Zlib.Inffast.L := { l with len := l.len - l.op }
  have packetBefore : FastInputPacket h slow bs before :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨copied, heap1, copyRun, packet1, _, _, _, copyBytes,
      copyWritable, _, copyEq⟩ :=
    packetBefore.copyOp_distinct_view separate left different
      fromPtr windowGet (by dsimp [before]; rw [opCount]; exact windowRoom)
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
  have copiedDist : copied.dist = l.dist := by
    rw [copyEq]
  let intermediate := Zlib.Inffast.Proofs.blitN saved m fo j output
  have intermediateGet : Space.get heap1 dest = some intermediate := by
    have beforeOp : before.op.toNat = m := by
      simpa [before] using opCount
    simpa only [copyOtherBytes_eq_blitN, beforeOp]
      using copyBytes
  have intermediateSize : intermediate.size = output.size := by
    exact Zlib.Inffast.Proofs.blitN_size saved m fo j output
  have subRun : OkOn heap1
      (Zlib.Inffast.subn copied.out copied.dist)
      (.ref dest (j + m - l.dist.toNat)) := by
    rw [copiedOut, copiedDist]
    exact Zlib.Inffast.Proofs.subn_ok intermediateGet distance
      (by rw [intermediateSize]; omega)
  let tailStart : Zlib.Inffast.L := { copied with
    from_ := .ref dest (j + m - l.dist.toNat) }
  have packetTail : FastInputPacket heap1 slow bs tailStart :=
    ⟨packet1.source, packet1.cursor, packet1.hold, packet1.bits⟩
  obtain ⟨result, after, tailRun, resultPacket,
      tailEq, tailBytes, tailWritable⟩ :=
    packetTail.tailW_view (n := n) copyCount separate left
      (by rfl) intermediateGet
      (by rw [intermediateSize]; omega)
      (by simp [tailStart, copiedOut]) outputPtr
      intermediateGet copyWritable
      (by rw [intermediateSize]; exact outputSize)
      (by omega : oo ≤ j + m ∧
        j + m + n ≤ oo + slow.left.toNat)
  have bytes : Space.get after dest = some
      (Zlib.Inffast.Proofs.cpyN n
        (j + m - l.dist.toNat) (j + m) intermediate) := by
    simpa using tailBytes
  have resultEq : result = { l with
      from_ := .ref dest (j + m - l.dist.toNat + n),
      out := .ref dest (j + m + n), op := 0,
      len := UInt32.ofNat (n % 3) } := by
    rw [tailEq]
    simp [tailStart, copyEq, before, opCount]
  have run : C.run (do
      let before := { l with len := l.len - l.op }
      let copied ← Zlib.Inffast.copyOp before
      let from_ ← Zlib.Inffast.subn copied.out copied.dist
      Zlib.Inffast.Proofs.tailW { copied with from_ }) h =
        .ok (result, after) := by
    change Zlib.Inffast.copyOp before h =
      .ok (copied, heap1) at copyRun
    change Zlib.Inffast.subn copied.out copied.dist heap1 =
      .ok (.ref dest (j + m - l.dist.toNat), heap1) at subRun
    change (Zlib.Inffast.copyOp before >>= fun copied =>
      Zlib.Inffast.subn copied.out copied.dist >>= fun from_ =>
      Zlib.Inffast.Proofs.tailW { copied with from_ }) h = _
    simp only [bind_app, copyRun, subRun]
    exact tailRun
  exact ⟨result, after, run, resultPacket, resultEq,
    bytes, tailWritable⟩

end Zlib.Inflate.Proofs
