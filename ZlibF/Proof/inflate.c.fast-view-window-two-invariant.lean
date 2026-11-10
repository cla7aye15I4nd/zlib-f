import ZlibF.Proof.«inflate.c.fast-view-copyop-invariant»
import ZlibF.Proof.«inflate.c.fast-view-window-two»

namespace Zlib.Inflate.Proofs
open C Zlib.Inflate Zlib.Inflate.Spec ZlibF.Spec.Public
set_option autoImplicit false

/-- A wrapped match that copies a window tail and then the window start
retains the default state, exact bytes, and caller output frame. -/
theorem FastInputPacket.window_then_window_default_state
    {h : Heap} {slow : IL} {bs : List UInt8}
    {l : Zlib.Inffast.L} {c : Zlib.Inffast.Ctx} {m n : Nat}
    {r : ZStreamRef} {zs : Nat} {z : ZStream}
    {s : InflateState}
    (packet : FastInputPacket h slow bs l)
    (invariant : DefaultStateJ h r zs z s)
    (buffers : DispatchBuffers h r slow bs)
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
      DefaultStateJ after r zs z s ∧
      DispatchBuffers after r slow bs ∧
      ByteViewSizes h after ∧
      result = { l with
        from_ := .ref window (woff + n),
        out := .ref dest (j + m + n),
        op := 0,
        len := UInt32.ofNat (n % 3) } ∧
      Space.get after dest = some
        (Zlib.Inffast.Proofs.blitN saved n woff (j + m)
          (Zlib.Inffast.Proofs.blitN saved m fo j output)) ∧
      Space.ro after dest = false ∧
      after = Space.put h dest
        (Zlib.Inffast.Proofs.blitN saved n woff (j + m)
          (Zlib.Inffast.Proofs.blitN saved m fo j output)) ∧
      BufferFrame h after (fun _ => False)
        [⟨slow.put, slow.left.toNat⟩] := by
  let before : Zlib.Inffast.L := { l with len := l.len - l.op }
  have packetBefore : FastInputPacket h slow bs before :=
    ⟨packet.source, packet.cursor, packet.hold, packet.bits⟩
  obtain ⟨copied, heap1, copyRun, packet1, invariant1,
      buffers1, sizes1, copyEq, copyBytes, copyWritable,
      copyHeap, _⟩ :=
    packetBefore.copyOp_distinct_default_state invariant buffers
      left different fromPtr windowGet
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
  have copiedLen : copied.len = l.len - l.op := by
    rw [copyEq]
  have copiedOut : copied.out = .ref dest (j + m) := by
    rw [copyEq]
    simp [before, opCount]
  let intermediate := Zlib.Inffast.Proofs.blitN saved m fo j output
  have intermediateGet : Space.get heap1 dest = some intermediate := by
    simpa [intermediate, before, opCount] using copyBytes
  have intermediateSize : intermediate.size = output.size :=
    Zlib.Inffast.Proofs.blitN_size saved m fo j output
  have windowNext : Space.get heap1 window = some saved := by
    rw [copyHeap, byte_view_get_put_ne h different]
    exact windowGet
  let tailStart : Zlib.Inffast.L := { copied with from_ := c.window }
  have packetTail : FastInputPacket heap1 slow bs tailStart :=
    ⟨packet1.source, packet1.cursor, packet1.hold, packet1.bits⟩
  obtain ⟨result, after, tailRun, resultPacket,
      resultInvariant, resultBuffers, sizes2, tailEq,
      tailBytes, tailWritable, tailHeap, _⟩ :=
    packetTail.tailW_default_state invariant1 buffers1
      copyCount left (by simp [tailStart, windowPtr])
      windowNext windowStartRoom
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
  have tailHeapEq : after = Space.put heap1 dest
      (Zlib.Inffast.Proofs.blitN saved n woff (j + m)
        intermediate) := by
    simpa [different, tailStart, windowPtr] using tailHeap
  have beforeOp : before.op.toNat = m := by
    simpa [before] using opCount
  rw [beforeOp] at copyHeap
  have finalHeap : after = Space.put h dest
      (Zlib.Inffast.Proofs.blitN saved n woff (j + m)
        intermediate) := by
    rw [tailHeapEq, copyHeap]
    exact byte_view_put_put outputGet outputWrite intermediate _
  have finalSize :
      (Zlib.Inffast.Proofs.blitN saved n woff (j + m)
        intermediate).size = output.size := by
    rw [Zlib.Inffast.Proofs.blitN_size, intermediateSize]
  have finalOutside : ∀ index,
      index < oo ∨ oo + slow.left.toNat ≤ index →
        (Zlib.Inffast.Proofs.blitN saved n woff (j + m)
          intermediate)[index]? = output[index]? := by
    intro index outside
    calc
      _ = intermediate[index]? :=
        Zlib.Inffast.Proofs.blitN_frame saved n woff (j + m)
          intermediate index (by omega)
      _ = output[index]? :=
        Zlib.Inffast.Proofs.blitN_frame saved m fo j output index
          (by omega)
  have frame : BufferFrame h after (fun _ => False)
      [⟨slow.put, slow.left.toNat⟩] := by
    rw [finalHeap]
    exact output_view_buffer_frame outputPtr outputGet outputWrite
      finalSize finalOutside
  exact ⟨result, after, copied, heap1, run, copyRun,
    copiedLen, resultPacket, resultInvariant, resultBuffers,
    sizes1.trans sizes2, resultEq,
    by simpa [intermediate] using bytes, tailWritable,
    by simpa [intermediate] using finalHeap, frame⟩

end Zlib.Inflate.Proofs
